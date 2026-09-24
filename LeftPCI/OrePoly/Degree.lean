module

public import LeftPCI.OrePoly.Basic

@[expose] public section

namespace LeftPCI

open Finset

/-! # Degree theory for the Ore extension `k[t; σ, δ]`

`LeftPCI/OrePoly/Basic.lean` builds `OrePoly δ = k[t; σ, δ]` as `ℕ →₀ k`, with a
multiplication defined through the operator `Xop δ = twistShift σ + coeffDeriv δ` ("left
multiplication by `t`") so that associativity comes for free — but it supplies no degree function
at all.  Mathlib's degree theory for `SkewPolynomial` (`δ = 0`) does not apply.  This file
supplies the missing one, for **fully general `δ`**.

It is stated for an arbitrary ring `k` and an arbitrary ring endomorphism `σ` (the last section
adds `NoZeroDivisors k` and injectivity of `σ`, both automatic over a division ring).

## Why a derivation costs nothing

Everything rests on one computation, `coeff_X_mul_succ`:

  `coeff (t · f) (m+1) = σ (coeff f m) + δ (coeff f (m+1))`,

i.e. the twisted shift raises the index by one while `δ` keeps it *fixed*.  So `δ` can never create
a coefficient above the top of `f`, and by induction (`coeff_X_pow_mul_eq_zero`,
`coeff_X_pow_mul_top`)

  `deg (tⁿ f) ≤ n + deg f`   and   `coeff (tⁿ f) (n + deg f) = σⁿ (lc f)`,

with `δ` absent from the second statement.  Expanding the left factor over its monomials
(`mul_eq_sum`, `coeff_mul`) then gives the two facts everything else is a corollary of:

  `deg (f g) ≤ deg f + deg g`   (`natDegree_mul_le`)
  `coeff (f g) (deg f + deg g) = lc f · σ^(deg f) (lc g)`   (`coeff_mul_natDegree_add`).

Note the asymmetry: the leading coefficient of the *right* factor is twisted by `σ^(deg f)`, the
left one is untouched.  Over a domain with `σ` injective the right-hand side is nonzero, which
gives `natDegree_mul`, `leadingCoeff_mul` and `isDomain_of_injective`.

`natDegree 0 = 0`, exactly as for `Polynomial`; `degree` is the `WithBot ℕ` version with
`degree 0 = ⊥`.  `OrePoly δ` is a plain `def` for `ℕ →₀ k`, so dot notation such as `f.natDegree`
does not resolve and everything is written in prefix form with `δ` explicit, matching
`OrePoly.coeff`/`OrePoly.monomial` in `OrePolynomial.lean`.
-/

namespace OrePoly

universe u

variable {k : Type u} [Ring k] {σ : k →+* k} (δ : OreDerivation k σ)

/-! ## Support, coefficients -/

/-- The set of indices where `f` has a nonzero coefficient. -/
def support (f : OrePoly δ) : Finset ℕ := (show ℕ →₀ k from f).support

theorem mem_support_iff {f : OrePoly δ} {n : ℕ} : n ∈ support δ f ↔ coeff δ f n ≠ 0 :=
  Finsupp.mem_support_iff

theorem ext_coeff {f g : OrePoly δ} (h : ∀ n, coeff δ f n = coeff δ g n) : f = g :=
  Finsupp.ext (f := (show ℕ →₀ k from f)) (g := (show ℕ →₀ k from g)) h

@[simp] theorem coeff_zero (n : ℕ) : coeff δ (0 : OrePoly δ) n = 0 := rfl

@[simp] theorem coeff_add (f g : OrePoly δ) (n : ℕ) :
    coeff δ (f + g) n = coeff δ f n + coeff δ g n :=
  Finsupp.add_apply (show ℕ →₀ k from f) (show ℕ →₀ k from g) n

@[simp] theorem coeff_neg (f : OrePoly δ) (n : ℕ) : coeff δ (-f) n = -coeff δ f n :=
  Finsupp.neg_apply (g := (show ℕ →₀ k from f)) (a := n)

@[simp] theorem coeff_sub (f g : OrePoly δ) (n : ℕ) :
    coeff δ (f - g) n = coeff δ f n - coeff δ g n :=
  Finsupp.sub_apply (g₁ := (show ℕ →₀ k from f)) (g₂ := (show ℕ →₀ k from g)) (a := n)

theorem eq_zero_of_forall_coeff_eq_zero {f : OrePoly δ} (h : ∀ n, coeff δ f n = 0) : f = 0 :=
  ext_coeff δ fun n => by rw [h n, coeff_zero]

theorem exists_coeff_ne_zero {f : OrePoly δ} (hf : f ≠ 0) : ∃ n, coeff δ f n ≠ 0 := by
  by_contra hcon
  exact hf (eq_zero_of_forall_coeff_eq_zero δ fun n => not_not.mp (not_exists.mp hcon n))

/-! ## `natDegree`, `degree`, `leadingCoeff` -/

/-- The `t`-degree of `f`, with the usual junk value `natDegree 0 = 0`. -/
def natDegree (f : OrePoly δ) : ℕ := (support δ f).sup id

/-- The `t`-degree of `f` in `WithBot ℕ`, so that `degree 0 = ⊥`. -/
def degree (f : OrePoly δ) : WithBot ℕ := (support δ f).max

/-- The coefficient of `f` in its top degree. -/
def leadingCoeff (f : OrePoly δ) : k := coeff δ f (natDegree δ f)

theorem coeff_natDegree (f : OrePoly δ) : coeff δ f (natDegree δ f) = leadingCoeff δ f :=
  rfl

@[simp] theorem support_zero : support δ (0 : OrePoly δ) = ∅ := rfl

@[simp] theorem natDegree_zero : natDegree δ (0 : OrePoly δ) = 0 := rfl

@[simp] theorem degree_zero : degree δ (0 : OrePoly δ) = ⊥ := rfl

@[simp] theorem leadingCoeff_zero : leadingCoeff δ (0 : OrePoly δ) = 0 := rfl

theorem le_natDegree_of_ne_zero {f : OrePoly δ} {n : ℕ} (h : coeff δ f n ≠ 0) :
    n ≤ natDegree δ f :=
  Finset.le_sup (f := id) (mem_support_iff δ |>.mpr h)

theorem coeff_eq_zero_of_natDegree_lt {f : OrePoly δ} {n : ℕ} (h : natDegree δ f < n) :
    coeff δ f n = 0 := by
  by_contra hc
  exact absurd (le_natDegree_of_ne_zero δ hc) (by omega)

theorem natDegree_mem_support {f : OrePoly δ} (hf : f ≠ 0) : natDegree δ f ∈ support δ f := by
  obtain ⟨n, hn⟩ := exists_coeff_ne_zero δ hf
  have hne : (support δ f).Nonempty := ⟨n, (mem_support_iff δ).mpr hn⟩
  have hmax : (support δ f).sup id = (support δ f).max' hne := by
    rw [Finset.max'_eq_sup', Finset.sup'_eq_sup]
  change (support δ f).sup id ∈ support δ f
  rw [hmax]
  exact (support δ f).max'_mem hne

theorem leadingCoeff_ne_zero {f : OrePoly δ} (hf : f ≠ 0) : leadingCoeff δ f ≠ 0 :=
  (mem_support_iff δ).mp (natDegree_mem_support δ hf)

theorem ne_zero_of_leadingCoeff_ne_zero {f : OrePoly δ} (h : leadingCoeff δ f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h (leadingCoeff_zero δ)

theorem leadingCoeff_eq_zero_iff {f : OrePoly δ} : leadingCoeff δ f = 0 ↔ f = 0 :=
  ⟨fun h => by_contra fun hf => leadingCoeff_ne_zero δ hf h, fun h => by rw [h, leadingCoeff_zero]⟩

theorem natDegree_le_iff {f : OrePoly δ} {n : ℕ} :
    natDegree δ f ≤ n ↔ ∀ m, n < m → coeff δ f m = 0 := by
  constructor
  · intro h m hm; exact coeff_eq_zero_of_natDegree_lt δ (by omega)
  · intro h
    by_contra hc
    rcases eq_or_ne f 0 with rfl | hf
    · exact hc (by simp)
    · exact (mem_support_iff δ).mp (natDegree_mem_support δ hf) (h _ (by omega))

theorem degree_eq_natDegree {f : OrePoly δ} (hf : f ≠ 0) :
    degree δ f = (natDegree δ f : WithBot ℕ) := by
  have hne : (support δ f).Nonempty := ⟨natDegree δ f, natDegree_mem_support δ hf⟩
  rw [degree, natDegree, Finset.max_eq_sup_withBot, Finset.coe_sup_of_nonempty hne]
  rfl

theorem degree_eq_bot_iff {f : OrePoly δ} : degree δ f = ⊥ ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    rw [degree_eq_natDegree δ hf] at h
    exact absurd h (by simp)
  · rintro rfl; rfl

/-! ## Degrees of monomials, constants and `t` -/

theorem natDegree_monomial_le (n : ℕ) (a : k) : natDegree δ (monomial δ n a) ≤ n := by
  rw [natDegree_le_iff]
  intro m hm
  rw [coeff_monomial, ite_eq_right (by omega)]

theorem natDegree_monomial {n : ℕ} {a : k} (ha : a ≠ 0) : natDegree δ (monomial δ n a) = n := by
  refine le_antisymm (natDegree_monomial_le δ n a) (le_natDegree_of_ne_zero δ (n := n) ?_)
  rw [coeff_monomial, ite_eq_left rfl]
  exact ha

theorem monomial_ne_zero {n : ℕ} {a : k} (ha : a ≠ 0) : monomial δ n a ≠ 0 := by
  intro h
  refine ha ?_
  have hc := coeff_monomial δ n n a
  rw [h, coeff_zero, ite_eq_left rfl] at hc
  exact hc.symm

theorem C_ne_zero {a : k} (ha : a ≠ 0) : C δ a ≠ 0 := by
  rw [C_apply]
  exact monomial_ne_zero δ ha

theorem leadingCoeff_monomial {n : ℕ} {a : k} (ha : a ≠ 0) :
    leadingCoeff δ (monomial δ n a) = a := by
  rw [leadingCoeff, natDegree_monomial δ ha, coeff_monomial, ite_eq_left rfl]

@[simp] theorem coeff_C_zero (a : k) : coeff δ (C δ a) 0 = a := by
  rw [C_apply, coeff_monomial, ite_eq_left rfl]

theorem coeff_C_of_ne_zero (a : k) {m : ℕ} (hm : m ≠ 0) : coeff δ (C δ a) m = 0 := by
  rw [C_apply, coeff_monomial, ite_eq_right fun h => hm h.symm]

@[simp] theorem natDegree_C (a : k) : natDegree δ (C δ a) = 0 :=
  Nat.le_zero.mp (natDegree_monomial_le δ 0 a)

@[simp] theorem natDegree_one : natDegree δ (1 : OrePoly δ) = 0 := by
  rw [one_def]
  exact Nat.le_zero.mp (natDegree_monomial_le δ 0 1)

@[simp] theorem natDegree_X [Nontrivial k] : natDegree δ (X δ) = 1 :=
  natDegree_monomial δ one_ne_zero

@[simp] theorem natDegree_X_pow [Nontrivial k] (n : ℕ) : natDegree δ (X δ ^ n) = n := by
  rw [X_pow]
  exact natDegree_monomial δ one_ne_zero

theorem X_pow_ne_zero [Nontrivial k] (n : ℕ) : (X δ ^ n) ≠ 0 := by
  rw [X_pow]
  exact monomial_ne_zero δ one_ne_zero

/-- **`t ≠ 0` in `k[t; σ, δ]`**, for any nontrivial `k`: `t = monomial 1 1`. -/
theorem X_ne_zero [Nontrivial k] : (X δ) ≠ 0 := by
  simpa using X_pow_ne_zero δ 1

theorem eq_C_of_natDegree_eq_zero {f : OrePoly δ} (h : natDegree δ f = 0) :
    f = C δ (coeff δ f 0) := by
  refine ext_coeff δ fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [C_apply, coeff_monomial, ite_eq_left rfl]
  · rw [coeff_eq_zero_of_natDegree_lt δ (by omega), C_apply, coeff_monomial, ite_eq_right (by omega)]

/-! ## Sums -/

theorem support_neg (f : OrePoly δ) : support δ (-f) = support δ f :=
  Finsupp.support_neg (show ℕ →₀ k from f)

@[simp] theorem natDegree_neg (f : OrePoly δ) : natDegree δ (-f) = natDegree δ f := by
  rw [natDegree, natDegree, support_neg]

theorem natDegree_add_le (f g : OrePoly δ) :
    natDegree δ (f + g) ≤ max (natDegree δ f) (natDegree δ g) := by
  rw [natDegree_le_iff]
  intro m hm
  rw [coeff_add, coeff_eq_zero_of_natDegree_lt δ ((le_max_left _ _).trans_lt hm),
    coeff_eq_zero_of_natDegree_lt δ ((le_max_right _ _).trans_lt hm), add_zero]

theorem natDegree_sub_le (f g : OrePoly δ) :
    natDegree δ (f - g) ≤ max (natDegree δ f) (natDegree δ g) := by
  rw [sub_eq_add_neg]
  simpa using natDegree_add_le δ f (-g)

theorem coeff_sum {ι : Type*} (s : Finset ι) (F : ι → OrePoly δ) (m : ℕ) :
    coeff δ (∑ i ∈ s, F i) m = ∑ i ∈ s, coeff δ (F i) m := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, coeff_add, ih]

/-- Every `f` is the sum of its monomials. -/
theorem eq_sum_monomial (f : OrePoly δ) :
    f = ∑ n ∈ support δ f, monomial δ n (coeff δ f n) := by
  classical
  refine ext_coeff δ fun m => ?_
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' (support δ f) m fun n => coeff δ f n]
  split_ifs with h
  · rfl
  · exact not_not.mp ((mem_support_iff δ).not.mp h)

/-! ## Left multiplication by `t` -/

theorem twistShift_apply_succ (p : ℕ →₀ k) (m : ℕ) : twistShift σ p (m + 1) = σ (p m) := by
  change Finsupp.mapDomain Nat.succ (Finsupp.mapRange σ σ.map_zero p) (Nat.succ m) = σ (p m)
  rw [Finsupp.mapDomain_apply_of_injective Nat.succ_injective, Finsupp.mapRange_apply]

theorem twistShift_apply_zero (p : ℕ →₀ k) : twistShift σ p 0 = 0 := by
  change Finsupp.mapDomain Nat.succ (Finsupp.mapRange σ σ.map_zero p) 0 = 0
  refine Finsupp.mapDomain_of_notMem_range _ _ ?_
  rintro ⟨n, hn⟩
  exact Nat.succ_ne_zero n hn

theorem coeffDeriv_apply (p : ℕ →₀ k) (m : ℕ) : coeffDeriv δ p m = δ (p m) :=
  Finsupp.mapRange_apply (hf := δ.toAddMonoidHom.map_zero)

/-- Left multiplication by `t` is the operator `Xop` of `LeftPCI/OrePoly/Basic.lean`. -/
theorem X_mul_eq (f : OrePoly δ) : X δ * f = Xop δ f := by
  change act δ (Finsupp.single 1 (1 : k)) f = Xop δ f
  rw [act_single, pow_one, lmul_one, one_mul]

theorem Xop_apply_succ (p : ℕ →₀ k) (m : ℕ) :
    Xop δ p (m + 1) = σ (p m) + δ (p (m + 1)) := by
  change (twistShift σ p + coeffDeriv δ p) (m + 1) = _
  rw [Finsupp.add_apply, twistShift_apply_succ, coeffDeriv_apply]

theorem Xop_apply_zero (p : ℕ →₀ k) : Xop δ p 0 = δ (p 0) := by
  change (twistShift σ p + coeffDeriv δ p) 0 = _
  rw [Finsupp.add_apply, twistShift_apply_zero, coeffDeriv_apply, zero_add]

/-- **The coefficients of `t * f`**: `t · (Σ aₘ tᵐ) = Σ (σ aₘ) tᵐ⁺¹ + Σ (δ aₘ) tᵐ`.  The
derivation only ever feeds the *same* index, never a higher one — this is the reason the whole
degree theory below is insensitive to `δ`. -/
theorem coeff_X_mul_succ (f : OrePoly δ) (m : ℕ) :
    coeff δ (X δ * f) (m + 1) = σ (coeff δ f m) + δ (coeff δ f (m + 1)) := by
  rw [X_mul_eq]
  exact Xop_apply_succ δ f m

theorem coeff_X_mul_zero (f : OrePoly δ) : coeff δ (X δ * f) 0 = δ (coeff δ f 0) := by
  rw [X_mul_eq]
  exact Xop_apply_zero δ f

/-! ## Left multiplication by `tⁿ` and by constants -/

theorem lmul_apply_apply (a : k) (p : ℕ →₀ k) (m : ℕ) : lmul a p m = a * p m := by
  rw [lmul_apply, Finsupp.smul_apply, smul_eq_mul]

@[simp] theorem coeff_C_mul (a : k) (f : OrePoly δ) (m : ℕ) :
    coeff δ (C δ a * f) m = a * coeff δ f m := by
  change act δ (Finsupp.single 0 a) f m = _
  rw [act_single, pow_zero, mul_one]
  exact lmul_apply_apply a f m

/-- **`tⁿ` raises degrees by at most `n`.**  If `f` has all coefficients above `d` vanishing, then
so does `tⁿ f` above `n + d`; the `δ`-part of the multiplication contributes only to indices that
are already present. -/
theorem coeff_X_pow_mul_eq_zero {f : OrePoly δ} {d : ℕ} (hf : ∀ m, d < m → coeff δ f m = 0) :
    ∀ (n m : ℕ), n + d < m → coeff δ (X δ ^ n * f) m = 0 := by
  intro n
  induction n with
  | zero => intro m hm; rw [pow_zero, one_mul]; exact hf m (by omega)
  | succ n ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [pow_succ', mul_assoc, coeff_X_mul_succ, ih m' (by omega), ih (m' + 1) (by omega),
        map_zero, OreDerivation.map_zero, add_zero]

/-- **The top coefficient of `tⁿ f`**: the commutation rule `tⁿ a = σⁿ(a) tⁿ + (lower order)`,
stated on coefficients.  Only `σ` appears — every term `δ` contributes lands in a strictly
lower degree. -/
theorem coeff_X_pow_mul_top {f : OrePoly δ} {d : ℕ} (hf : ∀ m, d < m → coeff δ f m = 0) :
    ∀ n, coeff δ (X δ ^ n * f) (n + d) = (⇑σ)^[n] (coeff δ f d) := by
  intro n
  induction n with
  | zero => rw [pow_zero, one_mul, Nat.zero_add, Function.iterate_zero_apply]
  | succ n ih =>
      rw [show n + 1 + d = (n + d) + 1 from by omega, pow_succ', mul_assoc, coeff_X_mul_succ, ih,
        coeff_X_pow_mul_eq_zero δ hf n (n + d + 1) (by omega), OreDerivation.map_zero, add_zero,
        Function.iterate_succ_apply']

theorem natDegree_X_pow_mul_le (n : ℕ) (f : OrePoly δ) :
    natDegree δ (X δ ^ n * f) ≤ n + natDegree δ f :=
  (natDegree_le_iff δ).mpr fun m hm =>
    coeff_X_pow_mul_eq_zero δ (fun _ h => coeff_eq_zero_of_natDegree_lt δ h) n m hm

theorem coeff_X_pow_mul_natDegree (n : ℕ) (f : OrePoly δ) :
    coeff δ (X δ ^ n * f) (n + natDegree δ f) = (⇑σ)^[n] (leadingCoeff δ f) :=
  coeff_X_pow_mul_top δ (fun _ h => coeff_eq_zero_of_natDegree_lt δ h) n

/-- **The commutation rule in polynomial form**: `tⁿ c = σⁿ(c) tⁿ + r` with `r` of degree `< n`.

This is the form Ore-condition and simplicity arguments use.  (For `n = 0` the bound on `r` reads
`∀ m, 0 ≤ m → coeff r m = 0`, i.e. `r = 0`, which is correct.) -/
theorem X_pow_mul_C (n : ℕ) (c : k) :
    ∃ r : OrePoly δ, X δ ^ n * C δ c = C δ ((⇑σ)^[n] c) * X δ ^ n + r ∧
      ∀ m, n ≤ m → coeff δ r m = 0 := by
  have hC : ∀ m', 0 < m' → coeff δ (C δ c) m' = 0 := fun m' hm' =>
    coeff_C_of_ne_zero δ c (by omega)
  refine ⟨X δ ^ n * C δ c - C δ ((⇑σ)^[n] c) * X δ ^ n, by abel, fun m hm => ?_⟩
  rw [coeff_sub, ← monomial_eq, coeff_monomial]
  by_cases h : n = m
  · subst h
    have htop := coeff_X_pow_mul_top δ (d := 0) hC n
    rw [Nat.add_zero, coeff_C_zero] at htop
    rw [htop, ite_eq_left rfl, sub_self]
  · rw [ite_eq_right h, sub_zero]
    exact coeff_X_pow_mul_eq_zero δ hC n m (by omega)

/-! ## The degree of a product -/

/-- `f * g` expanded over the monomials of the left factor. -/
theorem mul_eq_sum (f g : OrePoly δ) :
    f * g = ∑ n ∈ support δ f, C δ (coeff δ f n) * (X δ ^ n * g) := by
  conv_lhs => rw [eq_sum_monomial δ f]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun n _ => by rw [monomial_eq, mul_assoc]

/-- **The coefficients of a product.** -/
theorem coeff_mul (f g : OrePoly δ) (m : ℕ) :
    coeff δ (f * g) m = ∑ n ∈ support δ f, coeff δ f n * coeff δ (X δ ^ n * g) m := by
  rw [mul_eq_sum, coeff_sum]
  exact Finset.sum_congr rfl fun n _ => coeff_C_mul δ _ _ _

theorem coeff_mul_eq_zero {f g : OrePoly δ} {d e : ℕ}
    (hf : ∀ m, d < m → coeff δ f m = 0) (hg : ∀ m, e < m → coeff δ g m = 0)
    {m : ℕ} (hm : d + e < m) : coeff δ (f * g) m = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun n hn => ?_
  have hnd : n ≤ d := by
    by_contra hc
    exact (mem_support_iff δ).mp hn (hf n (by omega))
  rw [coeff_X_pow_mul_eq_zero δ hg n m (by omega), mul_zero]

theorem natDegree_mul_le (f g : OrePoly δ) :
    natDegree δ (f * g) ≤ natDegree δ f + natDegree δ g :=
  (natDegree_le_iff δ).mpr fun _ hm =>
    coeff_mul_eq_zero δ (fun _ h => coeff_eq_zero_of_natDegree_lt δ h)
      (fun _ h => coeff_eq_zero_of_natDegree_lt δ h) hm

/-- **The coefficient of a product in the sum of the two degrees.**  Note the twist: the leading
coefficient of the *right* factor is hit by `σ^(deg f)`, the leading coefficient of the left factor
is untouched, and `δ` does not appear at all. -/
theorem coeff_mul_natDegree_add (f g : OrePoly δ) :
    coeff δ (f * g) (natDegree δ f + natDegree δ g)
      = leadingCoeff δ f * (⇑σ)^[natDegree δ f] (leadingCoeff δ g) := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [zero_mul, coeff_zero, leadingCoeff_zero, zero_mul]
  rw [coeff_mul, Finset.sum_eq_single (natDegree δ f)]
  · rw [coeff_X_pow_mul_natDegree]
    rfl
  · intro n hn hne
    have hnd : n ≤ natDegree δ f := le_natDegree_of_ne_zero δ ((mem_support_iff δ).mp hn)
    rw [coeff_X_pow_mul_eq_zero δ (fun _ h => coeff_eq_zero_of_natDegree_lt δ h) n _ (by omega),
      mul_zero]
  · intro hmem
    exact absurd (natDegree_mem_support δ hf) hmem

/-- Subtracting a polynomial with the same degree and the same leading coefficient drops the
degree.  This is the step of the left division algorithm, isolated. -/
theorem natDegree_sub_lt_of_leadingCoeff_eq {f g : OrePoly δ}
    (hdeg : natDegree δ g = natDegree δ f) (hlc : leadingCoeff δ g = leadingCoeff δ f)
    (hne : f - g ≠ 0) : natDegree δ (f - g) < natDegree δ f := by
  have hg : coeff δ g (natDegree δ f) = leadingCoeff δ f := by rw [← hdeg]; exact hlc
  have hle : natDegree δ (f - g) ≤ natDegree δ f := by
    rw [natDegree_le_iff]
    intro m hm
    rw [coeff_sub, coeff_eq_zero_of_natDegree_lt δ hm,
      coeff_eq_zero_of_natDegree_lt δ (by omega : natDegree δ g < m), sub_zero]
  rcases Nat.lt_or_ge (natDegree δ (f - g)) (natDegree δ f) with h | h
  · exact h
  · refine absurd ?_ (leadingCoeff_ne_zero δ hne)
    rw [← coeff_natDegree, le_antisymm hle h, coeff_sub, hg, coeff_natDegree, sub_self]

/-- Iterates of an injective `σ` do not kill nonzero elements: the side condition of every
leading-coefficient computation.  (`σ` is automatically injective over a division ring.) -/
theorem iterate_ne_zero (hσ : Function.Injective σ) (n : ℕ) {a : k} (ha : a ≠ 0) :
    (⇑σ)^[n] a ≠ 0 := fun h => ha (hσ.iterate n (by simpa using h))

/-! ## `k[t; σ, δ]` is a domain -/

section NoZeroDivisors

variable [NoZeroDivisors k]

/-- **The degree of a product is the sum of the degrees.**  `σ` injective is automatic when `k` is
a division ring (`RingHom.injective`). -/
theorem natDegree_mul (hσ : Function.Injective σ) {f g : OrePoly δ} (hf : f ≠ 0) (hg : g ≠ 0) :
    natDegree δ (f * g) = natDegree δ f + natDegree δ g := by
  refine le_antisymm (natDegree_mul_le δ f g) (le_natDegree_of_ne_zero δ ?_)
  rw [coeff_mul_natDegree_add]
  refine mul_ne_zero (leadingCoeff_ne_zero δ hf) fun h => ?_
  exact leadingCoeff_ne_zero δ hg (hσ.iterate (natDegree δ f) (by simpa using h))

/-- **The leading coefficient of a product**: `lc (f g) = lc f · σ^(deg f)(lc g)`. -/
theorem leadingCoeff_mul (hσ : Function.Injective σ) {f g : OrePoly δ} (hf : f ≠ 0) (hg : g ≠ 0) :
    leadingCoeff δ (f * g) = leadingCoeff δ f * (⇑σ)^[natDegree δ f] (leadingCoeff δ g) := by
  rw [← coeff_natDegree, natDegree_mul δ hσ hf hg, coeff_mul_natDegree_add]

theorem mul_ne_zero_of_injective (hσ : Function.Injective σ) {f g : OrePoly δ} (hf : f ≠ 0)
    (hg : g ≠ 0) : f * g ≠ 0 := by
  intro h
  have hc := coeff_mul_natDegree_add δ f g
  rw [h, coeff_zero] at hc
  rcases mul_eq_zero.mp hc.symm with h1 | h1
  · exact leadingCoeff_ne_zero δ hf h1
  · exact leadingCoeff_ne_zero δ hg (hσ.iterate _ (by simpa using h1))

theorem noZeroDivisors_of_injective (hσ : Function.Injective σ) : NoZeroDivisors (OrePoly δ) where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} hfg := by
    by_contra hcon
    exact mul_ne_zero_of_injective δ hσ (fun h => hcon (Or.inl h)) (fun h => hcon (Or.inr h)) hfg

/-- **`k[t; σ, δ]` is a domain** whenever `k` is and `σ` is injective. -/
theorem isDomain_of_injective [Nontrivial k] (hσ : Function.Injective σ) : IsDomain (OrePoly δ) :=
  letI := noZeroDivisors_of_injective δ hσ
  NoZeroDivisors.to_isDomain _

theorem natDegree_monomial_mul (hσ : Function.Injective σ) (n : ℕ) {a : k} (ha : a ≠ 0)
    {g : OrePoly δ} (hg : g ≠ 0) :
    natDegree δ (monomial δ n a * g) = n + natDegree δ g := by
  rw [natDegree_mul δ hσ (monomial_ne_zero δ ha) hg, natDegree_monomial δ ha]

theorem leadingCoeff_monomial_mul (hσ : Function.Injective σ) (n : ℕ) {a : k} (ha : a ≠ 0)
    {g : OrePoly δ} (hg : g ≠ 0) :
    leadingCoeff δ (monomial δ n a * g) = a * (⇑σ)^[n] (leadingCoeff δ g) := by
  rw [leadingCoeff_mul δ hσ (monomial_ne_zero δ ha) hg, natDegree_monomial δ ha,
    leadingCoeff_monomial δ ha]

/-- A unit of `k[t; σ, δ]` has degree `0`. -/
theorem natDegree_eq_zero_of_isUnit [Nontrivial k] (hσ : Function.Injective σ) {f : OrePoly δ}
    (hf : IsUnit f) : natDegree δ f = 0 := by
  have : NoZeroDivisors (OrePoly δ) := noZeroDivisors_of_injective δ hσ
  have : IsDomain (OrePoly δ) := isDomain_of_injective δ hσ
  obtain ⟨u, rfl⟩ := hf
  have h := natDegree_mul δ hσ (u.ne_zero) (u⁻¹.ne_zero)
  rw [u.mul_inv, natDegree_one] at h
  omega

/-- **`t` is not a unit of `k[t; σ, δ]`** when `σ` is injective: units have degree `0`
(`natDegree_eq_zero_of_isUnit`) while `t` has degree `1`. -/
theorem not_isUnit_X [Nontrivial k] (hσ : Function.Injective σ) : ¬ IsUnit (X δ) := by
  intro hu
  have h := natDegree_eq_zero_of_isUnit δ hσ hu
  rw [natDegree_X] at h
  exact one_ne_zero h

end NoZeroDivisors

end OrePoly

end LeftPCI
