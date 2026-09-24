module

public import LeftPCI.FreeAlgebra.Words
public import LeftPCI.FreeAlgebra.WeakAlgorithm
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

/-!
# Free associative algebras over a field are free ideal rings

This file proves **Cohn's theorem** that the free associative algebra `K⟨σ⟩` over a field `K` is
a *fir*: every one-sided ideal is a free module, of unique rank (P. M. Cohn, *Free Ideal Rings
and Localization in General Rings*, CUP 2006, Theorem 2.5.3 together with
Theorem 2.4.6).  The route is Cohn's own: the **weak algorithm**, developed for a general
filtered ring in `LeftPCI/FreeAlgebra/WeakAlgorithm.lean`, is verified here for the free algebra.

Everything is mirrored to the **left** (see the side-convention section of
`LeftPCI/FreeAlgebra/WeakAlgorithm.lean`): `Filtration.free_of_hasWeakAlgorithm` makes *left* ideals
free, which is what Mathlib's `Ideal R` and `Module.Free R I` mean.  Cohn's §2.5 proof is the
one that establishes the *left*-hand weak algorithm using *right* transductions, so it
transcribes directly.

## Contents

* `LeftPCI.Deglex` — the **degree-lexicographic order** on `FreeMonoid σ` for a finite
  alphabet, obtained by encoding a word as a base-`(card σ + 1)` numeral with digits in
  `[1, card σ]` (`Deglex.val`) and pulling `≤` back from `ℕ` along that encoding.  Linearity,
  well-foundedness and finiteness of every initial segment are then inherited from `ℕ` for free;
  what has to be proved is two-sided strict monotonicity of multiplication
  (`Deglex.mul_lt_mul_left'`, `Deglex.mul_lt_mul_right'`, `Deglex.mul_le_mul'`).
* `FA.lw` / `FA.lc` — the **leading word** and leading coefficient of an element of
  `FA K σ = MonoidAlgebra K (FreeMonoid σ)` (see `LeftPCI/FreeAlgebra/Words.lean`), with
  `FA.coeff_mul_lw` and `FA.lw_mul : lw (f * g) = lw f * lw g`.
* `FA.degFn` and `FA.filtration` — Cohn's **natural filtration**: the degree of an element is the
  greatest length of a word occurring in it.
* `FA.rtrans` — the **right transduction** at a word `w` (Cohn *FIR* §2.5): strip the prefix
  `w`.  Its two properties are `FA.degFn_rtrans_add_le` (`v (a*) + v w ≤ v a`) and
  `FA.degFn_rtrans_mul_sub_lt` (Cohn's congruence `(a b)* ≡ a* b mod R⁽ᵛᵇ⁻¹⁾`).
* `FA.hasWeakAlgorithm_filtration` — **the free algebra satisfies the weak algorithm**
  (Cohn *FIR* Theorem 2.5.1 (c) ⇒ (a) / Corollary 2.5.2).
* `FA.free_of_ideal` and `FA.invariantBasisNumber_fa` — the fir conclusion; unique rank is
  `InvariantBasisNumber`, pulled back along the augmentation `FA.eps` to `K`
  (`invariantBasisNumber_of_ringHom`).

Note that Mathlib's `AddMonoidAlgebra.supDegree` machinery is *not* usable here: it is set up for
additive monoids of exponents, whereas the grading relevant to a free algebra is by words of a
free (non-commutative) monoid.
-/

namespace LeftPCI

/-- **Invariant basis number transfers backwards along an arbitrary ring homomorphism.**

If there is *any* ring hom `f : R →+* S` with `S` having IBN, then `R` has IBN.  No surjectivity,
injectivity, or commutativity is needed: `R` has IBN iff there is no pair of matrices
`A : n × m`, `B : m × n` over `R` with `A * B = 1` and `B * A = 1` and `n ≠ m`
(`invariantBasisNumber_iff_matrix`), and such a pair maps entrywise through `f` to a pair over `S`
satisfying the same two equations. -/
theorem invariantBasisNumber_of_ringHom {R S : Type*} [Ring R] [Ring S]
    [InvariantBasisNumber S] (f : R →+* S) : InvariantBasisNumber R := by
  rw [invariantBasisNumber_iff_matrix]
  intro n m A B hAB hBA
  refine (invariantBasisNumber_iff_matrix (R := S)).mp ‹_› n m (A.map f) (B.map f) ?_ ?_
  · rw [← Matrix.map_mul, hAB, Matrix.map_one f (map_zero f) (map_one f)]
  · rw [← Matrix.map_mul, hBA, Matrix.map_one f (map_zero f) (map_one f)]

/-! ## The degree-lexicographic order on words, as a base-`b` numeral -/

namespace Deglex

variable {σ : Type*} [Fintype σ]

/-- The numeral base used to encode words: one more than the size of the alphabet, so that every
letter gets a nonzero digit. -/
def base (σ : Type*) [Fintype σ] : ℕ := Fintype.card σ + 1

theorem base_pos : 0 < base σ := Nat.succ_pos _

/-- The digit of a letter: a value in `[1, card σ]`, in particular nonzero and `< base σ`. -/
noncomputable def digit (c : σ) : ℕ := (Fintype.equivFin σ c : ℕ) + 1

theorem one_le_digit (c : σ) : 1 ≤ digit c := Nat.le_add_left 1 _

theorem digit_lt_base (c : σ) : digit c < base σ := by
  have h := (Fintype.equivFin σ c).isLt
  simp only [digit, base]
  omega

theorem digit_injective : Function.Injective (digit (σ := σ)) := by
  intro a b h
  simp only [digit, Nat.add_right_cancel_iff] at h
  exact (Fintype.equivFin σ).injective (Fin.val_injective h)

/-- The step function of the numeral evaluation. -/
noncomputable def step (σ : Type*) [Fintype σ] : ℕ → σ → ℕ := fun n c => n * base σ + digit c

/-- **The value of a word**: its letters read as the digits of a base-`base σ` numeral.
This is a strictly monotone encoding of the degree-lexicographic order (see `val_lt_of_length_lt`
and `val_injective`), and it is what makes descending induction on leading words available as
plain strong induction on `ℕ`. -/
noncomputable def val (w : FreeMonoid σ) : ℕ := (FreeMonoid.toList w).foldl (step σ) 0

private theorem foldl_eq (l : List σ) (a : ℕ) :
    l.foldl (step σ) a = a * base σ ^ l.length + l.foldl (step σ) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons c l ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (step σ a c), ih (step σ 0 c)]
      simp only [step, zero_mul, zero_add]
      ring

/-- The value of a product of words: the base-`base σ` shift-and-add rule. -/
theorem val_mul (u v : FreeMonoid σ) : val (u * v) = val u * base σ ^ v.length + val v := by
  simp only [val, FreeMonoid.toList_mul, List.foldl_append]
  exact foldl_eq _ _

@[simp] theorem val_one : val (1 : FreeMonoid σ) = 0 := rfl

@[simp] theorem val_of (c : σ) : val (FreeMonoid.of c) = digit c := by
  simp [val, step, FreeMonoid.toList_of]

theorem val_of_mul (c : σ) (w : FreeMonoid σ) :
    val (FreeMonoid.of c * w) = digit c * base σ ^ w.length + val w := by
  rw [val_mul, val_of]

/-- A word's value is smaller than `base σ ^ (its length)`. -/
theorem val_lt_pow (w : FreeMonoid σ) : val w < base σ ^ w.length := by
  induction w using FreeMonoid.recOn with
  | one => simp
  | of_mul c w ih =>
      rw [val_of_mul]
      simp only [FreeMonoid.length_mul, FreeMonoid.length_of]
      have h1 : digit c + 1 ≤ base σ := digit_lt_base c
      have h2 : 0 < base σ ^ w.length := pow_pos base_pos _
      calc digit c * base σ ^ w.length + val w
          < digit c * base σ ^ w.length + base σ ^ w.length := by omega
        _ = (digit c + 1) * base σ ^ w.length := by ring
        _ ≤ base σ * base σ ^ w.length := Nat.mul_le_mul_right _ h1
        _ = base σ ^ (1 + w.length) := by ring

/-- A nonempty word's value is at least `base σ ^ (its length - 1)`. -/
theorem pow_le_val (c : σ) (w : FreeMonoid σ) :
    base σ ^ w.length ≤ val (FreeMonoid.of c * w) := by
  rw [val_of_mul]
  have : 1 * base σ ^ w.length ≤ digit c * base σ ^ w.length :=
    Nat.mul_le_mul_right _ (one_le_digit c)
  omega

/-- **A longer word has a bigger value.** -/
theorem val_lt_of_length_lt {u v : FreeMonoid σ} (h : u.length < v.length) : val u < val v := by
  induction v using FreeMonoid.casesOn with
  | one => simp [FreeMonoid.length] at h
  | of_mul c v =>
      have hlen : u.length ≤ v.length := by
        rw [FreeMonoid.length_mul, FreeMonoid.length_of] at h; omega
      calc val u < base σ ^ u.length := val_lt_pow u
        _ ≤ base σ ^ v.length := Nat.pow_le_pow_right base_pos hlen
        _ ≤ val (FreeMonoid.of c * v) := pow_le_val c v

theorem length_le_of_val_le {u v : FreeMonoid σ} (h : val u ≤ val v) : u.length ≤ v.length := by
  by_contra hcon
  exact absurd (val_lt_of_length_lt (Nat.lt_of_not_le hcon)) (by omega)

theorem length_eq_of_val_eq {u v : FreeMonoid σ} (h : val u = val v) : u.length = v.length :=
  Nat.le_antisymm (length_le_of_val_le h.le) (length_le_of_val_le h.ge)

private theorem digits_eq {a b x y n : ℕ} (hn : 0 < n) (hx : x < n) (hy : y < n)
    (h : a * n + x = b * n + y) : a = b ∧ x = y := by
  have h' : n * a + x = n * b + y := by rw [Nat.mul_comm n a, Nat.mul_comm n b]; exact h
  have hd := congrArg (· / n) h'
  have hm := congrArg (· % n) h'
  simp only [Nat.mul_add_div hn, Nat.mul_add_mod, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.add_zero] at hd hm
  exact ⟨hd, hm⟩

/-- **The encoding is injective**, so `val` really is a linear order on words. -/
theorem val_injective : Function.Injective (val (σ := σ)) := by
  intro u
  induction u using FreeMonoid.recOn with
  | one =>
      intro v hv
      have hlen := length_eq_of_val_eq hv
      simp only [FreeMonoid.length_one] at hlen
      exact (FreeMonoid.length_eq_zero.mp hlen.symm).symm
  | of_mul c u ih =>
      intro v hv
      have hlen := length_eq_of_val_eq hv
      induction v using FreeMonoid.casesOn with
      | one => simp [FreeMonoid.length_mul, FreeMonoid.length_of] at hlen
      | of_mul d v =>
          simp only [FreeMonoid.length_mul, FreeMonoid.length_of] at hlen
          have hlen' : u.length = v.length := by omega
          rw [val_of_mul, val_of_mul, ← hlen'] at hv
          obtain ⟨hdig, hval⟩ :=
            digits_eq (pow_pos base_pos _) (val_lt_pow u) (hlen' ▸ val_lt_pow v) hv
          rw [digit_injective hdig, ih hval]

/-- The **degree-lexicographic order** on words, transported from `ℕ` along `val`.  Scoped, so
that it never leaks out of this development. -/
noncomputable scoped instance instLinearOrder : LinearOrder (FreeMonoid σ) :=
  LinearOrder.lift' val val_injective

theorem le_iff {u v : FreeMonoid σ} : u ≤ v ↔ val u ≤ val v := Iff.rfl

theorem lt_iff {u v : FreeMonoid σ} : u < v ↔ val u < val v := Iff.rfl

theorem length_le_of_le {u v : FreeMonoid σ} (h : u ≤ v) : u.length ≤ v.length :=
  length_le_of_val_le h

/-- **Strict monotonicity of multiplication on the left.** -/
theorem mul_lt_mul_left' {u v : FreeMonoid σ} (h : u < v) (w : FreeMonoid σ) : w * u < w * v := by
  rw [lt_iff] at h ⊢
  rw [val_mul, val_mul]
  have hlen : u.length ≤ v.length := length_le_of_val_le h.le
  have : base σ ^ u.length ≤ base σ ^ v.length := Nat.pow_le_pow_right base_pos hlen
  have := Nat.mul_le_mul_left (val w) this
  omega

/-- **Strict monotonicity of multiplication on the right.** -/
theorem mul_lt_mul_right' {u v : FreeMonoid σ} (h : u < v) (w : FreeMonoid σ) : u * w < v * w := by
  rw [lt_iff] at h ⊢
  rw [val_mul, val_mul]
  have := Nat.mul_lt_mul_of_lt_of_le h (le_refl (base σ ^ w.length)) (pow_pos base_pos _)
  omega

theorem mul_le_mul_left' {u v : FreeMonoid σ} (h : u ≤ v) (w : FreeMonoid σ) : w * u ≤ w * v := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact (mul_lt_mul_left' h w).le

theorem mul_le_mul_right' {u v : FreeMonoid σ} (h : u ≤ v) (w : FreeMonoid σ) : u * w ≤ v * w := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact (mul_lt_mul_right' h w).le

theorem mul_le_mul' {u v u' v' : FreeMonoid σ} (h : u ≤ u') (h' : v ≤ v') : u * v ≤ u' * v' :=
  le_trans (mul_le_mul_left' h' u) (mul_le_mul_right' h v')

end Deglex

/-! ## Leading words and the length filtration on the free algebra -/

namespace FA

open MonoidAlgebra Finsupp

open scoped Deglex

variable {K : Type*} [Field K] {σ : Type*}

theorem support_nonempty {f : FA K σ} (hf : f ≠ 0) : f.coeff.support.Nonempty := by
  rw [Finsupp.support_nonempty_iff]
  intro hc
  exact hf (MonoidAlgebra.coeff_injective (by simpa using hc))

section Deglex

variable [Fintype σ]

/-- The **leading word** of `f`: the largest word in the support of `f` for the
degree-lexicographic order (and `1` when `f = 0`). -/
noncomputable def lw (f : FA K σ) : FreeMonoid σ :=
  if h : f.coeff.support.Nonempty then f.coeff.support.max' h else 1

theorem lw_mem_support {f : FA K σ} (hf : f ≠ 0) : lw f ∈ f.coeff.support := by
  rw [lw, dite_eq_left (support_nonempty hf)]
  exact Finset.max'_mem _ _

theorem le_lw {f : FA K σ} (hf : f ≠ 0) {u : FreeMonoid σ} (hu : u ∈ f.coeff.support) :
    u ≤ lw f := by
  rw [lw, dite_eq_left (support_nonempty hf)]
  exact Finset.le_max' _ _ hu

theorem length_le_length_lw {f : FA K σ} (hf : f ≠ 0) {u : FreeMonoid σ}
    (hu : u ∈ f.coeff.support) : FreeMonoid.length u ≤ FreeMonoid.length (lw f) :=
  Deglex.length_le_of_le (le_lw hf hu)

/-- The **leading coefficient** of `f`. -/
noncomputable def lc (f : FA K σ) : K := f.coeff (lw f)

theorem lc_ne_zero {f : FA K σ} (hf : f ≠ 0) : lc f ≠ 0 :=
  Finsupp.mem_support_iff.mp (lw_mem_support hf)

/-- **Leading coefficients multiply**: this is `coeff_mul_of_maxLen` at the two leading words,
which have maximal *length* because the degree-lexicographic order refines length. -/
theorem coeff_mul_lw {f g : FA K σ} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).coeff (lw f * lw g) = lc f * lc g :=
  coeff_mul_of_maxLen (fun _ hw => length_le_length_lw hf hw)
    (fun _ hw => length_le_length_lw hg hw)

/-- **Leading words multiply.** -/
theorem lw_mul {f g : FA K σ} (hf : f ≠ 0) (hg : g ≠ 0) : lw (f * g) = lw f * lw g := by
  classical
  have hne : (f * g).coeff (lw f * lw g) ≠ 0 := by
    rw [coeff_mul_lw hf hg]
    exact mul_ne_zero (lc_ne_zero hf) (lc_ne_zero hg)
  have hfg : f * g ≠ 0 := by
    intro h
    rw [h] at hne
    simp at hne
  refine le_antisymm ?_ (le_lw hfg (Finsupp.mem_support_iff.mpr hne))
  refine le_lw ?_ (lw_mem_support hfg) |>.trans ?_
  · exact hfg
  · obtain ⟨u, hu, w, hw, huw⟩ :=
      Finset.mem_mul.mp (MonoidAlgebra.support_coeff_mul_subset f g (lw_mem_support hfg))
    rw [← huw]
    exact Deglex.mul_le_mul' (le_lw hf hu) (le_lw hg hw)

end Deglex

/-! ### The length filtration -/

/-- The **degree** of an element of the free algebra: the largest length of a word occurring in
it (`⊥` for `0`).  This is Cohn's natural filtration on the free algebra. -/
noncomputable def degFn (f : FA K σ) : WithBot ℕ :=
  f.coeff.support.sup fun w => (FreeMonoid.length w : WithBot ℕ)

theorem degFn_le_iff {f : FA K σ} {n : WithBot ℕ} :
    degFn f ≤ n ↔ ∀ w ∈ f.coeff.support, (FreeMonoid.length w : WithBot ℕ) ≤ n := by
  simp only [degFn]
  exact ⟨fun h w hw => le_trans (Finset.le_sup
    (f := fun w : FreeMonoid σ => (FreeMonoid.length w : WithBot ℕ)) hw) h,
    fun h => Finset.sup_le h⟩

theorem le_degFn {f : FA K σ} {w : FreeMonoid σ} (hw : w ∈ f.coeff.support) :
    (FreeMonoid.length w : WithBot ℕ) ≤ degFn f := by
  simp only [degFn]
  exact Finset.le_sup (f := fun w : FreeMonoid σ => (FreeMonoid.length w : WithBot ℕ)) hw

theorem degFn_eq_bot_iff {f : FA K σ} : degFn f = ⊥ ↔ f = 0 := by
  classical
  constructor
  · intro h
    by_contra hf
    obtain ⟨u, hu⟩ := support_nonempty hf
    have hle := le_degFn hu
    rw [h, le_bot_iff] at hle
    exact absurd hle (by simp)
  · rintro rfl
    simp [degFn]

theorem degFn_eq_length_lw [Fintype σ] {f : FA K σ} (hf : f ≠ 0) :
    degFn f = (FreeMonoid.length (lw f) : WithBot ℕ) :=
  le_antisymm (degFn_le_iff.2 fun _ hw => by exact_mod_cast length_le_length_lw hf hw)
    (le_degFn (lw_mem_support hf))

theorem degFn_one : degFn (1 : FA K σ) = 0 := by
  classical
  have h1 : (1 : FA K σ).coeff.support = {1} := by
    simp [MonoidAlgebra.one_def]
  rw [degFn, h1]
  simp

theorem degFn_sub_le (f g : FA K σ) : degFn (f - g) ≤ max (degFn f) (degFn g) := by
  classical
  refine degFn_le_iff.2 fun w hw => ?_
  have : w ∈ f.coeff.support ∪ g.coeff.support := by
    refine Finset.mem_union.2 ?_
    by_contra hcon
    rw [not_or] at hcon
    simp only [Finsupp.mem_support_iff, not_not] at hcon
    refine absurd (Finsupp.mem_support_iff.1 hw) ?_
    simp only [not_not]
    have : (f - g).coeff w = f.coeff w - g.coeff w := by simp
    rw [this, hcon.1, hcon.2, sub_zero]
  rcases Finset.mem_union.1 this with h | h
  · exact le_trans (le_degFn h) (le_max_left _ _)
  · exact le_trans (le_degFn h) (le_max_right _ _)

theorem degFn_mul_le (f g : FA K σ) : degFn (f * g) ≤ degFn f + degFn g := by
  classical
  refine degFn_le_iff.2 fun w hw => ?_
  obtain ⟨u, hu, z, hz, rfl⟩ := Finset.mem_mul.mp (MonoidAlgebra.support_coeff_mul_subset f g hw)
  rw [FreeMonoid.length_mul]
  push_cast
  exact add_le_add (le_degFn hu) (le_degFn hz)

theorem degFn_zero : degFn (0 : FA K σ) = ⊥ := degFn_eq_bot_iff.2 rfl

theorem degFn_neg (f : FA K σ) : degFn (-f) = degFn f := by
  refine le_antisymm ?_ ?_
  · have h := degFn_sub_le (0 : FA K σ) f
    rwa [zero_sub, degFn_zero, max_eq_right bot_le] at h
  · have h := degFn_sub_le (0 : FA K σ) (-f)
    rwa [zero_sub, neg_neg, degFn_zero, max_eq_right bot_le] at h

theorem degFn_add_le (f g : FA K σ) : degFn (f + g) ≤ max (degFn f) (degFn g) := by
  have h := degFn_sub_le f (-g)
  rwa [sub_neg_eq_add, degFn_neg] at h

theorem degFn_smul_le (r : K) (f : FA K σ) : degFn (r • f) ≤ degFn f := by
  refine degFn_le_iff.2 fun u hu => ?_
  refine le_degFn (Finsupp.mem_support_iff.2 fun hc => ?_)
  refine absurd (Finsupp.mem_support_iff.1 hu) ?_
  simp only [not_not]
  have : (r • f).coeff u = r * f.coeff u := by simp
  rw [this, hc, mul_zero]

/-- Cohn's **natural filtration** on the free algebra `K⟨σ⟩`: the degree of an element is the
largest length of a word occurring in it. -/
noncomputable def filtration (K : Type*) [Field K] (σ : Type*) : Filtration (FA K σ) where
  deg := degFn
  deg_eq_bot _ := degFn_eq_bot_iff
  deg_one := degFn_one
  deg_sub_le := degFn_sub_le
  deg_mul_le := degFn_mul_le

@[simp] theorem filtration_deg (f : FA K σ) : (filtration K σ).deg f = degFn f := rfl

/-! ### Right transductions

Cohn (*FIR* §2.5) attaches to a monomial `w` of the monomial basis the *right
transduction* `a ↦ a*`, the `K`-linear map sending a monomial `w * u` to `u` and every other
monomial to `0`; in the free algebra the monomial basis is the set of words, so the right
transduction at the word `w` is simply "strip the prefix `w`".  The two facts Cohn needs are
`degFn_rtrans_add_le` (`v (a*) ≤ v a - v w`) and `degFn_rtrans_mul_sub_lt`
(`(a b)* ≡ a* b mod R⁽ᵛᵇ⁻¹⁾`). -/

theorem mul_left_injective' (w : FreeMonoid σ) :
    Function.Injective fun u : FreeMonoid σ => w * u := fun _ _ h => mul_left_cancel h

/-- The **right transduction** at the word `w`: strip a leading `w`. -/
noncomputable def rtrans (w : FreeMonoid σ) : FA K σ →ₗ[K] FA K σ :=
  (MonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap ∘ₗ
    Finsupp.lcomapDomain _ (mul_left_injective' w) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv K).toLinearMap

@[simp] theorem coeff_rtrans (w : FreeMonoid σ) (f : FA K σ) (u : FreeMonoid σ) :
    (rtrans (K := K) w f).coeff u = f.coeff (w * u) := rfl

/-- Cohn's `v (a*) ≤ v a - v w`, in the form that avoids truncated subtraction. -/
theorem exists_degFn_eq {f : FA K σ} (hf : f ≠ 0) :
    ∃ u ∈ f.coeff.support, degFn f = (FreeMonoid.length u : WithBot ℕ) := by
  obtain ⟨u, hu, humax⟩ := Finset.exists_max_image f.coeff.support
    (fun w => FreeMonoid.length w) (support_nonempty hf)
  exact ⟨u, hu, le_antisymm (degFn_le_iff.2 fun z hz => by exact_mod_cast humax z hz)
    (le_degFn hu)⟩

theorem degFn_rtrans_add_le (w : FreeMonoid σ) (f : FA K σ) :
    degFn (rtrans (K := K) w f) + (FreeMonoid.length w : WithBot ℕ) ≤ degFn f := by
  rcases eq_or_ne (rtrans (K := K) w f) 0 with h | h
  · rw [h, degFn_zero]
    simp
  obtain ⟨u, hu, hdegeq⟩ := exists_degFn_eq h
  rw [hdegeq]
  have hmem : w * u ∈ f.coeff.support := by
    rwa [Finsupp.mem_support_iff, coeff_rtrans, ← Finsupp.mem_support_iff] at hu
  have hle := le_degFn hmem
  rwa [FreeMonoid.length_mul, Nat.cast_add, add_comm (FreeMonoid.length w : WithBot ℕ)] at hle

theorem rtrans_single_self_mul (w : FreeMonoid σ) (h : FA K σ) :
    rtrans w (MonoidAlgebra.single w (1 : K) * h) = h := by
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun u => ?_)
  rw [coeff_rtrans, MonoidAlgebra.coeff_single_mul_eq_mul_coeff u
    (fun _ _ => mul_right_inj _), one_mul]

theorem rtrans_single_of_not_prefix {u w : FreeMonoid σ} (hA : ¬ ∃ z, u = w * z) :
    rtrans w (MonoidAlgebra.single u (1 : K)) = 0 := by
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun t => ?_)
  rw [coeff_rtrans]
  have hne : u ≠ w * t := fun h => hA ⟨t, h⟩
  simp [MonoidAlgebra.coeff_single, hne]

theorem rtrans_single_mul_of_prefix {u w y : FreeMonoid σ} (hy : w = u * y) (g : FA K σ) :
    rtrans w (MonoidAlgebra.single u (1 : K) * g) = rtrans y g := by
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun t => ?_)
  rw [coeff_rtrans, coeff_rtrans, show w * t = u * (y * t) by rw [hy, mul_assoc]]
  rw [MonoidAlgebra.coeff_single_mul_eq_mul_coeff (y * t) (fun _ _ => mul_right_inj _), one_mul]

theorem rtrans_single_mul_of_incomparable {u w : FreeMonoid σ} (hA : ¬ ∃ z, u = w * z)
    (hB : ¬ ∃ y, w = u * y) (g : FA K σ) :
    rtrans w (MonoidAlgebra.single u (1 : K) * g) = 0 := by
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun t => ?_)
  rw [coeff_rtrans]
  refine (MonoidAlgebra.coeff_single_mul_of_forall_mul_ne 1 g fun d hd => ?_).trans rfl
  have hl : FreeMonoid.toList u ++ FreeMonoid.toList d
      = FreeMonoid.toList w ++ FreeMonoid.toList t := by
    rw [← FreeMonoid.toList_mul, ← FreeMonoid.toList_mul, hd]
  rcases List.append_eq_append_iff.1 hl with ⟨a', ha', -⟩ | ⟨c', hc', -⟩
  · exact hB ⟨FreeMonoid.ofList a', FreeMonoid.toList.injective (by simpa using ha')⟩
  · exact hA ⟨FreeMonoid.ofList c', FreeMonoid.toList.injective (by simpa using hc')⟩

theorem le_of_add_le_add_right' {a b : WithBot ℕ} {k : ℕ}
    (h : a + (k : WithBot ℕ) ≤ b + (k : WithBot ℕ)) : a ≤ b := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe m =>
    induction b using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.bot_add] at h
      simp at h
    | coe q =>
      rw [show ((k : WithBot ℕ)) = (WithBot.some k) from rfl, ← WithBot.coe_add,
        ← WithBot.coe_add, WithBot.coe_le_coe] at h
      exact_mod_cast (by omega : m ≤ q)

theorem lt_of_add_pos_le {a b : WithBot ℕ} {k : ℕ} (hk : 1 ≤ k) (hb : b ≠ ⊥)
    (h : a + (k : WithBot ℕ) ≤ b) : a < b := by
  induction a using WithBot.recBotCoe with
  | bot => exact lt_of_le_of_ne bot_le (Ne.symm hb)
  | coe m =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd rfl hb
    | coe q =>
      rw [show ((k : WithBot ℕ)) = (WithBot.some k) from rfl, ← WithBot.coe_add,
        WithBot.coe_le_coe] at h
      exact_mod_cast (by omega : m < q)

/-- **Cohn's congruence** (Cohn *FIR* §2.5, formula (2), mirrored):
`(a b)* = a* b` up to a term of degree `< deg b`. -/
theorem degFn_rtrans_mul_sub_lt (w : FreeMonoid σ) (g : FA K σ) (hg : g ≠ 0) (f : FA K σ) :
    degFn (rtrans w (f * g) - rtrans (K := K) w f * g) < degFn g := by
  have hgb : degFn g ≠ ⊥ := fun h => hg (degFn_eq_bot_iff.1 h)
  have hbot : (⊥ : WithBot ℕ) < degFn g := lt_of_le_of_ne bot_le (Ne.symm hgb)
  induction f using MonoidAlgebra.induction_on with
  | of u =>
      rw [MonoidAlgebra.of_apply]
      by_cases hA : ∃ z, u = w * z
      · obtain ⟨z, rfl⟩ := hA
        rw [show (MonoidAlgebra.single (w * z) (1 : K))
            = MonoidAlgebra.single w (1 : K) * MonoidAlgebra.single z (1 : K) by
          rw [MonoidAlgebra.single_mul_single, one_mul], mul_assoc,
          rtrans_single_self_mul, rtrans_single_self_mul, sub_self, degFn_zero]
        exact hbot
      · by_cases hB : ∃ y, w = u * y
        · obtain ⟨y, hy⟩ := hB
          have hy1 : y ≠ 1 := by
            rintro rfl
            exact hA ⟨1, by rw [hy, mul_one, mul_one]⟩
          have hylen : 1 ≤ FreeMonoid.length y := by
            rcases Nat.eq_zero_or_pos (FreeMonoid.length y) with h0 | h0
            · exact absurd (FreeMonoid.length_eq_zero.mp h0) hy1
            · exact h0
          rw [rtrans_single_mul_of_prefix hy, rtrans_single_of_not_prefix hA, zero_mul, sub_zero]
          exact lt_of_add_pos_le hylen hgb (degFn_rtrans_add_le y g)
        · rw [rtrans_single_mul_of_incomparable hA hB, rtrans_single_of_not_prefix hA, zero_mul,
            sub_self, degFn_zero]
          exact hbot
  | add x y hx hy =>
      have hsplit : rtrans w ((x + y) * g) - rtrans (K := K) w (x + y) * g
          = (rtrans w (x * g) - rtrans (K := K) w x * g)
            + (rtrans w (y * g) - rtrans (K := K) w y * g) := by
        rw [add_mul, map_add, map_add, add_mul]
        abel
      rw [hsplit]
      exact lt_of_le_of_lt (degFn_add_le _ _) (max_lt hx hy)
  | smul r x hx =>
      have hsplit : rtrans w ((r • x) * g) - rtrans (K := K) w (r • x) * g
          = r • (rtrans w (x * g) - rtrans (K := K) w x * g) := by
        rw [smul_mul_assoc, map_smul, map_smul, smul_mul_assoc, smul_sub]
      rw [hsplit]
      exact lt_of_le_of_lt (degFn_smul_le r _) hx

/-! ### The free algebra satisfies the weak algorithm

This is Cohn, *FIR* Theorem 2.5.1 (c) ⇒ (a) / Corollary 2.5.2, specialized to the free
algebra and mirrored to the left: Cohn proves the *left*-hand weak algorithm using *right*
transductions, which is exactly the side we need. -/

theorem single_one_mul (a : K) (x : FA K σ) :
    MonoidAlgebra.single (1 : FreeMonoid σ) a * x = a • x := by
  have h : MonoidAlgebra.single (1 : FreeMonoid σ) a = algebraMap K (FA K σ) a := by
    rw [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single,
      smul_eq_mul, mul_one]
  rw [h, ← Algebra.smul_def]

/-- **The free algebra satisfies the weak algorithm** for its natural filtration
(Cohn, *FIR* Corollary 2.5.2, mirrored to the left). -/
theorem hasWeakAlgorithm_filtration : (filtration K σ).HasWeakAlgorithm := by
  classical
  intro ι _ u hdep w hwinj hwref
  rcases hdep with ⟨i0, hi0⟩ | ⟨c, hlt⟩
  · exact ⟨i0, Or.inl hi0⟩
  have hwref' : ∀ i j, degFn (u i) < degFn (u j) → w i < w j := hwref
  set d : WithBot ℕ := Finset.univ.sup fun i => degFn (c i) + degFn (u i) with hd
  have hlt' : degFn (∑ i, c i * u i) < d := hlt
  have hdbot : (⊥ : WithBot ℕ) < d := lt_of_le_of_lt bot_le hlt'
  have hne : (Finset.univ : Finset ι).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset ι) with he | h
    · rw [hd, he, Finset.sup_empty] at hdbot
      exact absurd hdbot (lt_irrefl _)
    · exact h
  set S : Finset ι := {i ∈ Finset.univ | degFn (c i) + degFn (u i) = d} with hSdef
  have hSmem : ∀ i ∈ S, degFn (c i) + degFn (u i) = d := by
    intro i hi
    simpa [hSdef] using hi
  have hSle : ∀ i, degFn (c i) + degFn (u i) ≤ d := fun i =>
    Finset.le_sup (f := fun i => degFn (c i) + degFn (u i)) (Finset.mem_univ i)
  have hSne : S.Nonempty := by
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_mem_eq_sup Finset.univ hne fun i => degFn (c i) + degFn (u i)
    exact ⟨i, by simp [hSdef, hd, ← hi]⟩
  -- restrict the relation to the indices attaining the maximum
  have hltS : degFn (∑ i ∈ S, c i * u i) < d := by
    have hsplit : ∑ i ∈ S, c i * u i
        = (∑ i, c i * u i) - ∑ i ∈ Finset.univ \ S, c i * u i := by
      rw [eq_sub_iff_add_eq, add_comm, Finset.sum_sdiff (Finset.subset_univ S)]
    have hout : degFn (∑ i ∈ Finset.univ \ S, c i * u i) < d := by
      refine lt_of_le_of_lt ((filtration K σ).deg_sum_le (Finset.univ \ S) _) ?_
      rw [Finset.sup_lt_iff hdbot]
      intro i hi
      refine lt_of_le_of_lt (degFn_mul_le (c i) (u i)) ?_
      refine lt_of_le_of_ne (hSle i) fun heq => ?_
      exact absurd (by simp [hSdef, heq]) (Finset.mem_sdiff.1 hi).2
    rw [hsplit]
    exact lt_of_le_of_lt (degFn_sub_le _ _) (max_lt hlt' hout)
  -- choose the index of maximal `deg (u i)` in `S`, last in the listing among ties
  set M : WithBot ℕ := S.sup fun i => degFn (u i) with hM
  set S' : Finset ι := {i ∈ S | degFn (u i) = M} with hS'def
  have hS'ne : S'.Nonempty := by
    obtain ⟨i, hi, hiM⟩ := Finset.exists_mem_eq_sup S hSne fun i => degFn (u i)
    exact ⟨i, by simp [hS'def, hi, hM, ← hiM]⟩
  obtain ⟨i₀, hi₀S', hi₀max⟩ := Finset.exists_max_image S' w hS'ne
  have hi₀mem : i₀ ∈ S ∧ degFn (u i₀) = M := by
    have hmem := hi₀S'
    rw [hS'def, Finset.mem_filter] at hmem
    exact hmem
  have hi₀S : i₀ ∈ S := hi₀mem.1
  have hi₀M : degFn (u i₀) = M := hi₀mem.2
  have hwlt : ∀ i ∈ S, i ≠ i₀ → w i < w i₀ := by
    intro i hi hne'
    rcases lt_or_eq_of_le (Finset.le_sup (f := fun i => degFn (u i)) hi : degFn (u i) ≤ M)
      with h | h
    · exact hwref' i i₀ (hi₀M ▸ h)
    · have hiS' : i ∈ S' := by
        rw [hS'def, Finset.mem_filter]
        exact ⟨hi, h.trans hM.symm⟩
      exact lt_of_le_of_ne (hi₀max i hiS') fun he => hne' (hwinj he)
  -- the transduction at a longest word of `c i₀`
  have hd₀ : degFn (c i₀) + degFn (u i₀) = d := hSmem i₀ hi₀S
  have hci₀ : c i₀ ≠ 0 := by
    intro h0
    rw [h0, degFn_zero] at hd₀
    simp only [WithBot.bot_add] at hd₀
    exact absurd hd₀ hdbot.ne
  have hui₀ : u i₀ ≠ 0 := by
    intro h0
    rw [h0, degFn_zero] at hd₀
    simp only [WithBot.add_bot] at hd₀
    exact absurd hd₀ hdbot.ne
  have hSu : ∀ i ∈ S, u i ≠ 0 := by
    intro i hi h0
    have := hSmem i hi
    rw [h0, degFn_zero] at this
    simp only [WithBot.add_bot] at this
    exact absurd this hdbot.ne
  obtain ⟨W, hWmem, hWdeg⟩ := exists_degFn_eq hci₀
  set r : ℕ := FreeMonoid.length W with hr
  set α : K := (c i₀).coeff W with hαdef
  have hα0 : α ≠ 0 := Finsupp.mem_support_iff.1 hWmem
  have hrtα : rtrans W (c i₀) = MonoidAlgebra.single (1 : FreeMonoid σ) α := by
    refine MonoidAlgebra.coeff_injective (Finsupp.ext fun t => ?_)
    rw [coeff_rtrans]
    rcases eq_or_ne t 1 with rfl | ht
    · simp [hαdef, MonoidAlgebra.coeff_single]
    · have hz : (c i₀).coeff (W * t) = 0 := by
        by_contra hcon
        have hle := le_degFn (Finsupp.mem_support_iff.2 hcon)
        rw [hWdeg, FreeMonoid.length_mul] at hle
        have hle' : r + FreeMonoid.length t ≤ r := by exact_mod_cast hle
        have ht0 : FreeMonoid.length t = 0 := by omega
        exact ht (FreeMonoid.length_eq_zero.mp ht0)
      rw [hz]
      simp [MonoidAlgebra.coeff_single, Ne.symm ht]
  -- apply the transduction to the relation
  have hEi : ∀ i ∈ S,
      degFn (rtrans W (c i * u i) - rtrans W (c i) * u i) < degFn (u i₀) := by
    intro i hi
    refine lt_of_lt_of_le (degFn_rtrans_mul_sub_lt W (u i) (hSu i hi) (c i)) ?_
    rw [hi₀M]
    exact Finset.le_sup (f := fun i => degFn (u i)) hi
  have hsum1 : rtrans W (∑ i ∈ S, c i * u i)
      = (∑ i ∈ S, rtrans W (c i) * u i)
        + ∑ i ∈ S, (rtrans W (c i * u i) - rtrans W (c i) * u i) := by
    rw [map_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by abel
  have hdr : d = degFn (u i₀) + (r : WithBot ℕ) := by
    rw [← hd₀, hWdeg, add_comm]
  have hA : degFn (rtrans W (∑ i ∈ S, c i * u i)) < degFn (u i₀) := by
    have h1 := degFn_rtrans_add_le W (∑ i ∈ S, c i * u i)
    have h2 : degFn (∑ i ∈ S, c i * u i) < degFn (u i₀) + (r : WithBot ℕ) := hdr ▸ hltS
    exact lt_of_add_lt_add_right (lt_of_le_of_lt h1 h2)
  have hbotu : (⊥ : WithBot ℕ) < degFn (u i₀) :=
    lt_of_le_of_ne bot_le fun h => hui₀ (degFn_eq_bot_iff.1 h.symm)
  have hB : degFn (∑ i ∈ S, (rtrans W (c i * u i) - rtrans W (c i) * u i))
      < degFn (u i₀) := by
    refine lt_of_le_of_lt ((filtration K σ).deg_sum_le S _) ?_
    rw [Finset.sup_lt_iff hbotu]
    exact hEi
  have hC : degFn (∑ i ∈ S, rtrans W (c i) * u i) < degFn (u i₀) := by
    have heq : (∑ i ∈ S, rtrans W (c i) * u i)
        = rtrans W (∑ i ∈ S, c i * u i)
          - ∑ i ∈ S, (rtrans W (c i * u i) - rtrans W (c i) * u i) := by
      rw [hsum1]; abel
    rw [heq]
    exact lt_of_le_of_lt (degFn_sub_le _ _) (max_lt hA hB)
  -- split off the `i₀` term and divide by the leading coefficient
  set T : FA K σ := ∑ i ∈ S.erase i₀, rtrans W (c i) * u i with hTdef
  have hsplit0 : (∑ i ∈ S, rtrans W (c i) * u i) = α • u i₀ + T := by
    rw [hTdef, ← Finset.add_sum_erase S _ hi₀S, hrtα, single_one_mul]
  refine ⟨i₀, Or.inr ⟨fun i => if i ∈ S.erase i₀ then -(α⁻¹ • rtrans W (c i)) else 0, ?_, ?_⟩⟩
  · have hγ : (∑ i, (if i ∈ S.erase i₀ then -(α⁻¹ • rtrans W (c i)) else 0)
        * (if w i < w i₀ then u i else 0)) = -(α⁻¹ • T) := by
      rw [← Finset.sum_subset (Finset.subset_univ (S.erase i₀))
        (fun i _ hi => by rw [ite_eq_right hi, zero_mul])]
      rw [hTdef, Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hwi : w i < w i₀ := hwlt i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
      rw [ite_eq_left hi, ite_eq_left hwi, neg_mul, smul_mul_assoc]
    change degFn (u i₀ - _) < degFn (u i₀)
    rw [hγ, sub_neg_eq_add]
    have heq : u i₀ + α⁻¹ • T = α⁻¹ • (α • u i₀ + T) := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hα0, one_smul]
    rw [heq, ← hsplit0]
    exact lt_of_le_of_lt (degFn_smul_le _ _) hC
  · intro i
    change degFn (if i ∈ S.erase i₀ then -(α⁻¹ • rtrans W (c i)) else 0)
      + degFn (if w i < w i₀ then u i else 0) ≤ degFn (u i₀)
    by_cases hi : i ∈ S.erase i₀
    · have hwi : w i < w i₀ := hwlt i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
      rw [ite_eq_left hi, ite_eq_left hwi, degFn_neg]
      have h1 : degFn (α⁻¹ • rtrans W (c i)) ≤ degFn (rtrans W (c i)) := degFn_smul_le _ _
      refine le_trans (add_le_add h1 le_rfl) ?_
      refine le_of_add_le_add_right' (k := r) ?_
      calc degFn (rtrans W (c i)) + degFn (u i) + (r : WithBot ℕ)
          = degFn (rtrans W (c i)) + (r : WithBot ℕ) + degFn (u i) := by
            rw [add_right_comm]
        _ ≤ degFn (c i) + degFn (u i) :=
            add_le_add (degFn_rtrans_add_le W (c i)) le_rfl
        _ = d := hSmem i (Finset.mem_of_mem_erase hi)
        _ = degFn (u i₀) + (r : WithBot ℕ) := hdr
    · rw [ite_eq_right hi, degFn_zero]
      simp

/-! ### Corollaries: the free algebra is a left fir -/

/-- **Cohn's theorem** (Cohn *FIR* Theorem 2.5.3 + Theorem 2.4.6): every left ideal of the
free algebra is a free module. -/
theorem free_of_ideal (I : Ideal (FA K σ)) : Module.Free (FA K σ) I :=
  (filtration K σ).free_of_hasWeakAlgorithm hasWeakAlgorithm_filtration I

/-- The free algebra has invariant basis number: the augmentation is a ring map onto the
field `K`, and IBN transfers backwards along any ring map (`invariantBasisNumber_of_ringHom`). -/
theorem invariantBasisNumber_fa : InvariantBasisNumber (FA K σ) :=
  invariantBasisNumber_of_ringHom (eps (K := K) (σ := σ)).toRingHom

end FA

end LeftPCI
