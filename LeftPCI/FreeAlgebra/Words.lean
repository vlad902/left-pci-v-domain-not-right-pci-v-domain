module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.FreeMonoid.UniqueProds
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Span.Basic

@[expose] public section

/-!
# The free algebra by words: leading-letter derivations, the augmentation, and degrees

This file is the word-combinatorics layer under the proof that the free algebra is a fir
(`LeftPCI/FreeAlgebra/Fir.lean`).  The free `K`-algebra on a type `σ` of generators is taken in
its concrete presentation

```
FA K σ = MonoidAlgebra K (FreeMonoid σ)
```

so that every element has honest coefficients indexed by words.  What is developed here:

* `FA.gen g` — the generator `g`;
* `FA.eps : FA K σ →ₐ[K] K` — the **constant term**, an algebra map (a word is `1` iff both its
  factors are);
* `FA.del g : FA K σ →ₗ[K] FA K σ` — "**strip a leading `g`**", `(del g h).coeff w = h.coeff (g·w)`,
  with the two facts that drive everything downstream:
  * `FA.del_mul` : `del g (p * f) = eps p • del g f + (del g p) * f` (a twisted derivation), and
  * `FA.recon` : `h = eps h + ∑ g, gen g * del g h` for `σ` finite — the direct-sum decomposition
    `FA = K ⊕ ⨁_g (gen g) · FA` in usable form;
* `FA.LowDeg h n` (all words of `h` have length `≥ n`), multiplicative and separating
  (`FA.eq_zero_of_lowDeg`), which replaces any appeal to completions;
* `FA.coeff_mul_of_maxLen` — the top-length coefficient of a product, whence
  `FA.eq_C_of_mul_eq_one`: a **one-sided inverse in a free algebra forces a scalar**.
-/

namespace LeftPCI

/-- The free `K`-algebra on the generating set `σ`, presented as the monoid algebra of the free
monoid so that coefficients of words are directly available. -/
abbrev FA (K : Type*) [Field K] (σ : Type*) := MonoidAlgebra K (FreeMonoid σ)

namespace FA

open MonoidAlgebra Finsupp

variable {K : Type*} [Field K] {σ : Type*}

/-- The generator `g`, as an element of the free algebra. -/
noncomputable def gen (g : σ) : FA K σ := single (FreeMonoid.of g) 1

@[simp] theorem coeff_gen_self (g : σ) :
    (gen (K := K) g).coeff (FreeMonoid.of g) = 1 := by simp [gen]

theorem coeff_gen_of_ne {g : σ} {w : FreeMonoid σ} (hw : w ≠ FreeMonoid.of g) :
    (gen (K := K) g).coeff w = 0 := by
  simp [gen, hw]

theorem of_ne_one (g : σ) : (FreeMonoid.of g) ≠ (1 : FreeMonoid σ) := by
  intro h; simpa using congrArg FreeMonoid.length h

/-! ### The augmentation (constant term) -/

/-- The constant term, as a monoid hom on words: `1 ↦ 1`, every nonempty word `↦ 0`. -/
def epsMonoidHom : FreeMonoid σ →* K := FreeMonoid.lift fun _ => 0

@[simp] theorem epsMonoidHom_of (g : σ) : epsMonoidHom (K := K) (FreeMonoid.of g) = 0 :=
  FreeMonoid.lift_eval_of _ _

theorem epsMonoidHom_eq_zero {w : FreeMonoid σ} (hw : w ≠ 1) : epsMonoidHom (K := K) w = 0 := by
  induction w using FreeMonoid.casesOn with
  | one => exact absurd rfl hw
  | of_mul a v => simp

/-- The **constant term** of an element of the free algebra, as a `K`-algebra map. -/
noncomputable def eps : FA K σ →ₐ[K] K := MonoidAlgebra.lift K K _ epsMonoidHom

theorem eps_apply (h : FA K σ) : eps h = h.coeff 1 := by
  rw [eps, MonoidAlgebra.lift_apply]
  rw [Finsupp.sum_eq_single 1 (fun w _ hw => by simp [epsMonoidHom_eq_zero hw]) (by simp)]
  simp

@[simp] theorem eps_gen (g : σ) : eps (gen (K := K) g) = 0 := by
  rw [eps_apply, coeff_gen_of_ne (Ne.symm (of_ne_one g))]

/-! ### Stripping a leading generator -/

theorem of_mul_injective (g : σ) :
    Function.Injective (fun w : FreeMonoid σ => FreeMonoid.of g * w) :=
  fun _ _ h => mul_left_cancel h

theorem head_eq_of_of_mul_eq {g g' : σ} {w v : FreeMonoid σ}
    (h : FreeMonoid.of g * w = FreeMonoid.of g' * v) : g = g' := by
  simpa using congrArg (fun x => (FreeMonoid.toList x).head?) h

/-- **Strip a leading `g`**: the `K`-linear map with `(del g h).coeff w = h.coeff (g · w)`. -/
noncomputable def del (g : σ) : FA K σ →ₗ[K] FA K σ :=
  (MonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap ∘ₗ
    Finsupp.lcomapDomain _ (of_mul_injective g) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv K).toLinearMap

@[simp] theorem coeff_del (g : σ) (h : FA K σ) (w : FreeMonoid σ) :
    (del g h).coeff w = h.coeff (FreeMonoid.of g * w) := rfl

theorem coeff_gen_mul (g : σ) (p : FA K σ) (w : FreeMonoid σ) :
    (gen g * p).coeff (FreeMonoid.of g * w) = p.coeff w := by
  rw [gen, MonoidAlgebra.coeff_single_mul_eq_mul_coeff w (fun m' _ => mul_right_inj _), one_mul]

theorem coeff_gen_mul_of_ne {g g' : σ} (hne : g ≠ g') (p : FA K σ) (w : FreeMonoid σ) :
    (gen (K := K) g * p).coeff (FreeMonoid.of g' * w) = 0 := by
  rw [gen]
  refine MonoidAlgebra.coeff_single_mul_of_forall_mul_ne 1 p ?_
  intro d hd
  exact hne (head_eq_of_of_mul_eq hd)

theorem coeff_gen_mul_one (g : σ) (p : FA K σ) : (gen (K := K) g * p).coeff 1 = 0 := by
  rw [gen]
  refine MonoidAlgebra.coeff_single_mul_of_forall_mul_ne 1 p ?_
  intro d hd
  simpa using congrArg FreeMonoid.length hd

@[simp] theorem del_gen_mul (g : σ) (p : FA K σ) : del g (gen g * p) = p := by
  refine MonoidAlgebra.coeff_injective ?_
  ext w
  simp [coeff_gen_mul]

theorem del_gen_mul_of_ne {g g' : σ} (hne : g ≠ g') (p : FA K σ) :
    del g' (gen (K := K) g * p) = 0 := by
  refine MonoidAlgebra.coeff_injective ?_
  ext w
  simp [coeff_gen_mul_of_ne hne]

@[simp] theorem del_gen (g : σ) : del g (gen (K := K) g) = 1 := by
  simpa using del_gen_mul (K := K) g 1

theorem del_gen_of_ne {g g' : σ} (hne : g ≠ g') : del g' (gen (K := K) g) = 0 := by
  simpa using del_gen_mul_of_ne (K := K) hne 1

@[simp] theorem del_one (g : σ) : del g (1 : FA K σ) = 0 := by
  refine MonoidAlgebra.coeff_injective ?_
  ext w
  have : (FreeMonoid.of g * w) ≠ 1 := by
    intro h; simpa using congrArg FreeMonoid.length h
  simp [MonoidAlgebra.one_def, this]

/-- **The twisted derivation rule.**  Stripping a leading `g` from a product. -/
theorem del_mul (g : σ) (p f : FA K σ) :
    del g (p * f) = eps p • del g f + (del g p) * f := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
      induction w using FreeMonoid.casesOn with
      | one => simp [← MonoidAlgebra.one_def]
      | of_mul a v =>
          have hof : (MonoidAlgebra.of K (FreeMonoid σ)) (FreeMonoid.of a * v)
              = gen a * (MonoidAlgebra.of K (FreeMonoid σ)) v := by
            simp [gen, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single]
          have heps : eps (gen a * (MonoidAlgebra.of K (FreeMonoid σ)) v) = 0 := by
            rw [map_mul, eps_gen, zero_mul]
          rw [hof, heps, zero_smul, zero_add, mul_assoc]
          rcases eq_or_ne a g with rfl | hne
          · rw [del_gen_mul, del_gen_mul]
          · rw [del_gen_mul_of_ne hne, del_gen_mul_of_ne hne, zero_mul]
  | add x y hx hy =>
      rw [add_mul, map_add, hx, hy, map_add, map_add, add_smul, add_mul]
      exact add_add_add_comm _ _ _ _
  | smul r x hx =>
      rw [smul_mul_assoc, map_smul, hx, map_smul, map_smul, smul_add, smul_smul, smul_mul_assoc,
        smul_eq_mul]

/-! ### Reconstruction: `FA = K ⊕ ⨁_g gen g · FA` -/

@[simp] theorem coeff_algebraMap_one (c : K) :
    ((algebraMap K (FA K σ)) c).coeff 1 = c := by
  simp [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def]

theorem coeff_algebraMap_of_ne (c : K) {w : FreeMonoid σ} (hw : w ≠ 1) :
    ((algebraMap K (FA K σ)) c).coeff w = 0 := by
  simp [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def, hw]

/-- **Reconstruction.**  Every element is its constant term plus the sum, over generators, of
`g` times what remains after stripping `g`.  This is the direct-sum decomposition
`FA K σ = K ⊕ ⨁_g (gen g) · FA K σ`. -/
theorem recon [Fintype σ] (h : FA K σ) :
    h = algebraMap K (FA K σ) (eps h) + ∑ g : σ, gen g * del g h := by
  classical
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun w => ?_)
  have hsum : ((algebraMap K (FA K σ)) (eps h) + ∑ g : σ, gen g * del g h).coeff w
      = ((algebraMap K (FA K σ)) (eps h)).coeff w + ∑ g : σ, (gen g * del g h).coeff w := by
    simp
  rw [hsum]
  induction w using FreeMonoid.casesOn with
  | one =>
      rw [coeff_algebraMap_one, eps_apply,
        Finset.sum_eq_zero (fun g _ => coeff_gen_mul_one g _), add_zero]
  | of_mul a v =>
      have hne : (FreeMonoid.of a * v) ≠ 1 := by
        intro hcon; simpa using congrArg FreeMonoid.length hcon
      rw [coeff_algebraMap_of_ne _ hne, zero_add,
        Finset.sum_eq_single a (fun g _ hg => coeff_gen_mul_of_ne hg _ _) (by simp),
        coeff_gen_mul, coeff_del]

/-! ### The length filtration -/

/-- `LowDeg h n` : every word occurring in `h` has length at least `n`. -/
def LowDeg (h : FA K σ) (n : ℕ) : Prop := ∀ w ∈ h.coeff.support, n ≤ FreeMonoid.length w

theorem lowDeg_zero (h : FA K σ) : LowDeg h 0 := fun _ _ => Nat.zero_le _

theorem lowDeg_one_of_eps_eq_zero {h : FA K σ} (hh : eps h = 0) : LowDeg h 1 := by
  intro w hw
  rcases Nat.eq_zero_or_pos (FreeMonoid.length w) with h0 | hpos
  · exfalso
    rw [FreeMonoid.length_eq_zero.mp h0] at hw
    rw [eps_apply] at hh
    exact (Finsupp.mem_support_iff.mp hw) hh
  · exact hpos

theorem lowDeg_mul {x y : FA K σ} {m n : ℕ} (hx : LowDeg x m) (hy : LowDeg y n) :
    LowDeg (x * y) (m + n) := by
  classical
  intro w hw
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ :=
    Finset.mem_mul.mp (MonoidAlgebra.support_coeff_mul_subset x y hw)
  rw [FreeMonoid.length_mul]
  exact Nat.add_le_add (hx _ hw₁) (hy _ hw₂)

theorem lowDeg_pow {x : FA K σ} (hx : LowDeg x 1) : ∀ n, LowDeg (x ^ n) n
  | 0 => lowDeg_zero _
  | n + 1 => by rw [pow_succ]; exact lowDeg_mul (lowDeg_pow hx n) hx

theorem eq_zero_of_lowDeg {h : FA K σ} (H : ∀ n, LowDeg h n) : h = 0 := by
  by_contra hne
  have hsupp : h.coeff.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro hc
    exact hne (MonoidAlgebra.coeff_injective (by simpa using hc))
  obtain ⟨w, hw⟩ := hsupp
  exact absurd (H (FreeMonoid.length w + 1) w hw) (by omega)

/-- If `f = w * f` with `w` in the augmentation ideal, then `f = 0`. -/
theorem eq_zero_of_eq_mul_self {w f : FA K σ} (hw : eps w = 0) (h : f = w * f) : f = 0 := by
  refine eq_zero_of_lowDeg fun n => ?_
  have hpow : ∀ n, f = w ^ n * f := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, ← h, ← ih]
  have := lowDeg_mul (lowDeg_pow (lowDeg_one_of_eps_eq_zero hw) n) (lowDeg_zero f)
  rw [Nat.add_zero] at this
  rw [hpow n]
  exact this

/-! ### Top-length coefficients and one-sided inverses -/

/-- The coefficient of `wx * wy` in `x * y`, when `wx` and `wy` have maximal length in the
supports of `x` and `y`: no other pair of words can multiply to it. -/
theorem coeff_mul_of_maxLen {x y : FA K σ} {wx wy : FreeMonoid σ}
    (hxmax : ∀ w ∈ x.coeff.support, FreeMonoid.length w ≤ FreeMonoid.length wx)
    (hymax : ∀ w ∈ y.coeff.support, FreeMonoid.length w ≤ FreeMonoid.length wy) :
    (x * y).coeff (wx * wy) = x.coeff wx * y.coeff wy := by
  classical
  rw [MonoidAlgebra.coeff_mul]
  rw [Finsupp.sum_eq_single (a := wx)]
  · rw [Finsupp.sum_eq_single (a := wy)]
    · simp
    · intro w hw hne
      simp only [ite_eq_right_iff]
      intro hcon
      exact absurd (mul_left_cancel hcon) hne
    · intro h; simp
  · intro w hw hne
    rw [Finsupp.sum]
    refine Finset.sum_eq_zero fun v hv => ?_
    simp only [ite_eq_right_iff]
    intro hcon
    exfalso
    have hlen : FreeMonoid.length w + FreeMonoid.length v
        = FreeMonoid.length wx + FreeMonoid.length wy := by
      simpa [FreeMonoid.length_mul] using congrArg FreeMonoid.length hcon
    have h1 := hxmax w (Finsupp.mem_support_iff.mpr hw)
    have h2 := hymax v hv
    have hwlen : FreeMonoid.length w = FreeMonoid.length wx := by omega
    refine hne ?_
    have hlist := congrArg FreeMonoid.toList hcon
    simp only [FreeMonoid.toList_mul] at hlist
    exact FreeMonoid.toList.injective
      (List.append_inj hlist (by simpa [FreeMonoid.length] using hwlen)).1
  · intro h; simp

/-- **A one-sided inverse in a free algebra forces a scalar.** -/
theorem eq_algebraMap_of_mul_eq_one {g f : FA K σ} (h : g * f = 1) :
    f = algebraMap K (FA K σ) (eps f) := by
  classical
  have hf : f ≠ 0 := by rintro rfl; rw [mul_zero] at h; exact zero_ne_one h
  have hg : g ≠ 0 := by rintro rfl; rw [zero_mul] at h; exact zero_ne_one h
  obtain ⟨wf, hwf, hwfmax⟩ : ∃ wf ∈ f.coeff.support,
      ∀ w ∈ f.coeff.support, FreeMonoid.length w ≤ FreeMonoid.length wf := by
    refine Finset.exists_max_image _ _ ?_
    rw [Finsupp.support_nonempty_iff]
    intro hc; exact hf (MonoidAlgebra.coeff_injective (by simpa using hc))
  obtain ⟨wg, hwg, hwgmax⟩ : ∃ wg ∈ g.coeff.support,
      ∀ w ∈ g.coeff.support, FreeMonoid.length w ≤ FreeMonoid.length wg := by
    refine Finset.exists_max_image _ _ ?_
    rw [Finsupp.support_nonempty_iff]
    intro hc; exact hg (MonoidAlgebra.coeff_injective (by simpa using hc))
  have hcoe := coeff_mul_of_maxLen hwgmax hwfmax
  rw [h] at hcoe
  have hne : (g.coeff wg) * (f.coeff wf) ≠ 0 :=
    mul_ne_zero (Finsupp.mem_support_iff.mp hwg) (Finsupp.mem_support_iff.mp hwf)
  have hwgwf : wg * wf = 1 := by
    by_contra hcon
    refine hne ?_
    rw [← hcoe]
    simp [MonoidAlgebra.one_def, hcon]
  have hwf1 : wf = 1 := eq_one_of_mul_left hwgwf
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun w => ?_)
  rcases eq_or_ne w 1 with rfl | hw
  · rw [coeff_algebraMap_one, eps_apply]
  · rw [coeff_algebraMap_of_ne _ hw]
    by_contra hcon
    have hle := hwfmax w (Finsupp.mem_support_iff.mpr hcon)
    rw [hwf1] at hle
    simp only [FreeMonoid.length_one, Nat.le_zero] at hle
    exact hw (FreeMonoid.length_eq_zero.mp hle)

/-- A one-sided inverse in a free algebra makes the element a unit. -/
theorem isUnit_of_mul_eq_one {g f : FA K σ} (h : g * f = 1) : IsUnit f := by
  have hf := eq_algebraMap_of_mul_eq_one h
  have hne : eps f ≠ 0 := by
    intro hc
    rw [hc, map_zero] at hf
    rw [hf, mul_zero] at h
    exact zero_ne_one h
  rw [hf]
  exact (algebraMap K (FA K σ)).isUnit_map (IsUnit.mk0 _ hne)

/-! ### Head and last letters: `gen a · FA` and `FA · gen a` for different `a` meet in `0` -/

@[simp] theorem support_gen (a : σ) : (gen (K := K) a).coeff.support = {FreeMonoid.of a} := by
  simp [gen]

theorem head_of_mem_support_gen_mul {x : FA K σ} {a : σ} {w : FreeMonoid σ}
    (hw : w ∈ (gen a * x).coeff.support) : (FreeMonoid.toList w).head? = some a := by
  classical
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ :=
    Finset.mem_mul.mp (MonoidAlgebra.support_coeff_mul_subset _ _ hw)
  rw [support_gen, Finset.mem_singleton] at hw₁
  subst hw₁
  simp

theorem last_of_mem_support_mul_gen {x : FA K σ} {a : σ} {w : FreeMonoid σ}
    (hw : w ∈ (x * gen a).coeff.support) : (FreeMonoid.toList w).getLast? = some a := by
  classical
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ :=
    Finset.mem_mul.mp (MonoidAlgebra.support_coeff_mul_subset _ _ hw)
  rw [support_gen, Finset.mem_singleton] at hw₂
  subst hw₂
  simp [FreeMonoid.toList_mul, List.getLast?_append]

theorem gen_ne_zero (a : σ) : gen (K := K) a ≠ 0 := by
  intro h
  have h1 := coeff_gen_self (K := K) a
  rw [h] at h1
  simp at h1

theorem eq_zero_of_gen_mul_eq_zero {a : σ} {u : FA K σ} (h : gen a * u = 0) : u = 0 :=
  (mul_eq_zero.mp h).elim (fun h => absurd h (gen_ne_zero a)) id

theorem eq_zero_of_mul_gen_eq_zero {a : σ} {u : FA K σ} (h : u * gen a = 0) : u = 0 :=
  (mul_eq_zero.mp h).elim id (fun h => absurd h (gen_ne_zero a))

theorem eq_zero_of_support_empty {z : FA K σ} (h : ∀ w, w ∉ z.coeff.support) : z = 0 := by
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun w => ?_)
  simpa using not_imp_not.mpr Finsupp.mem_support_iff.mpr (h w)

theorem mem_support_add {x y : FA K σ} {w : FreeMonoid σ} (hw : w ∈ (x + y).coeff.support) :
    w ∈ x.coeff.support ∨ w ∈ y.coeff.support := by
  classical
  exact Finset.mem_union.mp (Finsupp.support_add (by simpa using hw))

/-- **Row disjointness on the left.**  `gen a · FA` and `gen b · FA` meet in `0` for `a ≠ b`. -/
theorem gen_mul_add_eq_zero {a b : σ} (hab : a ≠ b) {u v : FA K σ}
    (h : gen a * u + gen b * v = 0) : u = 0 ∧ v = 0 := by
  have hz : gen a * u = -(gen b * v) := add_eq_zero_iff_eq_neg.mp h
  have hzero : gen a * u = 0 := by
    refine eq_zero_of_support_empty fun w hw => ?_
    have h1 := head_of_mem_support_gen_mul hw
    rw [hz] at hw
    have hw' : w ∈ (gen b * v).coeff.support := by simpa using hw
    have h2 := head_of_mem_support_gen_mul hw'
    exact hab (Option.some_injective _ (h1.symm.trans h2))
  refine ⟨eq_zero_of_gen_mul_eq_zero hzero, eq_zero_of_gen_mul_eq_zero (a := b) ?_⟩
  have hb : -(gen b * v) = 0 := by rw [← hz, hzero]
  simpa using hb

/-- **Row disjointness on the right.**  `FA · gen a` and `FA · gen b` meet in `0` for `a ≠ b`. -/
theorem mul_gen_add_eq_zero {a b : σ} (hab : a ≠ b) {u v : FA K σ}
    (h : u * gen a + v * gen b = 0) : u = 0 ∧ v = 0 := by
  have hz : u * gen a = -(v * gen b) := add_eq_zero_iff_eq_neg.mp h
  have hzero : u * gen a = 0 := by
    refine eq_zero_of_support_empty fun w hw => ?_
    have h1 := last_of_mem_support_mul_gen hw
    rw [hz] at hw
    have hw' : w ∈ (v * gen b).coeff.support := by simpa using hw
    have h2 := last_of_mem_support_mul_gen hw'
    exact hab (Option.some_injective _ (h1.symm.trans h2))
  refine ⟨eq_zero_of_mul_gen_eq_zero hzero, eq_zero_of_mul_gen_eq_zero (a := b) ?_⟩
  have hb : -(v * gen b) = 0 := by rw [← hz, hzero]
  simpa using hb

/-- **Two rows with disjoint letters.**  `X · P = X' · Q` forces `P = Q = 0`, entrywise. -/
theorem gen_mul_pair_eq {a b a' b' : σ} (hab : a ≠ b) (hab' : a' ≠ b')
    (h1 : a ≠ a') (h2 : a ≠ b') (h3 : b ≠ a') (h4 : b ≠ b') {u v u' v' : FA K σ}
    (h : gen a * u + gen b * v = gen a' * u' + gen b' * v') :
    u = 0 ∧ v = 0 ∧ u' = 0 ∧ v' = 0 := by
  have hz : gen a * u + gen b * v = 0 := by
    refine eq_zero_of_support_empty fun w hw => ?_
    have hL : (FreeMonoid.toList w).head? = some a ∨ (FreeMonoid.toList w).head? = some b :=
      (mem_support_add hw).imp head_of_mem_support_gen_mul head_of_mem_support_gen_mul
    rw [h] at hw
    have hR : (FreeMonoid.toList w).head? = some a' ∨ (FreeMonoid.toList w).head? = some b' :=
      (mem_support_add hw).imp head_of_mem_support_gen_mul head_of_mem_support_gen_mul
    rcases hL with hL | hL <;> rcases hR with hR | hR <;>
      [exact h1 (Option.some_injective _ (hL.symm.trans hR));
       exact h2 (Option.some_injective _ (hL.symm.trans hR));
       exact h3 (Option.some_injective _ (hL.symm.trans hR));
       exact h4 (Option.some_injective _ (hL.symm.trans hR))]
  obtain ⟨hu, hv⟩ := gen_mul_add_eq_zero hab hz
  refine ⟨hu, hv, ?_, ?_⟩ <;>
    [exact (gen_mul_add_eq_zero hab' (by rw [← h, hz])).1;
     exact (gen_mul_add_eq_zero hab' (by rw [← h, hz])).2]

/-- **Two rows with disjoint letters, on the right.**  `P · X = Q · X'` forces `P = Q = 0`. -/
theorem mul_gen_pair_eq {a b a' b' : σ} (hab : a ≠ b) (hab' : a' ≠ b')
    (h1 : a ≠ a') (h2 : a ≠ b') (h3 : b ≠ a') (h4 : b ≠ b') {u v u' v' : FA K σ}
    (h : u * gen a + v * gen b = u' * gen a' + v' * gen b') :
    u = 0 ∧ v = 0 ∧ u' = 0 ∧ v' = 0 := by
  have hz : u * gen a + v * gen b = 0 := by
    refine eq_zero_of_support_empty fun w hw => ?_
    have hL : (FreeMonoid.toList w).getLast? = some a ∨ (FreeMonoid.toList w).getLast? = some b :=
      (mem_support_add hw).imp last_of_mem_support_mul_gen last_of_mem_support_mul_gen
    rw [h] at hw
    have hR : (FreeMonoid.toList w).getLast? = some a' ∨ (FreeMonoid.toList w).getLast? = some b' :=
      (mem_support_add hw).imp last_of_mem_support_mul_gen last_of_mem_support_mul_gen
    rcases hL with hL | hL <;> rcases hR with hR | hR <;>
      [exact h1 (Option.some_injective _ (hL.symm.trans hR));
       exact h2 (Option.some_injective _ (hL.symm.trans hR));
       exact h3 (Option.some_injective _ (hL.symm.trans hR));
       exact h4 (Option.some_injective _ (hL.symm.trans hR))]
  obtain ⟨hu, hv⟩ := mul_gen_add_eq_zero hab hz
  refine ⟨hu, hv, ?_, ?_⟩ <;>
    [exact (mul_gen_add_eq_zero hab' (by rw [← h, hz])).1;
     exact (mul_gen_add_eq_zero hab' (by rw [← h, hz])).2]

end FA

end LeftPCI
