module

public import LeftPCI.OrePoly.Division
public import LeftPCI.OrePoly.Degree
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Field.Subfield.Defs

@[expose] public section

namespace LeftPCI.Counterexample.Adjoin

universe u

open LeftPCI.OrePoly

variable {U : Type u} [DivisionRing U] {σ : U →+* U} (δ : OreDerivation U σ)

/-! ## Section 2.1: the modules `R/Rf` -/

/-- The companion matrix `C_f` of `f` (paper, §2.1): row `i` is `e_{i+1}` for `i + 1 < n`, and the
last row is `(-f₀, …, -f_{n-1})`, where `n = deg f`. -/
noncomputable def companion (f : OrePoly δ) :
    Matrix (Fin (natDegree δ f)) (Fin (natDegree δ f)) U :=
  Matrix.of fun i j =>
    if (i : ℕ) + 1 < natDegree δ f then (if (j : ℕ) = i + 1 then 1 else 0) else -coeff δ f j

/-- The polynomial `Σ vᵢ tⁱ` with coefficient vector `v` (paper, §2.1: the inverse of `b ↦ b̄`). -/
noncomputable def ofVec {n : ℕ} (v : Fin n → U) : OrePoly δ :=
  ∑ i, OrePoly.C δ (v i) * X δ ^ (i : ℕ)

/-- The pseudo-linear map `T(v) = σ(v) C + δ(v)` (paper, §2.1: `T_f` is the case `C = C_f`). -/
noncomputable def T {n : ℕ} (C : Matrix (Fin n) (Fin n) U) (v : Fin n → U) : Fin n → U :=
  Matrix.vecMul (σ ∘ v) C + δ ∘ v

/-- `g(T)(v) = Σ gᵢ Tⁱ(v)` (paper, §2.1). -/
noncomputable def evalT {n : ℕ} (C : Matrix (Fin n) (Fin n) U) (g : OrePoly δ) (v : Fin n → U) :
    Fin n → U :=
  ∑ i ∈ Finset.range (natDegree δ g + 1), coeff δ g i • (T δ C)^[i] v

theorem companion_apply (f : OrePoly δ) (i j : Fin (natDegree δ f)) :
    companion δ f i j =
      if (i : ℕ) + 1 < natDegree δ f then (if (j : ℕ) = i + 1 then 1 else 0) else -coeff δ f j :=
  rfl

/-- The entries of `C_f`, in additive form valid for every row. -/
theorem companion_apply' (f : OrePoly δ) (i j : Fin (natDegree δ f)) :
    companion δ f i j =
      (if (j : ℕ) = i + 1 then 1 else 0) + (if (i : ℕ) + 1 = natDegree δ f then -coeff δ f j else 0) := by
  have hi := i.2
  have hj := j.2
  rw [companion_apply]
  split_ifs <;> first | omega | simp

theorem coeff_ofVec {n : ℕ} (w : Fin n → U) (m : ℕ) :
    coeff δ (ofVec δ w) m = if h : m < n then w ⟨m, h⟩ else 0 := by
  unfold ofVec
  rw [coeff_sum]
  simp only [← monomial_eq, coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨m, h⟩]
    · simp
    · intro b _ hb
      exact ite_eq_right_iff.2 fun hbm => absurd (Fin.ext hbm) hb
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    exact ite_eq_right_iff.2 fun hbm => absurd (hbm ▸ b.2) h

theorem vecMul_companion (f : OrePoly δ) (hn : 0 < natDegree δ f) (w : Fin (natDegree δ f) → U)
    (j : Fin (natDegree δ f)) :
    Matrix.vecMul w (companion δ f) j =
      (if h : (j : ℕ) = 0 then 0 else w ⟨j - 1, by omega⟩)
        - w ⟨natDegree δ f - 1, by omega⟩ * coeff δ f j := by
  simp only [Matrix.vecMul, dotProduct, companion_apply', mul_add, Finset.sum_add_distrib,
    mul_ite, mul_one, mul_zero]
  rw [sub_eq_add_neg, ← mul_neg]
  congr 1
  · split_ifs with h
    · refine Finset.sum_eq_zero fun x _ => ite_eq_right_iff.2 fun h' => ?_
      omega
    · rw [Finset.sum_eq_single ⟨j - 1, by omega⟩]
      · exact ite_eq_left_iff.2 fun h' => absurd (by simp; omega) h'
      · intro b _ hb
        refine ite_eq_right_iff.2 fun h' => absurd (Fin.ext ?_) hb
        simp; omega
      · simp
  · rw [Finset.sum_eq_single ⟨natDegree δ f - 1, by omega⟩]
    · exact ite_eq_left_iff.2 fun h' => absurd (by simp; omega) h'
    · intro b _ hb
      refine ite_eq_right_iff.2 fun h' => absurd (Fin.ext ?_) hb
      simp; omega
    · simp

@[simp] theorem T_apply {n : ℕ} (C : Matrix (Fin n) (Fin n) U) (v : Fin n → U) (j : Fin n) :
    T δ C v j = Matrix.vecMul (σ ∘ v) C j + δ (v j) := rfl

/-- The key computation of the proof of **Lemma 2.1**: `t · Σ bᵢ tⁱ − Σ T(b)ᵢ tⁱ = σ(b_{n-1}) f`,
using `tⁿ ≡ −Σ fⱼ tʲ (mod Rf)`. -/
theorem X_mul_ofVec_sub_eq (f : OrePoly δ) (hf : leadingCoeff δ f = 1) (hn : 0 < natDegree δ f)
    (v : Fin (natDegree δ f) → U) :
    X δ * ofVec δ v - ofVec δ (T δ (companion δ f) v)
      = OrePoly.C δ (σ (v ⟨natDegree δ f - 1, by omega⟩)) * f := by
  refine ext_coeff δ fun m => ?_
  rw [coeff_sub, coeff_C_mul, coeff_ofVec]
  cases m with
  | zero =>
    rw [coeff_X_mul_zero, coeff_ofVec]
    simp [hn, vecMul_companion δ f hn]
  | succ k =>
    rw [coeff_X_mul_succ, coeff_ofVec, coeff_ofVec]
    rcases lt_trichotomy (k + 1) (natDegree δ f) with h | h | h
    · have hk : k < natDegree δ f := by omega
      simp [h, hk, vecMul_companion δ f hn]
    · have hk : k = natDegree δ f - 1 := by omega
      subst hk
      rw [h, coeff_natDegree, hf]
      simp [hn]
    · have hk : ¬ k < natDegree δ f := by omega
      have h' : ¬ k + 1 < natDegree δ f := by omega
      rw [coeff_eq_zero_of_natDegree_lt δ h]
      simp [hk, h']

theorem X_mul_ofVec_sub_mem (f : OrePoly δ) (hf : leadingCoeff δ f = 1) (hn : 0 < natDegree δ f)
    (v : Fin (natDegree δ f) → U) :
    X δ * ofVec δ v - ofVec δ (T δ (companion δ f) v) ∈ Ideal.span ({f} : Set (OrePoly δ)) := by
  rw [X_mul_ofVec_sub_eq δ f hf hn v]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)

/-! ### Linearity of `ofVec` -/

@[simp] theorem ofVec_zero {n : ℕ} : ofVec δ (0 : Fin n → U) = 0 :=
  ext_coeff δ fun m => by rw [coeff_ofVec]; simp

@[simp] theorem ofVec_add {n : ℕ} (v w : Fin n → U) : ofVec δ (v + w) = ofVec δ v + ofVec δ w :=
  ext_coeff δ fun m => by
    rw [coeff_add, coeff_ofVec, coeff_ofVec, coeff_ofVec]
    split_ifs <;> simp

@[simp] theorem ofVec_smul {n : ℕ} (a : U) (v : Fin n → U) :
    ofVec δ (a • v) = OrePoly.C δ a * ofVec δ v :=
  ext_coeff δ fun m => by
    rw [coeff_C_mul, coeff_ofVec, coeff_ofVec]
    split_ifs <;> simp

theorem ofVec_sum {n : ℕ} {ι : Type*} (s : Finset ι) (v : ι → Fin n → U) :
    ofVec δ (∑ i ∈ s, v i) = ∑ i ∈ s, ofVec δ (v i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ofVec_add, ih]

/-- A polynomial all of whose coefficients from index `n` on vanish is `ofVec` of its first `n`
coefficients. -/
theorem ofVec_coeff {n : ℕ} (p : OrePoly δ) (h : ∀ k, n ≤ k → coeff δ p k = 0) :
    ofVec δ (fun i : Fin n => coeff δ p i) = p :=
  ext_coeff δ fun m => by
    rw [coeff_ofVec]
    split_ifs with hm
    · rfl
    · exact (h m (by omega)).symm

/-- `g = Σ_{i ≤ deg g} gᵢ tⁱ`. -/
theorem eq_sum_range (g : OrePoly δ) :
    g = ∑ i ∈ Finset.range (natDegree δ g + 1), OrePoly.C δ (coeff δ g i) * X δ ^ i := by
  refine ext_coeff δ fun m => ?_
  rw [coeff_sum]
  simp only [← monomial_eq, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · exact coeff_eq_zero_of_natDegree_lt δ (by simp at hm; omega)

/-- Iterating `X_mul_ofVec_sub_mem`: `tⁱ b ≡ Tⁱ(b̄) (mod Rf)`. -/
theorem X_pow_mul_ofVec_sub_mem (f : OrePoly δ) (hf : leadingCoeff δ f = 1)
    (hn : 0 < natDegree δ f) (v : Fin (natDegree δ f) → U) (i : ℕ) :
    X δ ^ i * ofVec δ v - ofVec δ ((T δ (companion δ f))^[i] v)
      ∈ Ideal.span ({f} : Set (OrePoly δ)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', mul_assoc, Function.iterate_succ_apply']
    have h := X_mul_ofVec_sub_mem δ f hf hn ((T δ (companion δ f))^[i] v)
    have h2 := Ideal.mul_mem_left _ (X δ) ih
    have : X δ * (X δ ^ i * ofVec δ v) - ofVec δ (T δ (companion δ f) ((T δ (companion δ f))^[i] v))
        = X δ * (X δ ^ i * ofVec δ v - ofVec δ ((T δ (companion δ f))^[i] v))
          + (X δ * ofVec δ ((T δ (companion δ f))^[i] v)
            - ofVec δ (T δ (companion δ f) ((T δ (companion δ f))^[i] v))) := by
      noncomm_ring
    rw [this]
    exact Ideal.add_mem _ h2 h

/-- **Lemma 2.1** (paper, §2.1): for `f` monic of degree `n ≥ 1`, `g b ≡ Σ g(T_f)(b̄)ᵢ tⁱ (mod Rf)`,
i.e. the coefficient vector of the remainder of `g b` modulo `Rf` is `g(T_f)(b̄)`. -/
theorem mul_ofVec_sub_mem (f : OrePoly δ) (hf : leadingCoeff δ f = 1) (hn : 0 < natDegree δ f)
    (g : OrePoly δ) (v : Fin (natDegree δ f) → U) :
    g * ofVec δ v - ofVec δ (evalT δ (companion δ f) g v)
      ∈ Ideal.span ({f} : Set (OrePoly δ)) := by
  have key : g * ofVec δ v - ofVec δ (evalT δ (companion δ f) g v)
      = ∑ i ∈ Finset.range (natDegree δ g + 1), OrePoly.C δ (coeff δ g i) *
          (X δ ^ i * ofVec δ v - ofVec δ ((T δ (companion δ f))^[i] v)) := by
    unfold evalT
    rw [ofVec_sum]
    nth_rw 1 [eq_sum_range δ g]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ofVec_smul, mul_sub, mul_assoc]
  rw [key]
  exact Submodule.sum_mem _ fun i _ =>
    Ideal.mul_mem_left _ _ (X_pow_mul_ofVec_sub_mem δ f hf hn v i)

/-- The remainder of `m` on left division by `f` (paper, §2: `m = q f + b`, `deg b < deg f`). -/
noncomputable def rem (f : OrePoly δ) (hf : f ≠ 0) (m : OrePoly δ) : OrePoly δ :=
  (exists_leftDiv δ hf m).choose_spec.choose

theorem rem_spec (f : OrePoly δ) (hf : f ≠ 0) (m : OrePoly δ) :
    m = (exists_leftDiv δ hf m).choose * f + rem δ f hf m ∧
      (rem δ f hf m = 0 ∨ natDegree δ (rem δ f hf m) < natDegree δ f) :=
  (exists_leftDiv δ hf m).choose_spec.choose_spec

theorem coeff_rem_eq_zero (f : OrePoly δ) (hf : f ≠ 0) (m : OrePoly δ) {k : ℕ}
    (hk : natDegree δ f ≤ k) : coeff δ (rem δ f hf m) k = 0 := by
  rcases (rem_spec δ f hf m).2 with h | h
  · rw [h, coeff_zero]
  · exact coeff_eq_zero_of_natDegree_lt δ (by omega)

/-- The coefficient vector `b̄` of the remainder `b` of `m` modulo `Rf` (paper, §2.1). -/
noncomputable def remVec (f : OrePoly δ) (hf : f ≠ 0) (m : OrePoly δ) :
    Fin (natDegree δ f) → U :=
  fun i => coeff δ (rem δ f hf m) i

theorem ofVec_remVec (f : OrePoly δ) (hf : f ≠ 0) (m : OrePoly δ) :
    ofVec δ (remVec δ f hf m) = rem δ f hf m :=
  ofVec_coeff δ _ fun _ hk => coeff_rem_eq_zero δ f hf m hk

/-- `m ≡ Σ (remVec m)ᵢ tⁱ (mod Rf)` (paper, §2.1: the identification `R/Rf ≅ Kⁿ`). -/
theorem sub_ofVec_remVec_mem (f : OrePoly δ) (hf : f ≠ 0) (m : OrePoly δ) :
    m - ofVec δ (remVec δ f hf m) ∈ Ideal.span ({f} : Set (OrePoly δ)) := by
  rw [ofVec_remVec]
  have h := (rem_spec δ f hf m).1
  rw [show m - rem δ f hf m = (exists_leftDiv δ hf m).choose * f from
    sub_eq_of_eq_add h]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)

/-- Uniqueness of the remainder: if `m` already has degree `< deg f`, it is its own remainder. -/
theorem rem_eq_self (f : OrePoly δ) (hf : f ≠ 0) (m : OrePoly δ)
    (h : ∀ k, natDegree δ f ≤ k → coeff δ m k = 0) : rem δ f hf m = m := by
  have hq : m - rem δ f hf m = (exists_leftDiv δ hf m).choose * f :=
    sub_eq_of_eq_add (rem_spec δ f hf m).1
  generalize (exists_leftDiv δ hf m).choose = q at hq
  by_cases hq0 : q = 0
  · rw [hq0, zero_mul, sub_eq_zero] at hq
    exact hq.symm
  · exfalso
    have hqf : q * f ≠ 0 := mul_ne_zero_of_injective δ σ.injective hq0 hf
    have hdeg : natDegree δ f ≤ natDegree δ (q * f) := by
      rw [natDegree_mul δ σ.injective hq0 hf]; omega
    have hc : ∀ d, natDegree δ f ≤ d → coeff δ (q * f) d = 0 := fun d hd => by
      rw [← hq, coeff_sub, h d hd, coeff_rem_eq_zero δ f hf m hd, sub_zero]
    exact leadingCoeff_ne_zero δ hqf (by rw [← coeff_natDegree]; exact hc _ hdeg)

theorem remVec_of_coeff (f : OrePoly δ) (hf : f ≠ 0) (m : OrePoly δ)
    (h : ∀ k, natDegree δ f ≤ k → coeff δ m k = 0) :
    remVec δ f hf m = fun i : Fin (natDegree δ f) => coeff δ m i := by
  unfold remVec
  rw [rem_eq_self δ f hf m h]

/-- `1̄ = e₁` for `deg f ≥ 1` (paper, §2.1). -/
theorem remVec_one (f : OrePoly δ) (hf : f ≠ 0) (hn : 0 < natDegree δ f) :
    remVec δ f hf 1 = fun i : Fin (natDegree δ f) => if (i : ℕ) = 0 then (1 : U) else 0 := by
  rw [remVec_of_coeff δ f hf 1 fun k hk => by
    rw [one_def, coeff_monomial]; exact ite_eq_right_iff.2 fun h' => by omega]
  funext i
  rw [one_def, coeff_monomial]
  split_ifs <;> first | rfl | omega

/-- **Lemma 2.1**, usable form: if `g(T_f)(b̄) = m̄` then `m ≡ g b (mod Rf)`; this is the
direction of the paper's `g b ≡ c (mod Rf) ⇔ g(T_f)(b̄) = c̄` that Proposition 2.2 uses. -/
theorem sub_mul_mem_of_evalT_eq (f : OrePoly δ) (hf : leadingCoeff δ f = 1)
    (hn : 0 < natDegree δ f) (hf0 : f ≠ 0) (g m : OrePoly δ) (v : Fin (natDegree δ f) → U)
    (hv : evalT δ (companion δ f) g v = remVec δ f hf0 m) :
    m - g * ofVec δ v ∈ Ideal.span ({f} : Set (OrePoly δ)) := by
  have h1 := sub_ofVec_remVec_mem δ f hf0 m
  have h2 := mul_ofVec_sub_mem δ f hf hn g v
  rw [hv] at h2
  have : m - g * ofVec δ v
      = (m - ofVec δ (remVec δ f hf0 m)) - (g * ofVec δ v - ofVec δ (remVec δ f hf0 m)) := by
    abel
  rw [this]
  exact Ideal.sub_mem _ h1 h2

end LeftPCI.Counterexample.Adjoin
