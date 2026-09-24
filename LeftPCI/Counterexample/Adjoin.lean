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

/-- The pseudo-linear map `T(v) = σ(v) C + δ(v)` (paper, §2.1 `T_f`, and §4 `T`). -/
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

/-- `1̄ = e₁` for `deg f ≥ 1` (paper, Lemma 2.1, last statement). -/
theorem remVec_one (f : OrePoly δ) (hf : f ≠ 0) (hn : 0 < natDegree δ f) :
    remVec δ f hf 1 = fun i : Fin (natDegree δ f) => if (i : ℕ) = 0 then (1 : U) else 0 := by
  rw [remVec_of_coeff δ f hf 1 fun k hk => by
    rw [one_def, coeff_monomial]; exact ite_eq_right_iff.2 fun h' => by omega]
  funext i
  rw [one_def, coeff_monomial]
  split_ifs <;> first | rfl | omega

/-- **Lemma 2.1**, usable form: if `g(T_f)(b̄) = m̄` then `m ≡ g b (mod Rf)`; the case `m = 1`
is the paper's `g b ≡ 1 (mod Rf) ⇔ g(T_f)(b̄) = e₁`. -/
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

/-! ## Section 4: adjoining the solution of one equation -/

section Adjoining

variable {n : ℕ}

theorem T_add (C : Matrix (Fin n) (Fin n) U) (v w : Fin n → U) :
    T δ C (v + w) = T δ C v + T δ C w := by
  ext j
  simp only [T_apply, Pi.add_apply, OreDerivation.map_add]
  rw [show σ ∘ (v + w) = σ ∘ v + σ ∘ w by ext; simp, Matrix.add_vecMul]
  simp only [Pi.add_apply]
  abel

@[simp] theorem T_zero (C : Matrix (Fin n) (Fin n) U) : T δ C 0 = 0 := by
  ext j
  simp [T_apply, show σ ∘ (0 : Fin n → U) = 0 by ext; simp]

theorem T_sum (C : Matrix (Fin n) (Fin n) U) {ι : Type*} (s : Finset ι) (v : ι → Fin n → U) :
    T δ C (∑ i ∈ s, v i) = ∑ i ∈ s, T δ C (v i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, T_add, ih]

theorem OreDerivation_map_sum {ι : Type*} (s : Finset ι) (a : ι → U) :
    δ (∑ i ∈ s, a i) = ∑ i ∈ s, δ (a i) :=
  map_sum δ.toAddMonoidHom a s

/-- **Lemma 4.1**: if `σ(v) = v` then `T(vN) = v(σ(N)C + δ(N)) + δ(v)N`. -/
theorem T_vecMul (C : Matrix (Fin n) (Fin n) U) (v : Fin n → U) (hv : σ ∘ v = v)
    (N : Matrix (Fin n) (Fin n) U) :
    T δ C (Matrix.vecMul v N)
      = Matrix.vecMul v (N.map σ * C + N.map δ) + Matrix.vecMul (δ ∘ v) N := by
  -- `σ(vN) = σ(v)σ(N) = vσ(N)`
  have h1 : σ ∘ Matrix.vecMul v N = Matrix.vecMul v (N.map σ) := by
    ext j
    rw [Function.comp_apply, RingHom.map_vecMul, hv]
  -- `δ(vN) = σ(v)δ(N) + δ(v)N = vδ(N) + δ(v)N`, entrywise Leibniz
  have h2 : δ ∘ Matrix.vecMul v N = Matrix.vecMul v (N.map δ) + Matrix.vecMul (δ ∘ v) N := by
    ext j
    simp only [Function.comp_apply, Matrix.vecMul, dotProduct, Pi.add_apply, Matrix.map_apply,
      OreDerivation_map_sum, OreDerivation.leibniz, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show σ (v l) = v l from congrFun hv l]
  unfold T
  rw [h1, h2, Matrix.vecMul_vecMul, Matrix.vecMul_add, add_assoc]

/-- The matrices `N_{i,j}` of §4: `N_{0,0} = I`, `N_{0,j+1} = 0`, and
`N_{i+1,j} = σ(N_{i,j})C + δ(N_{i,j}) + N_{i,j-1}` (with `N_{i,-1} = 0`). -/
noncomputable def Nmat (C : Matrix (Fin n) (Fin n) U) : ℕ → ℕ → Matrix (Fin n) (Fin n) U
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | i + 1, 0 => (Nmat C i 0).map σ * C + (Nmat C i 0).map δ
  | i + 1, j + 1 => (Nmat C i (j + 1)).map σ * C + (Nmat C i (j + 1)).map δ + Nmat C i j

variable (C : Matrix (Fin n) (Fin n) U)

@[simp] theorem Nmat_zero_zero : Nmat δ C 0 0 = 1 := by rw [Nmat]
@[simp] theorem Nmat_zero_succ (j : ℕ) : Nmat δ C 0 (j + 1) = 0 := by rw [Nmat]
theorem Nmat_succ_zero (i : ℕ) :
    Nmat δ C (i + 1) 0 = (Nmat δ C i 0).map σ * C + (Nmat δ C i 0).map δ := by rw [Nmat]
theorem Nmat_succ_succ (i j : ℕ) :
    Nmat δ C (i + 1) (j + 1)
      = (Nmat δ C i (j + 1)).map σ * C + (Nmat δ C i (j + 1)).map δ + Nmat δ C i j := by
  rw [Nmat]

@[simp] theorem map_zero_σ : (0 : Matrix (Fin n) (Fin n) U).map σ = 0 :=
  Matrix.map_zero _ (map_zero σ)
@[simp] theorem map_zero_δ : (0 : Matrix (Fin n) (Fin n) U).map δ = 0 :=
  Matrix.map_zero _ δ.map_zero

/-- `N_{i,j} = 0` for `j > i` (§4, convention `N_{i,i+1} = 0`). -/
theorem Nmat_eq_zero_of_lt : ∀ {i j : ℕ}, i < j → Nmat δ C i j = 0
  | 0, j + 1, _ => Nmat_zero_succ δ C j
  | i + 1, j + 1, h => by
    rw [Nmat_succ_succ, Nmat_eq_zero_of_lt (by omega), Nmat_eq_zero_of_lt (by omega)]
    simp

/-- `N_{i,i} = I` (§4). -/
theorem Nmat_diag : ∀ i : ℕ, Nmat δ C i i = 1
  | 0 => Nmat_zero_zero δ C
  | i + 1 => by
    rw [Nmat_succ_succ, Nmat_eq_zero_of_lt δ C (Nat.lt_succ_self i), Nmat_diag i]
    simp

/-- **Lemma 4.2**: if `σ(x_j) = x_j` and `δ(x_j) = x_{j+1}` for `j < m`, then
`Tⁱ(x₀) = Σ_{j ≤ i} x_j N_{i,j}` for `i ≤ m`.  (Here `x_m` is part of the family `x`, and the
hypothesis `δ(x_{m-1}) = x_m` plays the role of the paper's definition `x_m := δ(x_{m-1})`.) -/
theorem iterate_T_eq_sum (x : ℕ → Fin n → U) (m : ℕ) (hσ : ∀ j < m, σ ∘ x j = x j)
    (hδ : ∀ j < m, δ ∘ x j = x (j + 1)) :
    ∀ i ≤ m, (T δ C)^[i] (x 0) = ∑ j ∈ Finset.range (i + 1), Matrix.vecMul (x j) (Nmat δ C i j) := by
  intro i hi
  induction i with
  | zero => simp [Matrix.vecMul_one]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega), T_sum]
    have step : ∀ j ∈ Finset.range (i + 1), T δ C (Matrix.vecMul (x j) (Nmat δ C i j))
        = Matrix.vecMul (x j) ((Nmat δ C i j).map σ * C + (Nmat δ C i j).map δ)
          + Matrix.vecMul (x (j + 1)) (Nmat δ C i j) := by
      intro j hj
      have hj : j < m := by simp at hj; omega
      rw [T_vecMul δ C (x j) (hσ j hj), hδ j hj]
    rw [Finset.sum_congr rfl step, Finset.sum_add_distrib]
    have hA : ∑ j ∈ Finset.range (i + 1),
          Matrix.vecMul (x j) ((Nmat δ C i j).map σ * C + (Nmat δ C i j).map δ)
        = ∑ j ∈ Finset.range (i + 1 + 1),
          Matrix.vecMul (x j) ((Nmat δ C i j).map σ * C + (Nmat δ C i j).map δ) := by
      rw [Finset.sum_range_succ _ (i + 1), Nmat_eq_zero_of_lt δ C (Nat.lt_succ_self i)]
      simp
    rw [hA, Finset.sum_range_succ' _ (i + 1),
      Finset.sum_range_succ' (fun j => Matrix.vecMul (x j) (Nmat δ C (i + 1) j)) (i + 1)]
    simp only [Nmat_succ_succ, Nmat_succ_zero, Matrix.vecMul_add, Finset.sum_add_distrib]
    abel

/-- The paper's `Φ = Σ_{i ≤ m} gᵢ Σ_{j ≤ min(i, m-1)} x_j N_{i,j}` (Proposition 4.3). -/
noncomputable def Phi (g : OrePoly δ) (x : ℕ → Fin n → U) : Fin n → U :=
  ∑ i ∈ Finset.range (natDegree δ g + 1), coeff δ g i •
    ∑ j ∈ Finset.range (min i (natDegree δ g - 1) + 1), Matrix.vecMul (x j) (Nmat δ C i j)

/-- The paper's `ζ = g_m⁻¹ (e - Φ)` (Proposition 4.3, with `e₁` generalized to `e`). -/
noncomputable def zeta (g : OrePoly δ) (x : ℕ → Fin n → U) (e : Fin n → U) : Fin n → U :=
  (leadingCoeff δ g)⁻¹ • (e - Phi δ C g x)

/-- `Φ` only reads `x_j` for `j ≤ m - 1` (so `ζ` is defined before `x_m`, Proposition 4.3). -/
theorem Phi_congr (g : OrePoly δ) (hg : 0 < natDegree δ g) {x x' : ℕ → Fin n → U}
    (h : ∀ j < natDegree δ g, x j = x' j) : Phi δ C g x = Phi δ C g x' := by
  unfold Phi
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [h j (by simp at hj; omega)]

theorem zeta_congr (g : OrePoly δ) (hg : 0 < natDegree δ g) {x x' : ℕ → Fin n → U}
    (h : ∀ j < natDegree δ g, x j = x' j) (e : Fin n → U) :
    zeta δ C g x e = zeta δ C g x' e := by
  unfold zeta
  rw [Phi_congr δ C g hg h]

/-- **Proposition 4.3** (algebraic core): if `x₀, …, x_{m-1}` are `σ`-fixed with
`δ(x_j) = x_{j+1}`, and `x_m = δ(x_{m-1})` equals `ζ = g_m⁻¹(e - Φ)`, then `g(T)(x₀) = e`. -/
theorem evalT_eq (g : OrePoly δ) (hg : 0 < natDegree δ g) (x : ℕ → Fin n → U) (e : Fin n → U)
    (hσ : ∀ j < natDegree δ g, σ ∘ x j = x j)
    (hδ : ∀ j < natDegree δ g, δ ∘ x j = x (j + 1))
    (hζ : x (natDegree δ g) = zeta δ C g x e) :
    evalT δ C g (x 0) = e := by
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have hlc : coeff δ g (natDegree δ g) ≠ 0 := by
    rw [coeff_natDegree]; exact leadingCoeff_ne_zero δ hg0
  -- by Lemma 4.2, `g(T)(x₀) = Σ_{i ≤ m} gᵢ Σ_{j ≤ i} x_j N_{i,j}`
  have h1 : ∀ i ∈ Finset.range (natDegree δ g + 1), coeff δ g i • (T δ C)^[i] (x 0)
      = coeff δ g i • ∑ j ∈ Finset.range (i + 1), Matrix.vecMul (x j) (Nmat δ C i j) := by
    intro i hi
    rw [iterate_T_eq_sum δ C x (natDegree δ g) hσ hδ i (by simp at hi; omega)]
  -- the terms with `j ≤ m - 1` make up `Φ`
  have hPhi : Phi δ C g x
      = ∑ i ∈ Finset.range (natDegree δ g), coeff δ g i •
          ∑ j ∈ Finset.range (i + 1), Matrix.vecMul (x j) (Nmat δ C i j)
        + coeff δ g (natDegree δ g) •
          ∑ j ∈ Finset.range (natDegree δ g), Matrix.vecMul (x j) (Nmat δ C (natDegree δ g) j) := by
    unfold Phi
    rw [Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [min_eq_left (by simp at hi; omega)]
    · rw [min_eq_right (by omega), Nat.sub_add_cancel hg]
  unfold evalT
  rw [Finset.sum_congr rfl h1, Finset.sum_range_succ, Finset.sum_range_succ (fun j => _), Nmat_diag,
    Matrix.vecMul_one, hζ, zeta, coeff_natDegree, smul_add, smul_smul,
    mul_inv_cancel₀ (leadingCoeff_ne_zero δ hg0), one_smul]
  rw [coeff_natDegree] at hPhi
  rw [hPhi]
  abel

/-! ### `N_{i,j}` depends only on `C` and on `σ, δ` restricted to the entries' subfield (§4) -/

theorem step_mem (L : Subfield U) (hC : ∀ i j, C i j ∈ L) (hL : ∀ u ∈ L, σ u ∈ L ∧ δ u ∈ L)
    {M : Matrix (Fin n) (Fin n) U} (hM : ∀ a b, M a b ∈ L) (a b : Fin n) :
    (M.map σ * C + M.map δ) a b ∈ L := by
  rw [Matrix.add_apply, Matrix.mul_apply]
  refine L.add_mem (L.sum_mem fun l _ => L.mul_mem ?_ (hC l b)) ?_
  · exact (hL _ (hM a l)).1
  · exact (hL _ (hM a b)).2

/-- All entries of `N_{i,j}` lie in any subfield `L` containing the entries of `C` and stable
under `σ, δ` (§4: the `N_{i,j}` are matrices over `K`). -/
theorem Nmat_mem (L : Subfield U) (hC : ∀ i j, C i j ∈ L) (hL : ∀ u ∈ L, σ u ∈ L ∧ δ u ∈ L) :
    ∀ i j a b, Nmat δ C i j a b ∈ L
  | 0, 0, a, b => by
    rw [Nmat_zero_zero, Matrix.one_apply]
    split_ifs
    · exact L.one_mem
    · exact L.zero_mem
  | 0, j + 1, a, b => by rw [Nmat_zero_succ]; exact L.zero_mem
  | i + 1, 0, a, b => by
    rw [Nmat_succ_zero]
    exact step_mem δ C L hC hL (Nmat_mem L hC hL i 0) a b
  | i + 1, j + 1, a, b => by
    rw [Nmat_succ_succ, Matrix.add_apply]
    exact L.add_mem (step_mem δ C L hC hL (Nmat_mem L hC hL i (j + 1)) a b)
      (Nmat_mem L hC hL i j a b)

/-- The remark after the definition of `N_{i,j}` (§4): `N_{i,j}` depends only on `C` and on
`σ, δ` restricted to a subfield `L` containing the entries of `C` and stable under `σ, δ`. -/
theorem Nmat_congr {σ' : U →+* U} (δ' : OreDerivation U σ') (L : Subfield U)
    (hC : ∀ i j, C i j ∈ L) (hL : ∀ u ∈ L, σ u ∈ L ∧ δ u ∈ L)
    (hagree : ∀ u ∈ L, σ u = σ' u ∧ δ u = δ' u) : ∀ i j, Nmat δ C i j = Nmat δ' C i j := by
  have hmap : ∀ i j, (Nmat δ C i j).map σ = (Nmat δ C i j).map σ' ∧
      (Nmat δ C i j).map δ = (Nmat δ C i j).map δ' := fun i j =>
    ⟨Matrix.ext fun a b => (hagree _ (Nmat_mem δ C L hC hL i j a b)).1,
      Matrix.ext fun a b => (hagree _ (Nmat_mem δ C L hC hL i j a b)).2⟩
  intro i
  induction i with
  | zero => intro j; cases j <;> simp
  | succ i ih =>
    intro j
    cases j with
    | zero => rw [Nmat_succ_zero, Nmat_succ_zero, (hmap i 0).1, (hmap i 0).2, ih 0]
    | succ j =>
      rw [Nmat_succ_succ, Nmat_succ_succ, (hmap i (j + 1)).1, (hmap i (j + 1)).2, ih (j + 1), ih j]

end Adjoining

/-- The entries of the companion matrix `C_f` lie in any subfield containing the coefficients
of `f` (§2.1, §4: `C_f ∈ M_n(K)`). -/
theorem companion_mem (f : OrePoly δ) (L : Subfield U) (hf : ∀ i, coeff δ f i ∈ L) :
    ∀ i j, companion δ f i j ∈ L := by
  intro i j
  rw [companion_apply]
  split_ifs
  · exact L.one_mem
  · exact L.zero_mem
  · exact L.neg_mem (hf j)

end LeftPCI.Counterexample.Adjoin
