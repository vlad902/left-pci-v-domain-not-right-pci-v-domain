module

public import LeftPCI.FreeField.FullCalculus
public import LeftPCI.FreeField.UniversalLocalization
public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-! # Cramer's rule in `FullLoc R`; every element is `0` or a unit

Let `λ : R → FullLoc R` be the universal localization of `R` at all full matrices (`FullLoc`,
defined here as an abbreviation of `UnivLoc.Loc`).  A **display** is `(A, u, x, a)` with `A` a
square matrix, `u` a column, `x` a row and `a ∈ R`; its **value** is
`dispVal A u x a = λa − λx · (λA)⁻¹ · λu` (Cohn, *FIR* §7.4 p. 437), with `⁻¹` read as
`Ring.inverse` in the (non-commutative) matrix ring.

* **Cramer's rule** (`exists_dispVal`; FIR Thm 7.1.2 p. 412–413, SF Thm 4.2.1 p. 158): under
  `FullClosed R`, every element of `FullLoc R` is the value of a display with full `A`.  The
  display values contain `λ(R)` and the entries of the `invMat`s and are closed under `+`, `·`
  (`dispVal_add`, `dispVal_mul`: FIR p. 438 formulas (2), (3)), so `UnivLoc.induction` applies.
* **Dichotomy** (FIR Prop 7.5.9(i) pp. 447–448, SF Lemma 4.5.2 p. 178): if the display matrix
  `[[A, u], [x, a]]` is not full its value is `0` (`dispVal_eq_zero_of_not_isFullG`); if it is
  full the value is a unit (`isUnit_dispVal_of_isFullG`, via the noncommutative Schur complement
  `isUnit_schur`).  Hence `isUnit_or_eq_zero`.

Only `Ring.inverse` / `IsUnit` in `Matrix ι ι S` are used — no `det`, matrix `⁻¹`, transposes, or
Mathlib's (commutative) Schur-complement API.
-/

namespace LeftPCI.FreeField

open Matrix

universe u

/-! ## Block-inverse algebra over an arbitrary ring -/

section Generic

variable {S : Type*} [Ring S]

/-- A two-sided inverse is `Ring.inverse`. -/
theorem ring_inverse_eq_of_mul_eq_one {M : Type*} [MonoidWithZero M] {a b : M} (h₁ : a * b = 1)
    (h₂ : b * a = 1) : Ring.inverse a = b := by
  have := Ring.inverse_unit (⟨a, b, h₁, h₂⟩ : Mˣ)
  simpa using this

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem fromBlocks_upper_mul_inv {A : Matrix ι ι S} {B : Matrix κ κ S} (hA : IsUnit A)
    (hB : IsUnit B) (C : Matrix ι κ S) :
    fromBlocks A C 0 B *
        fromBlocks (Ring.inverse A) (-(Ring.inverse A * C * Ring.inverse B)) 0 (Ring.inverse B) = 1 ∧
      fromBlocks (Ring.inverse A) (-(Ring.inverse A * C * Ring.inverse B)) 0 (Ring.inverse B) *
        fromBlocks A C 0 B = 1 := by
  constructor
  · rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1 <;> simp [← Matrix.mul_assoc, Ring.mul_inverse_cancel _ hA, Ring.mul_inverse_cancel _ hB]
  · rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1 <;> simp [Matrix.mul_assoc, Ring.inverse_mul_cancel _ hA, Ring.inverse_mul_cancel _ hB]

/-- Inverse of an upper block-triangular matrix with invertible diagonal blocks:
`[[A, C], [0, B]]⁻¹ = [[A⁻¹, −A⁻¹CB⁻¹], [0, B⁻¹]]`. -/
theorem inverse_fromBlocks_upper {A : Matrix ι ι S} {B : Matrix κ κ S} (hA : IsUnit A)
    (hB : IsUnit B) (C : Matrix ι κ S) :
    Ring.inverse (fromBlocks A C 0 B) =
      fromBlocks (Ring.inverse A) (-(Ring.inverse A * C * Ring.inverse B)) 0 (Ring.inverse B) :=
  ring_inverse_eq_of_mul_eq_one (fromBlocks_upper_mul_inv hA hB C).1
    (fromBlocks_upper_mul_inv hA hB C).2

theorem isUnit_fromBlocks_upper {A : Matrix ι ι S} {B : Matrix κ κ S} (hA : IsUnit A)
    (hB : IsUnit B) (C : Matrix ι κ S) : IsUnit (fromBlocks A C 0 B) :=
  ⟨⟨fromBlocks A C 0 B, _, (fromBlocks_upper_mul_inv hA hB C).1,
    (fromBlocks_upper_mul_inv hA hB C).2⟩, rfl⟩

theorem isUnit_fromBlocks_one_zero_one (X : Matrix κ ι S) :
    IsUnit (fromBlocks (1 : Matrix ι ι S) 0 X (1 : Matrix κ κ S)) := by
  refine ⟨⟨fromBlocks 1 0 X 1, fromBlocks 1 0 (-X) 1, ?_, ?_⟩, rfl⟩ <;>
    simp [fromBlocks_multiply]

/-- If a block-diagonal matrix is a unit, so is its lower-right block. -/
theorem isUnit_of_isUnit_fromBlocks_diag {A : Matrix ι ι S} {D : Matrix κ κ S}
    (h : IsUnit (fromBlocks A 0 0 D)) : IsUnit D := by
  obtain ⟨w, hw⟩ := h
  have h₁ := w.mul_inv
  have h₂ := w.inv_mul
  rw [hw, ← fromBlocks_toBlocks (↑w⁻¹ : Matrix (ι ⊕ κ) (ι ⊕ κ) S), fromBlocks_multiply,
    ← fromBlocks_one, fromBlocks_inj] at h₁ h₂
  exact ⟨⟨D, _, by simpa using h₁.2.2.2, by simpa using h₂.2.2.2⟩, rfl⟩

/-- **Noncommutative Schur complement.**  If `A` and `[[A, B], [C, D]]` are invertible, so is
`D − C A⁻¹ B` (`⁻¹` = `Ring.inverse`).  Stated for an arbitrary lower-right index type `κ`
(the plan's `κ = Unit` is a special case). -/
theorem isUnit_schur {A : Matrix ι ι S} {B : Matrix ι κ S} {C : Matrix κ ι S}
    {D : Matrix κ κ S} (hA : IsUnit A) (hM : IsUnit (fromBlocks A B C D)) :
    IsUnit (D - C * Ring.inverse A * B) := by
  set s := D - C * Ring.inverse A * B
  have hL := isUnit_fromBlocks_one_zero_one (ι := ι) (κ := κ) (C * Ring.inverse A)
  have hU := isUnit_fromBlocks_upper (isUnit_one (M := Matrix ι ι S)) (isUnit_one (M := Matrix κ κ S))
    (Ring.inverse A * B)
  have hfac : fromBlocks A B C D =
      fromBlocks 1 0 (C * Ring.inverse A) 1 * fromBlocks A 0 0 s *
        fromBlocks 1 (Ring.inverse A * B) 0 1 := by
    simp only [fromBlocks_multiply, s]
    congr 1
    · simp
    · simp [← Matrix.mul_assoc, Ring.mul_inverse_cancel _ hA]
    · simp [Matrix.mul_assoc, Ring.inverse_mul_cancel _ hA]
    · simp only [Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
      rw [Matrix.mul_assoc C (Ring.inverse A) A, Ring.inverse_mul_cancel _ hA, Matrix.mul_one,
        ← Matrix.mul_assoc]
      abel
  rw [hfac] at hM
  apply isUnit_of_isUnit_fromBlocks_diag (A := A)
  rw [← hU.unit_spec, Units.isUnit_mul_units, ← hL.unit_spec, Units.isUnit_units_mul] at hM
  exact hM

/-- A `Unit × Unit` matrix that is a unit has a unit entry. -/
theorem isUnit_apply_of_isUnit {M : Matrix Unit Unit S} (h : IsUnit M) : IsUnit (M () ()) := by
  obtain ⟨w, rfl⟩ := h
  refine ⟨⟨(w : Matrix Unit Unit S) () (), (↑w⁻¹ : Matrix Unit Unit S) () (), ?_, ?_⟩, rfl⟩
  · simpa [mul_apply] using congrFun (congrFun w.mul_inv ()) ()
  · simpa [mul_apply] using congrFun (congrFun w.inv_mul ()) ()

/-- The value `a − x · A⁻¹ · u` of a display over an arbitrary ring. -/
noncomputable def dval (A : Matrix ι ι S) (u x : ι → S) (a : S) : S :=
  a - x ⬝ᵥ (Ring.inverse A *ᵥ u)

theorem dval_add {A : Matrix ι ι S} {B : Matrix κ κ S} (hA : IsUnit A) (hB : IsUnit B)
    (u x : ι → S) (v y : κ → S) (a b : S) :
    dval (fromBlocks A 0 0 B) (Sum.elim u v) (Sum.elim x y) (a + b) = dval A u x a + dval B v y b := by
  have := inverse_fromBlocks_upper hA hB 0
  simp only [Matrix.mul_zero, Matrix.zero_mul, neg_zero] at this
  simp only [dval, this, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec,
    add_zero, zero_add, sumElim_dotProduct_sumElim]
  abel

omit [DecidableEq ι] in
theorem dotProduct_mulVec_mul_right (x : ι → S) (M : Matrix ι ι S) (u : ι → S) (b : S) :
    x ⬝ᵥ (M *ᵥ fun i => u i * b) = (x ⬝ᵥ (M *ᵥ u)) * b := by
  simp [dotProduct, mulVec, Finset.sum_mul, mul_assoc]

omit [DecidableEq κ] in
theorem mul_left_dotProduct (a : S) (y w : κ → S) : (fun j => a * y j) ⬝ᵥ w = a * (y ⬝ᵥ w) := by
  simp [dotProduct, Finset.mul_sum, mul_assoc]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem vecMulVec_mulVec' (u : ι → S) (y w : κ → S) :
    vecMulVec u y *ᵥ w = fun i => u i * (y ⬝ᵥ w) := by
  ext i
  simp [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_assoc]

theorem dval_mul {A : Matrix ι ι S} {B : Matrix κ κ S} (hA : IsUnit A) (hB : IsUnit B)
    (u x : ι → S) (v y : κ → S) (a b : S) :
    dval (fromBlocks A (vecMulVec u y) 0 B) (Sum.elim (fun i => u i * b) v)
      (Sum.elim x (fun j => a * y j)) (a * b) = dval A u x a * dval B v y b := by
  simp only [dval, inverse_fromBlocks_upper hA hB, fromBlocks_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, zero_mulVec, zero_add, sumElim_dotProduct_sumElim, dotProduct_add,
    neg_mulVec, dotProduct_neg, ← mulVec_mulVec, vecMulVec_mulVec', dotProduct_mulVec_mul_right,
    mul_left_dotProduct]
  noncomm_ring

theorem inverse_mul_of_isUnit {P Q : Matrix ι ι S} (hP : IsUnit P) (hQ : IsUnit Q) :
    Ring.inverse (P * Q) = Ring.inverse Q * Ring.inverse P := by
  apply ring_inverse_eq_of_mul_eq_one
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, Ring.mul_inverse_cancel _ hQ, Matrix.one_mul,
      Ring.mul_inverse_cancel _ hP]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Ring.inverse P), Ring.inverse_mul_cancel _ hP,
      Matrix.one_mul, Ring.inverse_mul_cancel _ hQ]

/-- A display whose matrix factors through its denominator size has value `0`. -/
theorem dval_factor {P Q : Matrix ι ι S} (hP : IsUnit P) (hQ : IsUnit Q) (p q : ι → S) :
    dval (P * Q) (P *ᵥ q) (p ᵥ* Q) (p ⬝ᵥ q) = 0 := by
  rw [dval, inverse_mul_of_isUnit hP hQ, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
    ← Matrix.mul_assoc Q, Ring.mul_inverse_cancel _ hQ, Matrix.one_mul,
    Ring.inverse_mul_cancel _ hP, one_mulVec, sub_self]

omit [DecidableEq ι] in
theorem replicateRow_mul_mul_replicateCol_apply (x : ι → S) (M : Matrix ι ι S) (u : ι → S) :
    (replicateRow Unit x * M * replicateCol Unit u) () () = x ⬝ᵥ (M *ᵥ u) := by
  rw [Matrix.mul_assoc]
  simp [mul_apply, dotProduct, mulVec]

/-- If `A` and the display matrix `[[A, u], [x, a]]` are invertible, the value is a unit. -/
theorem isUnit_dval {A : Matrix ι ι S} {u x : ι → S} {a : S} (hA : IsUnit A)
    (h : IsUnit (fromBlocks A (replicateCol Unit u) (replicateRow Unit x) (of fun _ _ => a))) :
    IsUnit (dval A u x a) := by
  have := isUnit_apply_of_isUnit (isUnit_schur hA h)
  simpa [dval, replicateRow_mul_mul_replicateCol_apply] using this

end Generic

/-! ## The localization at all full matrices -/

/-- The universal localization of `R` at **all** full matrices (Cohn's `R_Φ`). -/
abbrev FullLoc (R : Type u) [Ring R] :=
  UnivLoc.Loc (fun n (A : Matrix (Fin n) (Fin n) R) => IsFull A)

/-- The canonical map `R → FullLoc R` (`= UnivLoc.toLoc _`). -/
noncomputable abbrev toFullLoc (R : Type u) [Ring R] : R →+* FullLoc R := UnivLoc.toLoc _

theorem toFullLoc_def (R : Type u) [Ring R] :
    toFullLoc R = (UnivLoc.toLoc _ : R →+* FullLoc R) := rfl

variable {R : Type u} [Ring R]

/-- `toLoc` inverts every `IsFullG` matrix, over any finite index type. -/
theorem isUnit_map_toLoc_of_isFullG {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι R} (hA : IsFullG A) : IsUnit (A.map (toFullLoc R)) := by
  let e := Fintype.equivFin ι
  have hA' : IsFull (reindex e e A) := (isFullG_iff_isFull _).1 ((isFullG_reindex_iff e A).2 hA)
  have h := (UnivLoc.isUnit_map_toLoc hA').map (reindexRingEquiv (FullLoc R) e.symm)
  convert h using 1
  ext i j
  simp [reindexRingEquiv, reindex_apply]

section Display

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The value `λa − λx · (λA)⁻¹ · λu ∈ FullLoc R` of the display `[[A, u], [x, a]]`. -/
noncomputable def dispVal (A : Matrix ι ι R) (u x : ι → R) (a : R) : FullLoc R :=
  dval (A.map (toFullLoc R)) (toFullLoc R ∘ u) (toFullLoc R ∘ x) (toFullLoc R a)

/-- The plan's formula: the `(Unit, Unit)` entry of `λa − (λx)(λA)⁻¹(λu)`. -/
theorem dispVal_eq (A : Matrix ι ι R) (u x : ι → R) (a : R) :
    dispVal A u x a = toFullLoc R a - ((replicateRow Unit x).map (toFullLoc R) *
      Ring.inverse (A.map (toFullLoc R)) * (replicateCol Unit u).map (toFullLoc R)) () () := by
  rw [dispVal, dval, ← replicateRow_mul_mul_replicateCol_apply]
  rfl

/-- Closure of display values under `+` (FIR p. 438 (2)). -/
theorem dispVal_add {A : Matrix ι ι R} {B : Matrix κ κ R} (hA : IsFullG A) (hB : IsFullG B)
    (u x : ι → R) (v y : κ → R) (a b : R) :
    dispVal (fromBlocks A 0 0 B) (Sum.elim u v) (Sum.elim x y) (a + b) =
      dispVal A u x a + dispVal B v y b := by
  have h := dval_add (isUnit_map_toLoc_of_isFullG hA) (isUnit_map_toLoc_of_isFullG hB)
    (toFullLoc R ∘ u) (toFullLoc R ∘ x) (toFullLoc R ∘ v) (toFullLoc R ∘ y)
    (toFullLoc R a) (toFullLoc R b)
  unfold dispVal
  rw [fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _),
    Sum.comp_elim, Sum.comp_elim, map_add]
  exact h

/-- Closure of display values under `·` (FIR p. 438 (3)). -/
theorem dispVal_mul {A : Matrix ι ι R} {B : Matrix κ κ R} (hA : IsFullG A) (hB : IsFullG B)
    (u x : ι → R) (v y : κ → R) (a b : R) :
    dispVal (fromBlocks A (vecMulVec u y) 0 B) (Sum.elim (fun i => u i * b) v)
      (Sum.elim x (fun j => a * y j)) (a * b) = dispVal A u x a * dispVal B v y b := by
  have h := dval_mul (isUnit_map_toLoc_of_isFullG hA) (isUnit_map_toLoc_of_isFullG hB)
    (toFullLoc R ∘ u) (toFullLoc R ∘ x) (toFullLoc R ∘ v) (toFullLoc R ∘ y)
    (toFullLoc R a) (toFullLoc R b)
  unfold dispVal
  rw [fromBlocks_map, Matrix.map_zero _ (map_zero _), Sum.comp_elim, Sum.comp_elim, map_mul]
  convert h using 3
  · ext i j; simp [vecMulVec_apply]
  · funext i; simp
  · funext i; simp

theorem dispVal_of_isEmpty [IsEmpty ι] (A : Matrix ι ι R) (u x : ι → R) (a : R) :
    dispVal A u x a = toFullLoc R a := by
  simp [dispVal, dval, dotProduct]

theorem dispVal_single {n : ℕ} {A : Matrix (Fin n) (Fin n) R} (hA : IsFull A) (i j : Fin n) :
    dispVal A (-Pi.single j 1) (Pi.single i 1) 0 = UnivLoc.invMat _ A hA i j := by
  have h₁ : ∀ k : Fin n, (toFullLoc R ∘ Pi.single k (1 : R)) = Pi.single k 1 := by
    intro k; funext l; by_cases h : l = k <;> simp [h]
  have h₂ : (toFullLoc R ∘ (-Pi.single j (1 : R))) = -Pi.single j 1 := by
    rw [← h₁ j]; funext l; simp
  rw [dispVal, dval, h₁, h₂, UnivLoc.invMat_eq_inverse]
  simp [mulVec_neg]

/-- **Cramer's rule** (FIR Thm 7.1.2 p. 412; SF Thm 4.2.1 p. 158): every element of `FullLoc R`
is the value of a display with full denominator. -/
theorem exists_dispVal [FullClosed R] (p : FullLoc R) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (A : Matrix ι ι R) (u x : ι → R) (a : R),
      IsFullG A ∧ p = dispVal A u x a := by
  induction p using UnivLoc.induction with
  | h_of r =>
    exact ⟨Fin 0, inferInstance, inferInstance, 0, 0, 0, r, isFullG_of_isEmpty _,
      (dispVal_of_isEmpty _ _ _ _).symm⟩
  | h_inv n A hA i j =>
    exact ⟨Fin n, inferInstance, inferInstance, A, -Pi.single j 1, Pi.single i 1, 0,
      (isFullG_iff_isFull A).2 hA, (dispVal_single hA i j).symm⟩
  | h_add p q hp hq =>
    obtain ⟨ι, _, _, A, u, x, a, hA, rfl⟩ := hp
    obtain ⟨κ, _, _, B, v, y, b, hB, rfl⟩ := hq
    exact ⟨ι ⊕ κ, inferInstance, inferInstance, _, _, _, _, hA.fromBlocks_diag hB,
      (dispVal_add hA hB u x v y a b).symm⟩
  | h_mul p q hp hq =>
    obtain ⟨ι, _, _, A, u, x, a, hA, rfl⟩ := hp
    obtain ⟨κ, _, _, B, v, y, b, hB, rfl⟩ := hq
    exact ⟨ι ⊕ κ, inferInstance, inferInstance, _, _, _, _, isFullG_fromBlocks_upper hA hB _,
      (dispVal_mul hA hB u x v y a b).symm⟩

/-- A display whose matrix `[[A, u], [x, a]]` is not full has value `0` (FIR Prop 7.5.9(i)). -/
theorem dispVal_eq_zero_of_not_isFullG {A : Matrix ι ι R} {u x : ι → R} {a : R}
    (hA : IsFullG A)
    (h : ¬ IsFullG (fromBlocks A (replicateCol Unit u) (replicateRow Unit x) (of fun _ _ => a))) :
    dispVal A u x a = 0 := by
  rw [not_isFullG_iff _ (by simp)] at h
  obtain ⟨P, Q, hPQ⟩ := (factorsThrough_iff_exists (k := ι) (by simp)).1 h
  set P₁ : Matrix ι ι R := P.submatrix Sum.inl id
  set Q₁ : Matrix ι ι R := Q.submatrix id Sum.inl
  set p : ι → R := P (Sum.inr ())
  set q : ι → R := fun k => Q k (Sum.inr ())
  have e := fun i j => congrFun (congrFun hPQ i) j
  have hA' : A = P₁ * Q₁ := by
    ext i j; simpa [mul_apply, P₁, Q₁] using (e (Sum.inl i) (Sum.inl j)).symm
  have hu : u = P₁ *ᵥ q := by
    ext i; simpa [mul_apply, mulVec, dotProduct, P₁, q] using (e (Sum.inl i) (Sum.inr ())).symm
  have hx : x = p ᵥ* Q₁ := by
    ext j; simpa [mul_apply, vecMul, dotProduct, Q₁, p] using (e (Sum.inr ()) (Sum.inl j)).symm
  have ha : a = p ⬝ᵥ q := by
    simpa [mul_apply, dotProduct, p, q] using (e (Sum.inr ()) (Sum.inr ())).symm
  rw [hA'] at hA
  have hP := isUnit_map_toLoc_of_isFullG (isFullG_left_of_mul hA)
  have hQ := isUnit_map_toLoc_of_isFullG (isFullG_right_of_mul hA)
  have := dval_factor hP hQ (toFullLoc R ∘ p) (toFullLoc R ∘ q)
  unfold dispVal
  rw [hA', hu, hx, ha, Matrix.map_mul, RingHom.map_dotProduct]
  convert this using 2
  · funext i; exact RingHom.map_mulVec _ _ _ i
  · funext j; exact RingHom.map_vecMul _ _ _ j

/-- A display whose matrix `[[A, u], [x, a]]` is full has invertible value (FIR Prop 7.5.9(i),
via the Schur complement). -/
theorem isUnit_dispVal_of_isFullG {A : Matrix ι ι R} {u x : ι → R} {a : R} (hA : IsFullG A)
    (h : IsFullG (fromBlocks A (replicateCol Unit u) (replicateRow Unit x) (of fun _ _ => a))) :
    IsUnit (dispVal A u x a) := by
  have hN := isUnit_map_toLoc_of_isFullG h
  refine isUnit_dval (isUnit_map_toLoc_of_isFullG hA) ?_
  convert hN using 1
  rw [fromBlocks_map]
  congr 1

/-- **Every element of `FullLoc R` is `0` or a unit** (FIR Prop 7.5.9(i); SF Lemma 4.5.2). -/
theorem isUnit_or_eq_zero [FullClosed R] (p : FullLoc R) : IsUnit p ∨ p = 0 := by
  obtain ⟨ι, _, _, A, u, x, a, hA, rfl⟩ := exists_dispVal p
  by_cases h : IsFullG (fromBlocks A (replicateCol Unit u) (replicateRow Unit x) (of fun _ _ => a))
  · exact Or.inl (isUnit_dispVal_of_isFullG hA h)
  · exact Or.inr (dispVal_eq_zero_of_not_isFullG hA h)

end Display

end LeftPCI.FreeField
