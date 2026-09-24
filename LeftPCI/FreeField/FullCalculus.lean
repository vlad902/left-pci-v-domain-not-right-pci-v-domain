module

public import LeftPCI.FreeField.Full
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Reindex

@[expose] public section

/-! # Full-matrix calculus over an arbitrary ring

Index-general fullness (`IsFullG`, for square matrices over an arbitrary finite index type) with
`FactorsThrough` ("inner rank `≤ r`") as the primitive: every non-fullness proof is "exhibit a
factorization".  Everything in the first half holds over an arbitrary (non-commutative) ring.

The class `FullClosed R` is Cohn's condition (FC) (*Free Ideal Rings* Thm 7.5.13 (b)/(c),
p. 450): `R ≠ 0` and full matrices are closed under products and diagonal sums.  It holds for
every Sylvester domain, in particular every semifir (proved in `Sylvester.lean`).  From it we
derive: identity and invertible matrices are full, block-triangular matrices with full diagonal
blocks are full, and the two block-triangular `iff`s used by the display invariant.

Sources: Cohn, *Free Ideal Rings and Localization in General Rings* §5.4 pp. 281–288, §7.5;
Cohn, *Skew Fields* §4.5.  No `CommRing`-only API (`det`, `⁻¹` on matrices, transposes) is used.
-/

namespace LeftPCI.FreeField

open Matrix

universe u

variable {R : Type u} [Ring R]

/-! ## `FactorsThrough` -/

/-- `M` factors through `Rʳ` (inner rank `≤ r`). -/
def FactorsThrough {m n : Type*} (M : Matrix m n R) (r : ℕ) : Prop :=
  ∃ (P : Matrix m (Fin r) R) (Q : Matrix (Fin r) n R), P * Q = M

section FactorsThrough

variable {l m n o m' n' : Type*}

/-- A product through any finite type `k` factors through `card k`. -/
theorem factorsThrough_mul {k : Type*} [Fintype k] (P : Matrix m k R) (Q : Matrix k n R) :
    FactorsThrough (P * Q) (Fintype.card k) := by
  classical
  let e := Fintype.equivFin k
  refine ⟨P.submatrix id e.symm, Q.submatrix e.symm id, ?_⟩
  rw [submatrix_mul_equiv, submatrix_id_id]

theorem FactorsThrough.mono {M : Matrix m n R} {r s : ℕ} (h : FactorsThrough M r)
    (hrs : r ≤ s) : FactorsThrough M s := by
  obtain ⟨P, Q, rfl⟩ := h
  have := factorsThrough_mul (Matrix.fromCols P (0 : Matrix m (Fin (s - r)) R))
    (Matrix.fromRows Q (0 : Matrix (Fin (s - r)) n R))
  rwa [Matrix.fromCols_mul_fromRows, Matrix.mul_zero, add_zero, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_fin, Nat.add_sub_cancel' hrs] at this

theorem FactorsThrough.mul_left [Fintype m] {M : Matrix m n R} {r : ℕ} (h : FactorsThrough M r)
    (L : Matrix l m R) : FactorsThrough (L * M) r := by
  obtain ⟨P, Q, rfl⟩ := h
  exact ⟨L * P, Q, by rw [Matrix.mul_assoc]⟩

theorem FactorsThrough.mul_right [Fintype n] {M : Matrix m n R} {r : ℕ} (h : FactorsThrough M r)
    (N : Matrix n o R) : FactorsThrough (M * N) r := by
  obtain ⟨P, Q, rfl⟩ := h
  exact ⟨P, Q * N, by rw [Matrix.mul_assoc]⟩

/-- Restricting (or repeating) rows and columns preserves a factorization. -/
theorem FactorsThrough.submatrix {M : Matrix m n R} {r : ℕ} (h : FactorsThrough M r)
    (f : m' → m) (g : n' → n) : FactorsThrough (M.submatrix f g) r := by
  obtain ⟨P, Q, rfl⟩ := h
  exact ⟨P.submatrix f id, Q.submatrix id g, by ext i j; simp [mul_apply]⟩

theorem factorsThrough_reindex (e₁ : m ≃ m') (e₂ : n ≃ n') {M : Matrix m n R} {r : ℕ} :
    FactorsThrough (reindex e₁ e₂ M) r ↔ FactorsThrough M r := by
  refine ⟨fun h => ?_, fun h => h.submatrix _ _⟩
  simpa [reindex_apply] using h.submatrix e₁ e₂

theorem factorsThrough_of_eq_mul {k : Type*} [Fintype k] {M : Matrix m n R} (P : Matrix m k R)
    (Q : Matrix k n R) (h : P * Q = M) {r : ℕ} (hr : Fintype.card k ≤ r) :
    FactorsThrough M r :=
  h ▸ (factorsThrough_mul P Q).mono hr

/-- `FactorsThrough M r` can be witnessed through any finite type of cardinality `r`. -/
theorem factorsThrough_iff_exists {k : Type*} [Fintype k] {M : Matrix m n R} {r : ℕ}
    (hk : Fintype.card k = r) :
    FactorsThrough M r ↔ ∃ (P : Matrix m k R) (Q : Matrix k n R), P * Q = M := by
  classical
  refine ⟨fun ⟨P, Q, h⟩ => ?_, fun ⟨P, Q, h⟩ => factorsThrough_of_eq_mul P Q h hk.le⟩
  let e : k ≃ Fin r := (Fintype.equivFin k).trans (finCongr hk)
  refine ⟨P.submatrix id e, Q.submatrix e id, ?_⟩
  rw [submatrix_mul_equiv, submatrix_id_id, h]

theorem factorsThrough_zero_iff {M : Matrix m n R} : FactorsThrough M 0 ↔ M = 0 := by
  constructor
  · rintro ⟨P, Q, rfl⟩
    ext i j
    simp [mul_apply]
  · rintro rfl
    exact ⟨0, 0, by simp⟩

theorem factorsThrough_zero_matrix (r : ℕ) : FactorsThrough (0 : Matrix m n R) r :=
  (factorsThrough_zero_iff.2 rfl).mono (Nat.zero_le r)

/-- Diagonal sums of factorizations. -/
theorem FactorsThrough.fromBlocks_diag {A : Matrix m n R} {B : Matrix m' n' R} {r s : ℕ}
    (hA : FactorsThrough A r) (hB : FactorsThrough B s) :
    FactorsThrough (fromBlocks A 0 0 B) (r + s) := by
  obtain ⟨P, Q, rfl⟩ := hA
  obtain ⟨P', Q', rfl⟩ := hB
  refine factorsThrough_of_eq_mul (fromBlocks P 0 0 P') (fromBlocks Q 0 0 Q') ?_ (by simp)
  simp [fromBlocks_multiply]

/-- Stacking two factorizations with a common right factor side-by-side. -/
theorem FactorsThrough.fromRows {A : Matrix m n R} {B : Matrix m' n R} {r s : ℕ}
    (hA : FactorsThrough A r) (hB : FactorsThrough B s) :
    FactorsThrough (Matrix.fromRows A B) (r + s) := by
  obtain ⟨P, Q, rfl⟩ := hA
  obtain ⟨P', Q', rfl⟩ := hB
  refine factorsThrough_of_eq_mul (fromBlocks P 0 0 P') (Matrix.fromRows Q Q') ?_ (by simp)
  ext (i | i) j <;> simp [mul_apply, Fintype.sum_sum_type, fromBlocks]

theorem FactorsThrough.fromCols {A : Matrix m n R} {B : Matrix m n' R} {r s : ℕ}
    (hA : FactorsThrough A r) (hB : FactorsThrough B s) :
    FactorsThrough (Matrix.fromCols A B) (r + s) := by
  obtain ⟨P, Q, rfl⟩ := hA
  obtain ⟨P', Q', rfl⟩ := hB
  refine factorsThrough_of_eq_mul (Matrix.fromCols P P') (fromBlocks Q 0 0 Q') ?_ (by simp)
  ext i (j | j) <;> simp [mul_apply, Fintype.sum_sum_type, fromBlocks]

end FactorsThrough

/-! ## `IsFullG` -/

/-- Index-general version of `IsFull`: `A` does not factor through any `r < card ι`. -/
def IsFullG {ι : Type*} [Fintype ι] (A : Matrix ι ι R) : Prop :=
  ∀ r < Fintype.card ι, ¬ FactorsThrough A r

section IsFullG

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem isFullG_iff_isFull {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : IsFullG A ↔ IsFull A := by
  simp [IsFullG, IsFull, FactorsThrough]

theorem isFullG_reindex_iff (e : ι ≃ κ) (A : Matrix ι ι R) :
    IsFullG (reindex e e A) ↔ IsFullG A := by
  simp only [IsFullG, factorsThrough_reindex, Fintype.card_congr e]

theorem not_isFullG_iff (A : Matrix ι ι R) (h : 0 < Fintype.card ι) :
    ¬ IsFullG A ↔ FactorsThrough A (Fintype.card ι - 1) := by
  simp only [IsFullG, not_forall, not_not, exists_prop]
  exact ⟨fun ⟨r, hr, hA⟩ => hA.mono (by omega), fun hA => ⟨_, by omega, hA⟩⟩

theorem not_isFullG_iff_exists (A : Matrix ι ι R) :
    ¬ IsFullG A ↔ ∃ r < Fintype.card ι, FactorsThrough A r := by
  simp [IsFullG]

theorem IsFullG.not_factorsThrough {A : Matrix ι ι R} (hA : IsFullG A) {r : ℕ}
    (hr : r < Fintype.card ι) : ¬ FactorsThrough A r :=
  hA r hr

/-- A full matrix is not a product through a smaller finite type. -/
theorem IsFullG.mul_ne {A : Matrix ι ι R} (hA : IsFullG A) {k : Type*} [Fintype k]
    (hk : Fintype.card k < Fintype.card ι) (P : Matrix ι k R) (Q : Matrix k ι R) : P * Q ≠ A :=
  fun h => hA _ hk (h ▸ factorsThrough_mul P Q)

theorem not_isFullG_of_factorsThrough {A : Matrix ι ι R} {r : ℕ} (hr : r < Fintype.card ι)
    (h : FactorsThrough A r) : ¬ IsFullG A :=
  fun hA => hA r hr h

theorem not_isFullG_mul {k : Type*} [Fintype k] (hk : Fintype.card k < Fintype.card ι)
    (P : Matrix ι k R) (Q : Matrix k ι R) : ¬ IsFullG (P * Q) :=
  fun h => h.mul_ne hk P Q rfl

theorem isFullG_of_isEmpty [IsEmpty ι] (A : Matrix ι ι R) : IsFullG A := by
  intro r hr
  simp at hr

theorem isFullG_unit_iff (a : R) : IsFullG (Matrix.of fun (_ _ : Unit) => a) ↔ a ≠ 0 := by
  simp only [IsFullG, Fintype.card_unit, Nat.lt_one_iff, forall_eq, factorsThrough_zero_iff]
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · simpa using congrFun (congrFun h ()) ()
  · ext; simp [h]

/-- A left factor of a full square product is full (any ring). -/
theorem isFullG_left_of_mul {P Q : Matrix ι ι R} (h : IsFullG (P * Q)) : IsFullG P :=
  fun r hr hP => h r hr (hP.mul_right Q)

/-- A right factor of a full square product is full (any ring). -/
theorem isFullG_right_of_mul {P Q : Matrix ι ι R} (h : IsFullG (P * Q)) : IsFullG Q :=
  fun r hr hQ => h r hr (hQ.mul_left P)

theorem isFullG_mul_isUnit_iff [DecidableEq ι] {A U : Matrix ι ι R} (hU : IsUnit U) :
    IsFullG (A * U) ↔ IsFullG A := by
  refine ⟨isFullG_left_of_mul, fun hA r hr h => hA r hr ?_⟩
  obtain ⟨u, rfl⟩ := hU
  simpa [Matrix.mul_assoc] using h.mul_right (↑u⁻¹ : Matrix ι ι R)

theorem isFullG_isUnit_mul_iff [DecidableEq ι] {A U : Matrix ι ι R} (hU : IsUnit U) :
    IsFullG (U * A) ↔ IsFullG A := by
  refine ⟨isFullG_right_of_mul, fun hA r hr h => hA r hr ?_⟩
  obtain ⟨u, rfl⟩ := hU
  simpa [← Matrix.mul_assoc] using h.mul_left (↑u⁻¹ : Matrix ι ι R)

/-- Upper block-triangular extensions of non-full matrices are non-full (any ring, no hypothesis
on `G`): `[[PQ, C], [0, G]] = [[P, C], [0, G]] · [[Q, 0], [0, 1]]`. -/
theorem not_isFullG_fromBlocks_upper {A : Matrix ι ι R} (hA : ¬ IsFullG A) (C : Matrix ι κ R)
    (G : Matrix κ κ R) : ¬ IsFullG (Matrix.fromBlocks A C 0 G) := by
  classical
  obtain ⟨r, hr, P, Q, rfl⟩ := (not_isFullG_iff_exists A).1 hA
  refine not_isFullG_of_factorsThrough (r := Fintype.card (Fin r ⊕ κ)) (by simpa using hr)
    (factorsThrough_of_eq_mul (fromBlocks P C 0 G) (fromBlocks Q 0 0 1) ?_ le_rfl)
  simp [fromBlocks_multiply]

/-- Lower block-triangular extensions of non-full matrices are non-full (any ring):
`[[PQ, 0], [C, G]] = [[P, 0], [0, 1]] · [[Q, 0], [C, G]]`. -/
theorem not_isFullG_fromBlocks_lower {A : Matrix ι ι R} (hA : ¬ IsFullG A) (C : Matrix κ ι R)
    (G : Matrix κ κ R) : ¬ IsFullG (Matrix.fromBlocks A 0 C G) := by
  classical
  obtain ⟨r, hr, P, Q, rfl⟩ := (not_isFullG_iff_exists A).1 hA
  refine not_isFullG_of_factorsThrough (r := Fintype.card (Fin r ⊕ κ)) (by simpa using hr)
    (factorsThrough_of_eq_mul (fromBlocks P 0 0 1) (fromBlocks Q 0 C G) ?_ le_rfl)
  simp [fromBlocks_multiply]

end IsFullG

/-! ## The class `FullClosed` -/

/-- **(FC)** — Cohn FIR Thm 7.5.13 (b)/(c): full matrices are closed under products and
diagonal sums.  Holds for every Sylvester domain, in particular every semifir (`Sylvester.lean`). -/
class FullClosed (R : Type u) [Ring R] : Prop where
  nontrivial : Nontrivial R
  mul : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι R},
    IsFullG A → IsFullG B → IsFullG (A * B)
  diag : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι R} {B : Matrix κ κ R}, IsFullG A → IsFullG B →
      IsFullG (Matrix.fromBlocks A 0 0 B)

instance (priority := 100) FullClosed.toNontrivial [h : FullClosed R] : Nontrivial R :=
  h.nontrivial

section FullClosed

variable [FullClosed R]

/-- `FullClosed.mul` for index types in any universe (reindex to `Fin`). -/
theorem IsFullG.mul {ι : Type*} [Fintype ι] {A B : Matrix ι ι R} (hA : IsFullG A)
    (hB : IsFullG B) : IsFullG (A * B) := by
  classical
  let e := Fintype.equivFin ι
  rw [← isFullG_reindex_iff e] at hA hB ⊢
  rw [reindex_apply, ← submatrix_mul_equiv _ _ _ e.symm]
  exact FullClosed.mul hA hB

/-- `FullClosed.diag` for index types in any universe (reindex to `Fin`). -/
theorem IsFullG.fromBlocks_diag {ι κ : Type*} [Fintype ι] [Fintype κ] {A : Matrix ι ι R}
    {B : Matrix κ κ R} (hA : IsFullG A) (hB : IsFullG B) :
    IsFullG (Matrix.fromBlocks A 0 0 B) := by
  classical
  let e₁ := Fintype.equivFin ι
  let e₂ := Fintype.equivFin κ
  rw [← isFullG_reindex_iff e₁] at hA
  rw [← isFullG_reindex_iff e₂] at hB
  rw [← isFullG_reindex_iff (e₁.sumCongr e₂)]
  convert FullClosed.diag hA hB using 1
  ext (i | i) (j | j) <;> simp [reindex_apply]

theorem isFullG_one (ι : Type*) [Fintype ι] [DecidableEq ι] : IsFullG (1 : Matrix ι ι R) := by
  have hfin : ∀ n : ℕ, IsFullG (1 : Matrix (Fin n) (Fin n) R) := by
    intro n
    induction n with
    | zero => exact isFullG_of_isEmpty _
    | succ n ih =>
      have h1 : IsFullG (1 : Matrix Unit Unit R) := by
        convert (isFullG_unit_iff (1 : R)).2 one_ne_zero using 1
        ext; simp
      have h2 := ih.fromBlocks_diag h1
      rw [fromBlocks_one, ← isFullG_reindex_iff
        ((Equiv.sumCongr (Equiv.refl (Fin n)) (Equiv.ofUnique Unit (Fin 1))).trans
          finSumFinEquiv)] at h2
      rwa [reindex_apply, submatrix_one_equiv] at h2
  let e := Fintype.equivFin ι
  rw [← isFullG_reindex_iff e]
  have := hfin (Fintype.card ι)
  rwa [reindex_apply, submatrix_one_equiv]

theorem isFullG_of_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι R}
    (h : IsUnit A) : IsFullG A := by
  simpa using (isFullG_isUnit_mul_iff (A := 1) h).2 (isFullG_one (R := R) ι)

/-- `[[A, C], [0, G]] = (1 ⊕ G) · [[1, C], [0, 1]] · (A ⊕ 1)`. -/
theorem isFullG_fromBlocks_upper {ι κ : Type*} [Fintype ι] [Fintype κ] {A : Matrix ι ι R}
    {G : Matrix κ κ R} (hA : IsFullG A) (hG : IsFullG G) (C : Matrix ι κ R) :
    IsFullG (Matrix.fromBlocks A C 0 G) := by
  classical
  have hU : IsUnit (fromBlocks (1 : Matrix ι ι R) C 0 (1 : Matrix κ κ R)) := by
    have h1 : fromBlocks (1 : Matrix ι ι R) C 0 (1 : Matrix κ κ R) *
        fromBlocks (1 : Matrix ι ι R) (-C) 0 (1 : Matrix κ κ R) = 1 := by
      rw [fromBlocks_multiply, ← fromBlocks_one]; congr 1 <;> simp
    have h2 : fromBlocks (1 : Matrix ι ι R) (-C) 0 (1 : Matrix κ κ R) *
        fromBlocks (1 : Matrix ι ι R) C 0 (1 : Matrix κ κ R) = 1 := by
      rw [fromBlocks_multiply, ← fromBlocks_one]; congr 1 <;> simp
    exact ⟨⟨_, _, h1, h2⟩, rfl⟩
  have h := ((isFullG_one (R := R) ι).fromBlocks_diag hG).mul
    ((isFullG_of_isUnit hU).mul (hA.fromBlocks_diag (isFullG_one (R := R) κ)))
  convert h using 1
  simp [fromBlocks_multiply]

/-- `[[A, 0], [C, G]] = (A ⊕ 1) · [[1, 0], [C, 1]] · (1 ⊕ G)`. -/
theorem isFullG_fromBlocks_lower {ι κ : Type*} [Fintype ι] [Fintype κ] {A : Matrix ι ι R}
    {G : Matrix κ κ R} (hA : IsFullG A) (hG : IsFullG G) (C : Matrix κ ι R) :
    IsFullG (Matrix.fromBlocks A 0 C G) := by
  classical
  have hU : IsUnit (fromBlocks (1 : Matrix ι ι R) 0 C (1 : Matrix κ κ R)) := by
    have h1 : fromBlocks (1 : Matrix ι ι R) 0 C (1 : Matrix κ κ R) *
        fromBlocks (1 : Matrix ι ι R) 0 (-C) (1 : Matrix κ κ R) = 1 := by
      rw [fromBlocks_multiply, ← fromBlocks_one]; congr 1 <;> simp
    have h2 : fromBlocks (1 : Matrix ι ι R) 0 (-C) (1 : Matrix κ κ R) *
        fromBlocks (1 : Matrix ι ι R) 0 C (1 : Matrix κ κ R) = 1 := by
      rw [fromBlocks_multiply, ← fromBlocks_one]; congr 1 <;> simp
    exact ⟨⟨_, _, h1, h2⟩, rfl⟩
  have h := (hA.fromBlocks_diag (isFullG_one (R := R) κ)).mul
    ((isFullG_of_isUnit hU).mul ((isFullG_one (R := R) ι).fromBlocks_diag hG))
  convert h using 1
  simp [fromBlocks_multiply]

/-- The block-triangular `iff` used by the display invariant (`DisplayModel.lean`), upper version. -/
theorem isFullG_fromBlocks_upper_iff {ι κ : Type*} [Fintype ι] [Fintype κ] {A : Matrix ι ι R}
    {G : Matrix κ κ R} (C : Matrix ι κ R) (hG : IsFullG G) :
    IsFullG (Matrix.fromBlocks A C 0 G) ↔ IsFullG A :=
  ⟨fun h => by_contra fun hA => not_isFullG_fromBlocks_upper hA C G h,
    fun hA => isFullG_fromBlocks_upper hA hG C⟩

/-- The block-triangular `iff` used by the display invariant (`DisplayModel.lean`), lower version. -/
theorem isFullG_fromBlocks_lower_iff {ι κ : Type*} [Fintype ι] [Fintype κ] {A : Matrix ι ι R}
    {G : Matrix κ κ R} (C : Matrix κ ι R) (hG : IsFullG G) :
    IsFullG (Matrix.fromBlocks A 0 C G) ↔ IsFullG A :=
  ⟨fun h => by_contra fun hA => not_isFullG_fromBlocks_lower hA C G h,
    fun hA => isFullG_fromBlocks_lower hA hG C⟩

theorem isFullG_fromBlocks_diag_iff {ι κ : Type*} [Fintype ι] [Fintype κ] {A : Matrix ι ι R}
    {G : Matrix κ κ R} (hG : IsFullG G) :
    IsFullG (Matrix.fromBlocks A 0 0 G) ↔ IsFullG A :=
  isFullG_fromBlocks_upper_iff 0 hG

end FullClosed

end LeftPCI.FreeField
