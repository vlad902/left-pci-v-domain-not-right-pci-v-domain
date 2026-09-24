module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Ring.Hom.Defs

@[expose] public section

namespace LeftPCI.FreeField

/-! # Full matrices (Cohn, *Free Ideal Rings* §0.1 / §5.4; *Skew Fields* §4.5)

An `n × n` matrix `A` over a ring `R` is **full** if it cannot be written as `A = P * Q` with
`P : n × r`, `Q : r × n` and `r < n` (i.e. its *inner rank* is `n`).  Over a semifir the full
matrices are exactly the matrices that become invertible over the universal field of fractions
(Cohn *Skew Fields* Cor. 4.5.9), which is the content of
`LeftPCI/FreeField/Interface.lean` (proved in `UniversalField.lean`).

A homomorphism is **honest** (Cohn *Skew Fields* §4.5) if it maps full matrices to full matrices.
The only source of honesty needed downstream is `IsFull.map_of_leftInverse`: a homomorphism with a
left-inverse homomorphism is honest (this generalizes Cohn's Prop. 4.5.1, "the inclusion of a
retract is honest", and also covers isomorphisms).
-/

variable {R S : Type*} [Ring R] [Ring S]

/-- **Cohn's full matrix**: `A` does not factor through any `r < n`. -/
def IsFull {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ r < n, ∀ (P : Matrix (Fin n) (Fin r) R) (Q : Matrix (Fin r) (Fin n) R), P * Q ≠ A

/-- `f` inverts every full matrix: Cohn's *`Φ`-inverting* homomorphism, `Φ` = full matrices. -/
def IsFullInverting (f : R →+* S) : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R), IsFull A → IsUnit (A.map f)

/-- `f` is **honest**: it maps full matrices to full matrices. -/
def IsHonest (f : R →+* S) : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R), IsFull A → IsFull (A.map f)

/-- A `1 × 1` matrix is full iff its entry is nonzero. -/
theorem isFull_one_iff (a : R) : IsFull (Matrix.of fun (_ _ : Fin 1) => a) ↔ a ≠ 0 := by
  constructor
  · intro h ha
    apply h 0 Nat.zero_lt_one 0 0
    ext i j
    simp [ha]
  · intro ha r hr P Q hPQ
    have hr0 : r = 0 := by omega
    subst hr0
    apply ha
    have := congrFun (congrFun hPQ 0) 0
    simpa [Matrix.mul_apply] using this.symm

/-- **A homomorphism with a left-inverse homomorphism is honest.**  If `f A = P Q` through
`r < n`, apply the left inverse `g` to get `A = g(P) g(Q)`.  (Cohn *Skew Fields* Prop. 4.5.1 is
the special case of the inclusion of a retract.) -/
theorem isHonest_of_leftInverse (f : R →+* S) (g : S →+* R) (hgf : ∀ r, g (f r) = r) :
    IsHonest f := by
  intro n A hA r hr P Q hPQ
  apply hA r hr (P.map g) (Q.map g)
  rw [← Matrix.map_mul, hPQ, Matrix.map_map]
  ext i j
  simp [hgf]

/-- Honest followed by full-inverting is full-inverting. -/
theorem IsFullInverting.comp_of_isHonest {T : Type*} [Ring T] {g : S →+* T} (hg : IsFullInverting g)
    {f : R →+* S} (hf : IsHonest f) : IsFullInverting (g.comp f) := by
  intro n A hA
  have := hg n (A.map f) (hf n A hA)
  rwa [Matrix.map_map] at this

end LeftPCI.FreeField
