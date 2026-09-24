module

public import LeftPCI.FreeField.FullCalculus
public import LeftPCI.FreeField.UniversalLocalization

@[expose] public section

/-! # The display model

Cohn's construction of the universal localization from *displays* (Cohn, *Free Ideal Rings and
Localization in General Rings* §7.4 pp. 437–441, a version of Malcolmson's construction), over a
ring with `FullClosed R` (full matrices closed under products and diagonal sums).

A display `d : Disp R` is `[[A, u], [x, a]]` with `A : Matrix d.ι d.ι R` full (`d.ι : Type`
finite), representing `a - x A⁻¹ u`.  Sum and product are FIR (2), (3); negation is
`x ↦ -x, a ↦ -a`.

## The step relation (final definition)

`Step d d'` has three constructors, each with an explicit reindexing equivalence `e` and a
*matrix equation* for `d'.mat` (never an equality of `Disp` structures):

* `lin  e P Q hP hQ g f`: `d'.mat = reindex (e ⊕ 1) (e ⊕ 1) (lMat P g * d.mat * rMat Q f)` with
  `lMat P g = [[P, 0], [g, 1]]`, `rMat Q f = [[Q, f], [0, 1]]`, `P Q : Matrix d.ι d.ι R` full,
  `e : d.ι ≃ d'.ι` (FIR F.1, F.2 and their duals, and reindexing);
* `up κ G hG C p e`: `d'.mat = reindex (e ⊕ 1) (e ⊕ 1) (insUpMat d.A d.u d.x d.a G C p)` where
  `insUpMat … = [[A, C, u], [0, G, 0], [x, p, a]]` on `(d.ι ⊕ κ) ⊕ Unit`, `G` full,
  `e : d.ι ⊕ κ ≃ d'.ι` — insert a trivial block whose *row* vanishes off `G` (column arbitrary);
* `low κ G hG C q e`: the same with `insLowMat … = [[A, 0, u], [C, G, q], [x, 0, a]]` — the
  trivial block's *column* vanishes off `G` (row arbitrary).

(The plan's combined `L · Ins · R` steps are `up`/`low` followed by `lin`; separating them makes
each compatibility case a single step.)  `Step.rec'`, `Step.lin_of`, `Step.up_of`, `Step.low_of`
translate between the matrix equations and field-wise equations.

## Main results

* `Step.isFullG_mat_iff` — **the fullness invariant**: every step preserves fullness of the
  display matrix in both directions (replaces Malcolmson's criterion, FIR Lemma 7.4.1).
* `Step.add_left`, `Step.add_comm`, `Step.mul_left`, `Step.mul_right`, `Step.neg` — every
  compatibility is a *single* step; hence the operations descend to `M R := Quot Step`.
* `M.fullPred`, `M.zero_ne_one`.
* Ring axioms on `M R` (`M.add_assoc'`, …, `M.left_distrib'`, `M.right_distrib'`,
  `M.neg_add_cancel'`), `M.instRing`, `M.ofR : R →+* M R`, `M.isUnit_map_ofR` (full-inverting,
  via the row/column merging lemmas `M.mk_dispOf_add_row/col`), and
  `nontrivial_loc_isFull : Nontrivial (UnivLoc.Loc fun n A => IsFull A)`.

Left distributivity is not written out in Cohn ("follows similarly"); the chain here is:
in `de + df` do `col d' -= col d`, `row d += row d'` (one `lin` step), then a low-removal of the
block `d'` (zero column, arbitrary row).  Cohn's claim that `M(Σ)` is `Σ`-inverting (FIR p. 440)
is proved directly (`M.isUnit_map_ofR`).
-/

namespace LeftPCI.FreeField.Display

open Matrix

universe u

set_option linter.unusedSectionVars false

variable {R : Type u} [Ring R]

/-- The block matrix `[[A, u], [x, a]]`. -/
def dmat {ι : Type*} (A : Matrix ι ι R) (u x : ι → R) (a : R) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  fromBlocks A (of fun i _ => u i) (of fun _ j => x j) (of fun _ _ => a)

/-- `[[P, 0], [g, 1]]`. -/
def lMat {ι : Type*} [DecidableEq ι] (P : Matrix ι ι R) (g : ι → R) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  fromBlocks P 0 (of fun _ j => g j) 1

/-- `[[Q, f], [0, 1]]`. -/
def rMat {ι : Type*} [DecidableEq ι] (Q : Matrix ι ι R) (f : ι → R) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  fromBlocks Q (of fun i _ => f i) 0 1

section dmat
variable {ι κ : Type*}

@[simp] theorem dmat_inl_inl (A : Matrix ι ι R) (u x : ι → R) (a : R) (i j : ι) :
    dmat A u x a (.inl i) (.inl j) = A i j := rfl
@[simp] theorem dmat_inl_inr (A : Matrix ι ι R) (u x : ι → R) (a : R) (i : ι) (j : Unit) :
    dmat A u x a (.inl i) (.inr j) = u i := rfl
@[simp] theorem dmat_inr_inl (A : Matrix ι ι R) (u x : ι → R) (a : R) (i : Unit) (j : ι) :
    dmat A u x a (.inr i) (.inl j) = x j := rfl
@[simp] theorem dmat_inr_inr (A : Matrix ι ι R) (u x : ι → R) (a : R) (i j : Unit) :
    dmat A u x a (.inr i) (.inr j) = a := rfl

theorem dmat_inj {A A' : Matrix ι ι R} {u u' x x' : ι → R} {a a' : R} :
    dmat A u x a = dmat A' u' x' a' ↔ A = A' ∧ u = u' ∧ x = x' ∧ a = a' := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext i j; simpa using congrFun (congrFun h (.inl i)) (.inl j)
    · ext i; simpa using congrFun (congrFun h (.inl i)) (.inr ())
    · ext j; simpa using congrFun (congrFun h (.inr ())) (.inl j)
    · simpa using congrFun (congrFun h (.inr ())) (.inr ())
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

theorem reindex_dmat (e : ι ≃ κ) (A : Matrix ι ι R) (u x : ι → R) (a : R) :
    reindex (e.sumCongr (Equiv.refl Unit)) (e.sumCongr (Equiv.refl Unit)) (dmat A u x a) =
      dmat (reindex e e A) (u ∘ e.symm) (x ∘ e.symm) a := by
  ext (i | i) (j | j) <;> rfl

set_option linter.flexible false in
theorem lMat_mul_dmat_mul_rMat [Fintype ι] [DecidableEq ι] (P Q A : Matrix ι ι R) (g f u x : ι → R) (a : R) :
    lMat P g * dmat A u x a * rMat Q f =
      dmat (P * A * Q) (P *ᵥ (A *ᵥ f + u)) ((g ᵥ* A + x) ᵥ* Q)
        ((g ᵥ* A + x) ⬝ᵥ f + g ⬝ᵥ u + a) := by
  ext (i | i) (j | j) <;>
    simp [lMat, rMat, dmat, fromBlocks_multiply, mul_apply, mulVec, vecMul, dotProduct,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, add_mul, mul_add, mul_assoc]
  all_goals first | exact Finset.sum_comm | abel

/-- `Ins↑`: `[[A, C, u], [0, G, 0], [x, p, a]]` laid out on `(ι ⊕ κ) ⊕ Unit`. -/
def insUpMat (A : Matrix ι ι R) (u x : ι → R) (a : R) (G : Matrix κ κ R) (C : Matrix ι κ R)
    (p : κ → R) : Matrix ((ι ⊕ κ) ⊕ Unit) ((ι ⊕ κ) ⊕ Unit) R :=
  dmat (fromBlocks A C 0 G) (Sum.elim u 0) (Sum.elim x p) a

/-- `Ins↓`: `[[A, 0, u], [C, G, q], [x, 0, a]]` laid out on `(ι ⊕ κ) ⊕ Unit`. -/
def insLowMat (A : Matrix ι ι R) (u x : ι → R) (a : R) (G : Matrix κ κ R) (C : Matrix κ ι R)
    (q : κ → R) : Matrix ((ι ⊕ κ) ⊕ Unit) ((ι ⊕ κ) ⊕ Unit) R :=
  dmat (fromBlocks A 0 C G) (Sum.elim u q) (Sum.elim x 0) a

/-- The reordering `(α ⊕ β) ⊕ γ ≃ (α ⊕ γ) ⊕ β`. -/
def sumSwapRight (α β γ : Type*) : (α ⊕ β) ⊕ γ ≃ (α ⊕ γ) ⊕ β :=
  (Equiv.sumAssoc α β γ).trans (((Equiv.refl α).sumCongr (Equiv.sumComm β γ)).trans
    (Equiv.sumAssoc α γ β).symm)

@[simp] theorem sumSwapRight_inl_inl {α β γ : Type*} (a : α) :
    sumSwapRight α β γ (.inl (.inl a)) = .inl (.inl a) := rfl
@[simp] theorem sumSwapRight_inl_inr {α β γ : Type*} (b : β) :
    sumSwapRight α β γ (.inl (.inr b)) = .inr b := rfl
@[simp] theorem sumSwapRight_inr {α β γ : Type*} (c : γ) :
    sumSwapRight α β γ (.inr c) = .inl (.inr c) := rfl

/-- The reordering `(ι ⊕ κ) ⊕ Unit ≃ (ι ⊕ Unit) ⊕ κ`. -/
abbrev moveEquiv (ι κ : Type*) : (ι ⊕ κ) ⊕ Unit ≃ (ι ⊕ Unit) ⊕ κ := sumSwapRight ι κ Unit

theorem reindex_insUpMat (A : Matrix ι ι R) (u x : ι → R) (a : R) (G : Matrix κ κ R)
    (C : Matrix ι κ R) (p : κ → R) :
    reindex (moveEquiv ι κ) (moveEquiv ι κ) (insUpMat A u x a G C p) =
      fromBlocks (dmat A u x a) (of fun i k => Sum.elim (fun i => C i k) (fun _ => p k) i) 0 G := by
  ext ((i | i) | i) ((j | j) | j) <;> rfl

theorem reindex_insLowMat (A : Matrix ι ι R) (u x : ι → R) (a : R) (G : Matrix κ κ R)
    (C : Matrix κ ι R) (q : κ → R) :
    reindex (moveEquiv ι κ) (moveEquiv ι κ) (insLowMat A u x a G C q) =
      fromBlocks (dmat A u x a) 0 (of fun k j => Sum.elim (fun j => C k j) (fun _ => q k) j) G := by
  ext ((i | i) | i) ((j | j) | j) <;> rfl

end dmat

/-! ## Displays -/

/-- Cohn's display `[[A, u], [x, a]]`, representing `a - x A⁻¹ u` (FIR §7.4 p. 437).
Indexed by an arbitrary finite `ι : Type`, so it lives in `Type (max u 1)` — this is harmless:
it is only used to show that the universal localization is nontrivial. -/
structure Disp (R : Type u) [Ring R] where
  /-- the index type of the denominator -/
  ι : Type
  [instFintype : Fintype ι]
  [instDecEq : DecidableEq ι]
  /-- the denominator -/
  A : Matrix ι ι R
  /-- the last column (numerator side) -/
  u : ι → R
  /-- the last row -/
  x : ι → R
  /-- the corner entry -/
  a : R
  /-- the denominator is full -/
  full : IsFullG A

attribute [instance] Disp.instFintype Disp.instDecEq

namespace Disp

/-- The display matrix `[[A, u], [x, a]]`. -/
def mat (d : Disp R) : Matrix (d.ι ⊕ Unit) (d.ι ⊕ Unit) R := dmat d.A d.u d.x d.a

/-- The scalar display `(r)` (empty denominator). -/
@[reducible] def scalar (r : R) : Disp R where
  ι := Empty
  A := 0
  u := 0
  x := 0
  a := r
  full := isFullG_of_isEmpty _

/-- Negation: `[[A, u], [-x, -a]]` (value `-(a - x A⁻¹ u)`). -/
@[reducible] def neg (d : Disp R) : Disp R where
  ι := d.ι
  A := d.A
  u := d.u
  x := -d.x
  a := -d.a
  full := d.full

variable [FullClosed R]

/-- Sum, FIR §7.4 (2): `[[A, 0, u], [0, B, v], [x, y, a + b]]`. -/
@[reducible] def add (d e : Disp R) : Disp R where
  ι := d.ι ⊕ e.ι
  A := fromBlocks d.A 0 0 e.A
  u := Sum.elim d.u e.u
  x := Sum.elim d.x e.x
  a := d.a + e.a
  full := d.full.fromBlocks_diag e.full

/-- Product, FIR §7.4 (3): `[[A, u y, u b], [0, B, v], [x, a y, a b]]`. -/
@[reducible] def mul (d e : Disp R) : Disp R where
  ι := d.ι ⊕ e.ι
  A := fromBlocks d.A (of fun i j => d.u i * e.x j) 0 e.A
  u := Sum.elim (fun i => d.u i * e.a) e.u
  x := Sum.elim d.x (fun j => d.a * e.x j)
  a := d.a * e.a
  full := isFullG_fromBlocks_upper d.full e.full _

end Disp

/-! ## The step relation -/

/-- One elementary operation on displays.  Three shapes (all with an explicit reindexing
equivalence `e` and a matrix equation):
* `lin`: `d'.mat ≅ [[P, 0], [g, 1]] · d.mat · [[Q, f], [0, 1]]` with `P, Q` full
  (FIR F.1, F.2 and their duals, plus reindexing);
* `up`: `d'.mat ≅ [[A, C, u], [0, G, 0], [x, p, a]]` with `G` full (insert a trivial block
  whose *row* vanishes off `G`; its column `(C; p)` is arbitrary) — generalizes FIR F.3′;
* `low`: `d'.mat ≅ [[A, 0, u], [C, G, q], [x, 0, a]]` with `G` full (insert a trivial block
  whose *column* vanishes off `G`; its row `(C, q)` is arbitrary) — generalizes FIR F.3. -/
inductive Step : Disp R → Disp R → Prop
  | lin (d d' : Disp R) (e : d.ι ≃ d'.ι) (P Q : Matrix d.ι d.ι R) (hP : IsFullG P)
      (hQ : IsFullG Q) (g f : d.ι → R)
      (h : d'.mat = reindex (e.sumCongr (Equiv.refl Unit)) (e.sumCongr (Equiv.refl Unit))
        (lMat P g * d.mat * rMat Q f)) : Step d d'
  | up (d d' : Disp R) (κ : Type) [Fintype κ] (G : Matrix κ κ R)
      (hG : IsFullG G) (C : Matrix d.ι κ R) (p : κ → R) (e : d.ι ⊕ κ ≃ d'.ι)
      (h : d'.mat = reindex (e.sumCongr (Equiv.refl Unit)) (e.sumCongr (Equiv.refl Unit))
        (insUpMat d.A d.u d.x d.a G C p)) : Step d d'
  | low (d d' : Disp R) (κ : Type) [Fintype κ] (G : Matrix κ κ R)
      (hG : IsFullG G) (C : Matrix κ d.ι R) (q : κ → R) (e : d.ι ⊕ κ ≃ d'.ι)
      (h : d'.mat = reindex (e.sumCongr (Equiv.refl Unit)) (e.sumCongr (Equiv.refl Unit))
        (insLowMat d.A d.u d.x d.a G C q)) : Step d d'

theorem Disp.mat_eq_reindex_dmat_iff {ι : Type*} (d : Disp R) (e : ι ≃ d.ι) (A : Matrix ι ι R)
    (u x : ι → R) (a : R) :
    d.mat = reindex (e.sumCongr (Equiv.refl Unit)) (e.sumCongr (Equiv.refl Unit)) (dmat A u x a) ↔
      (∀ i j, d.A (e i) (e j) = A i j) ∧ (∀ i, d.u (e i) = u i) ∧ (∀ j, d.x (e j) = x j) ∧
        d.a = a := by
  rw [reindex_dmat, Disp.mat, dmat_inj]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ Iff.rfl))
  · refine ⟨fun h i j => by simp [h], fun h => ?_⟩
    ext i j; simpa using h (e.symm i) (e.symm j)
  · refine ⟨fun h i => by simp [h], fun h => ?_⟩
    ext i; simpa using h (e.symm i)
  · refine ⟨fun h i => by simp [h], fun h => ?_⟩
    ext i; simpa using h (e.symm i)

/-! ## The fullness invariant -/

section Invariant

variable [FullClosed R]

theorem isFullG_mul_mul_iff {ι : Type*} [Fintype ι] {L M N : Matrix ι ι R} (hL : IsFullG L)
    (hN : IsFullG N) : IsFullG (L * M * N) ↔ IsFullG M :=
  ⟨fun h => isFullG_right_of_mul (isFullG_left_of_mul h), fun h => (hL.mul h).mul hN⟩

theorem isFullG_lMat {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι R}
    (hP : IsFullG P) (g : ι → R) : IsFullG (lMat P g) :=
  isFullG_fromBlocks_lower hP (isFullG_one Unit) _

theorem isFullG_rMat {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι R}
    (hQ : IsFullG Q) (f : ι → R) : IsFullG (rMat Q f) :=
  isFullG_fromBlocks_upper hQ (isFullG_one Unit) _

/-- **The fullness invariant**: every elementary operation preserves fullness of the display
matrix, in both directions.  This replaces Malcolmson's criterion (FIR Lemma 7.4.1). -/
theorem Step.isFullG_mat_iff {d d' : Disp R} (h : Step d d') :
    IsFullG d.mat ↔ IsFullG d'.mat := by
  cases h with
  | lin e P Q hP hQ g f h =>
    rw [h, isFullG_reindex_iff, isFullG_mul_mul_iff (isFullG_lMat hP g) (isFullG_rMat hQ f)]
  | up κ G hG C p e h =>
    rw [h, isFullG_reindex_iff, ← isFullG_reindex_iff (moveEquiv d.ι κ), reindex_insUpMat,
      isFullG_fromBlocks_upper_iff _ hG]
    rfl
  | low κ G hG C q e h =>
    rw [h, isFullG_reindex_iff, ← isFullG_reindex_iff (moveEquiv d.ι κ), reindex_insLowMat,
      isFullG_fromBlocks_lower_iff _ hG]
    rfl

end Invariant

/-! ## Field-level constructors and eliminator for `Step` -/

namespace Step

theorem lin_of {d d' : Disp R} (e : d.ι ≃ d'.ι) (P Q : Matrix d.ι d.ι R) (hP : IsFullG P)
    (hQ : IsFullG Q) (g f : d.ι → R)
    (hA : ∀ i j, d'.A (e i) (e j) = (P * d.A * Q) i j)
    (hu : ∀ i, d'.u (e i) = (P *ᵥ (d.A *ᵥ f + d.u)) i)
    (hx : ∀ j, d'.x (e j) = ((g ᵥ* d.A + d.x) ᵥ* Q) j)
    (ha : d'.a = (g ᵥ* d.A + d.x) ⬝ᵥ f + g ⬝ᵥ d.u + d.a) : Step d d' :=
  .lin d d' e P Q hP hQ g f (by
    change d'.mat = reindex _ _ (lMat P g * dmat d.A d.u d.x d.a * rMat Q f)
    rw [lMat_mul_dmat_mul_rMat, Disp.mat_eq_reindex_dmat_iff]
    exact ⟨hA, hu, hx, ha⟩)

theorem up_of {d d' : Disp R} (κ : Type) [Fintype κ] (G : Matrix κ κ R)
    (hG : IsFullG G) (C : Matrix d.ι κ R) (p : κ → R) (e : d.ι ⊕ κ ≃ d'.ι)
    (hA : ∀ i j, d'.A (e i) (e j) = fromBlocks d.A C 0 G i j)
    (hu : ∀ i, d'.u (e i) = Sum.elim d.u 0 i)
    (hx : ∀ j, d'.x (e j) = Sum.elim d.x p j)
    (ha : d'.a = d.a) : Step d d' :=
  .up d d' κ G hG C p e (by
    rw [insUpMat, Disp.mat_eq_reindex_dmat_iff]
    exact ⟨hA, hu, hx, ha⟩)

theorem low_of {d d' : Disp R} (κ : Type) [Fintype κ] (G : Matrix κ κ R)
    (hG : IsFullG G) (C : Matrix κ d.ι R) (q : κ → R) (e : d.ι ⊕ κ ≃ d'.ι)
    (hA : ∀ i j, d'.A (e i) (e j) = fromBlocks d.A 0 C G i j)
    (hu : ∀ i, d'.u (e i) = Sum.elim d.u q i)
    (hx : ∀ j, d'.x (e j) = Sum.elim d.x 0 j)
    (ha : d'.a = d.a) : Step d d' :=
  .low d d' κ G hG C q e (by
    rw [insLowMat, Disp.mat_eq_reindex_dmat_iff]
    exact ⟨hA, hu, hx, ha⟩)

/-- Eliminator for `Step` with the matrix equations unfolded into field equations. -/
theorem rec' {motive : Disp R → Disp R → Prop}
    (lin : ∀ (d d' : Disp R) (e : d.ι ≃ d'.ι) (P Q : Matrix d.ι d.ι R), IsFullG P → IsFullG Q →
      ∀ (g f : d.ι → R),
      (∀ i j, d'.A (e i) (e j) = (P * d.A * Q) i j) →
      (∀ i, d'.u (e i) = (P *ᵥ (d.A *ᵥ f + d.u)) i) →
      (∀ j, d'.x (e j) = ((g ᵥ* d.A + d.x) ᵥ* Q) j) →
      d'.a = (g ᵥ* d.A + d.x) ⬝ᵥ f + g ⬝ᵥ d.u + d.a → motive d d')
    (up : ∀ (d d' : Disp R) (κ : Type) [Fintype κ] (G : Matrix κ κ R),
      IsFullG G → ∀ (C : Matrix d.ι κ R) (p : κ → R) (e : d.ι ⊕ κ ≃ d'.ι),
      (∀ i j, d'.A (e i) (e j) = fromBlocks d.A C 0 G i j) →
      (∀ i, d'.u (e i) = Sum.elim d.u 0 i) →
      (∀ j, d'.x (e j) = Sum.elim d.x p j) → d'.a = d.a → motive d d')
    (low : ∀ (d d' : Disp R) (κ : Type) [Fintype κ] (G : Matrix κ κ R),
      IsFullG G → ∀ (C : Matrix κ d.ι R) (q : κ → R) (e : d.ι ⊕ κ ≃ d'.ι),
      (∀ i j, d'.A (e i) (e j) = fromBlocks d.A 0 C G i j) →
      (∀ i, d'.u (e i) = Sum.elim d.u q i) →
      (∀ j, d'.x (e j) = Sum.elim d.x 0 j) → d'.a = d.a → motive d d')
    {d d' : Disp R} (h : Step d d') : motive d d' := by
  cases h with
  | lin e P Q hP hQ g f h =>
    have h' : d'.mat = reindex _ _ (lMat P g * dmat d.A d.u d.x d.a * rMat Q f) := h
    rw [lMat_mul_dmat_mul_rMat, Disp.mat_eq_reindex_dmat_iff] at h'
    exact lin d d' e P Q hP hQ g f h'.1 h'.2.1 h'.2.2.1 h'.2.2.2
  | up κ G hG C p e h =>
    rw [insUpMat, Disp.mat_eq_reindex_dmat_iff] at h
    exact up d d' κ G hG C p e h.1 h.2.1 h.2.2.1 h.2.2.2
  | low κ G hG C q e h =>
    rw [insLowMat, Disp.mat_eq_reindex_dmat_iff] at h
    exact low d d' κ G hG C q e h.1 h.2.1 h.2.2.1 h.2.2.2

/-- Pure reindexing. -/
theorem reindex [FullClosed R] {d d' : Disp R} (e : d.ι ≃ d'.ι) (hA : ∀ i j, d'.A (e i) (e j) = d.A i j)
    (hu : ∀ i, d'.u (e i) = d.u i) (hx : ∀ j, d'.x (e j) = d.x j) (ha : d'.a = d.a) :
    Step d d' :=
  lin_of e 1 1 (isFullG_one _) (isFullG_one _) 0 0 (by simpa using hA) (by simpa using hu)
    (by simpa using hx) (by simpa using ha)

end Step

section Compat

/-- Expand matrix/vector products into (distributed) finite sums. -/
local macro "sum_expand" : tactic =>
  `(tactic| simp only [mul_apply, mulVec, vecMul, dotProduct, of_apply, Pi.add_apply, Matrix.add_apply,
    Finset.sum_mul, Finset.mul_sum, add_mul, mul_add, mul_assoc, Finset.sum_add_distrib])

/-- Close a goal of sums that agree up to `Finset.sum_comm` and reassociation. -/
local macro "sum_close" : tactic =>
  `(tactic| first
    | rfl
    | (congr 1 <;> first | rfl | exact Finset.sum_comm)
    | abel1
    | ((conv_lhs => rw [Finset.sum_comm]); abel1)
    | ((conv_rhs => rw [Finset.sum_comm]); abel1))

variable [FullClosed R]

theorem Step.add_left {d d' : Disp R} (h : Step d d') (c : Disp R) :
    Step (d.add c) (d'.add c) := by
  refine Step.rec' (motive := fun d d' => Step (d.add c) (d'.add c)) ?_ ?_ ?_ h
  · intro d d' e P Q hP hQ g f hA hu hx ha
    refine Step.lin_of (e.sumCongr (Equiv.refl c.ι)) (fromBlocks P 0 0 1) (fromBlocks Q 0 0 1)
      (hP.fromBlocks_diag (isFullG_one _)) (hQ.fromBlocks_diag (isFullG_one _))
      (Sum.elim g 0) (Sum.elim f 0) ?_ ?_ ?_ ?_
    · rintro (i | i) (j | j)
      all_goals simp [fromBlocks_multiply, hA]
    · rintro (i | i) <;> simp [fromBlocks_mulVec, ← Sum.elim_add_add, hu]
    · rintro (i | i) <;> simp [vecMul_fromBlocks, ← Sum.elim_add_add, hx]
    · simp [Disp.add, vecMul_fromBlocks, sumElim_dotProduct_sumElim, ha]; abel
  · intro d d' κ _ G hG C p e hA hu hx ha
    refine Step.up_of κ G hG (fromRows C 0) p
      ((sumSwapRight d.ι c.ι κ).trans (e.sumCongr (Equiv.refl c.ι))) ?_ ?_ ?_ ?_
    · rintro ((i | i) | i) ((j | j) | j) <;> simp [hA]
    · rintro ((i | i) | i) <;> simp [hu]
    · rintro ((i | i) | i) <;> simp [hx]
    · simp [ha]
  · intro d d' κ _ G hG C q e hA hu hx ha
    refine Step.low_of κ G hG (fromCols C 0) q
      ((sumSwapRight d.ι c.ι κ).trans (e.sumCongr (Equiv.refl c.ι))) ?_ ?_ ?_ ?_
    · rintro ((i | i) | i) ((j | j) | j) <;> simp [hA]
    · rintro ((i | i) | i) <;> simp [hu]
    · rintro ((i | i) | i) <;> simp [hx]
    · simp [ha]

theorem Step.add_comm (d c : Disp R) : Step (d.add c) (c.add d) :=
  Step.reindex (Equiv.sumComm d.ι c.ι) (by rintro (i | i) (j | j) <;> rfl)
    (by rintro (i | i) <;> rfl) (by rintro (i | i) <;> rfl) (_root_.add_comm _ _)

theorem Step.neg {d d' : Disp R} (h : Step d d') : Step d.neg d'.neg := by
  refine Step.rec' (motive := fun d d' => Step d.neg d'.neg) ?_ ?_ ?_ h
  · intro d d' e P Q hP hQ g f hA hu hx ha
    refine Step.lin_of e P Q hP hQ (-g) f hA hu ?_ ?_
    · intro j
      change -d'.x (e j) = _
      rw [hx, neg_vecMul, ← neg_add, neg_vecMul, Pi.neg_apply]
    · change -d'.a = _
      rw [ha, neg_vecMul, ← neg_add, neg_dotProduct, neg_dotProduct]
      change _ = _ + _ + -d.a
      abel
  · intro d d' κ _ G hG C p e hA hu hx ha
    refine Step.up_of κ G hG C (-p) e hA hu ?_ (by simp [ha])
    rintro (j | j) <;> simp [hx]
  · intro d d' κ _ G hG C q e hA hu hx ha
    refine Step.low_of κ G hG C q e hA hu ?_ (by simp [ha])
    rintro (j | j) <;> simp [hx]

set_option linter.flexible false in
theorem Step.mul_left {d d' : Disp R} (h : Step d d') (c : Disp R) :
    Step (d.mul c) (d'.mul c) := by
  refine Step.rec' (motive := fun d d' => Step (d.mul c) (d'.mul c)) ?_ ?_ ?_ h
  · intro d d' e P Q hP hQ g f hA hu hx ha
    refine Step.lin_of (e.sumCongr (Equiv.refl c.ι)) (fromBlocks P 0 0 1)
      (fromBlocks Q (of fun i j => f i * c.x j) 0 1)
      (hP.fromBlocks_diag (isFullG_one _)) (isFullG_fromBlocks_upper hQ (isFullG_one _) _)
      (Sum.elim g 0) (Sum.elim (fun i => f i * c.a) 0) ?_ ?_ ?_ ?_
    · rintro (i | i) (j | j) <;> simp [fromBlocks_multiply, hA, hu]
      all_goals (sum_expand; sum_close)
    · rintro (i | i) <;> simp [fromBlocks_mulVec, ← Sum.elim_add_add, hu]
      all_goals sum_expand
    · rintro (i | i) <;> simp [vecMul_fromBlocks, ← Sum.elim_add_add, hx, ha]
      all_goals (sum_expand; sum_close)
    · simp [vecMul_fromBlocks, sumElim_dotProduct_sumElim, ha]
      all_goals sum_expand
  · intro d d' κ _ G hG C p e hA hu hx ha
    refine Step.up_of κ G hG (fromRows C 0) p
      ((sumSwapRight d.ι c.ι κ).trans (e.sumCongr (Equiv.refl c.ι))) ?_ ?_ ?_ ?_
    · rintro ((i | i) | i) ((j | j) | j) <;> simp [hA, hu]
    · rintro ((i | i) | i) <;> simp [hu]
    · rintro ((i | i) | i) <;> simp [hx, ha]
    · simp [ha]
  · intro d d' κ _ G hG C q e hA hu hx ha
    refine Step.low_of κ G hG (fromCols C (of fun k j => q k * c.x j)) (fun k => q k * c.a)
      ((sumSwapRight d.ι c.ι κ).trans (e.sumCongr (Equiv.refl c.ι))) ?_ ?_ ?_ ?_
    · rintro ((i | i) | i) ((j | j) | j) <;> simp [hA, hu]
    · rintro ((i | i) | i) <;> simp [hu]
    · rintro ((i | i) | i) <;> simp [hx, ha]
    · simp [ha]

set_option linter.flexible false in
theorem Step.mul_right {d d' : Disp R} (h : Step d d') (c : Disp R) :
    Step (c.mul d) (c.mul d') := by
  refine Step.rec' (motive := fun d d' => Step (c.mul d) (c.mul d')) ?_ ?_ ?_ h
  · intro d d' e P Q hP hQ g f hA hu hx ha
    refine Step.lin_of ((Equiv.refl c.ι).sumCongr e) (fromBlocks 1 (of fun k i => c.u k * g i) 0 P)
      (fromBlocks 1 0 0 Q)
      (isFullG_fromBlocks_upper (isFullG_one _) hP _) ((isFullG_one _).fromBlocks_diag hQ)
      (Sum.elim 0 (fun i => c.a * g i)) (Sum.elim 0 f) ?_ ?_ ?_ ?_
    · rintro (i | i) (j | j) <;> simp [fromBlocks_multiply, hA, hx]
      all_goals (sum_expand; sum_close)
    · rintro (i | i) <;> simp [fromBlocks_mulVec, ← Sum.elim_add_add, hu, ha]
      all_goals (sum_expand; sum_close)
    · rintro (i | i) <;> simp [vecMul_fromBlocks, ← Sum.elim_add_add, hx]
      all_goals sum_expand
    · simp [vecMul_fromBlocks, sumElim_dotProduct_sumElim, ha]
      all_goals sum_expand
  · intro d d' κ _ G hG C p e hA hu hx ha
    refine Step.up_of κ G hG (fromRows (of fun k l => c.u k * p l) C) (fun l => c.a * p l)
      ((Equiv.sumAssoc c.ι d.ι κ).trans ((Equiv.refl c.ι).sumCongr e)) ?_ ?_ ?_ ?_
    · rintro ((i | i) | i) ((j | j) | j) <;> simp [hA, hx]
    · rintro ((i | i) | i) <;> simp [hu, ha]
    · rintro ((i | i) | i) <;> simp [hx]
    · simp [ha]
  · intro d d' κ _ G hG C q e hA hu hx ha
    refine Step.low_of κ G hG (fromCols 0 C) q
      ((Equiv.sumAssoc c.ι d.ι κ).trans ((Equiv.refl c.ι).sumCongr e)) ?_ ?_ ?_ ?_
    · rintro ((i | i) | i) ((j | j) | j) <;> simp [hA, hx]
    · rintro ((i | i) | i) <;> simp [hu, ha]
    · rintro ((i | i) | i) <;> simp [hx]
    · simp [ha]

theorem add_comm_step (d c : Disp R) : Step (d.add c) (c.add d) := Step.add_comm d c

end Compat

/-! ## Removal constructors -/

section Removal

/-- Removing an upper trivial block: `d'` is `d` with an extra block `κ` whose rows vanish
outside `κ` (including the last column) and whose diagonal block is full. -/
theorem Step.removeUp {d d' : Disp R} (κ : Type) [Fintype κ]
    (e : d.ι ⊕ κ ≃ d'.ι) (hG : IsFullG (of fun k l => d'.A (e (.inr k)) (e (.inr l))))
    (hA : ∀ i j, d'.A (e (.inl i)) (e (.inl j)) = d.A i j)
    (h0 : ∀ k j, d'.A (e (.inr k)) (e (.inl j)) = 0)
    (hu : ∀ i, d'.u (e (.inl i)) = d.u i) (hu0 : ∀ k, d'.u (e (.inr k)) = 0)
    (hx : ∀ j, d'.x (e (.inl j)) = d.x j) (ha : d'.a = d.a) : Step d d' :=
  Step.up_of κ _ hG (of fun i k => d'.A (e (.inl i)) (e (.inr k))) (fun k => d'.x (e (.inr k))) e
    (by rintro (i | i) (j | j) <;> simp [hA, h0]) (by rintro (i | i) <;> simp [hu, hu0])
    (by rintro (i | i) <;> simp [hx]) ha

/-- Removing a lower trivial block: `d'` is `d` with an extra block `κ` whose columns vanish
outside `κ` (including the last row) and whose diagonal block is full. -/
theorem Step.removeLow {d d' : Disp R} (κ : Type) [Fintype κ]
    (e : d.ι ⊕ κ ≃ d'.ι) (hG : IsFullG (of fun k l => d'.A (e (.inr k)) (e (.inr l))))
    (hA : ∀ i j, d'.A (e (.inl i)) (e (.inl j)) = d.A i j)
    (h0 : ∀ i k, d'.A (e (.inl i)) (e (.inr k)) = 0)
    (hu : ∀ i, d'.u (e (.inl i)) = d.u i)
    (hx : ∀ j, d'.x (e (.inl j)) = d.x j) (hx0 : ∀ k, d'.x (e (.inr k)) = 0)
    (ha : d'.a = d.a) : Step d d' :=
  Step.low_of κ _ hG (of fun k j => d'.A (e (.inr k)) (e (.inl j))) (fun k => d'.u (e (.inr k))) e
    (by rintro (i | i) (j | j) <;> simp [hA, h0]) (by rintro (i | i) <;> simp [hu])
    (by rintro (i | i) <;> simp [hx, hx0]) ha

end Removal

/-! ## The image of a `lin` step -/

section LinMap

variable [FullClosed R]

/-- The display `[[P, 0], [g, 1]] · d · [[Q, f], [0, 1]]` (same index type). -/
@[reducible] def Disp.linMap (d : Disp R) (P Q : Matrix d.ι d.ι R) (hP : IsFullG P)
    (hQ : IsFullG Q) (g f : d.ι → R) : Disp R where
  ι := d.ι
  A := P * d.A * Q
  u := P *ᵥ (d.A *ᵥ f + d.u)
  x := (g ᵥ* d.A + d.x) ᵥ* Q
  a := (g ᵥ* d.A + d.x) ⬝ᵥ f + g ⬝ᵥ d.u + d.a
  full := (hP.mul d.full).mul hQ

theorem Step.linMap (d : Disp R) (P Q : Matrix d.ι d.ι R) (hP : IsFullG P)
    (hQ : IsFullG Q) (g f : d.ι → R) : Step d (d.linMap P Q hP hQ g f) :=
  Step.lin_of (Equiv.refl _) P Q hP hQ g f (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl

/-- `[[1, C], [0, 1]]` is full. -/
theorem isFullG_unitUpper {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (C : Matrix ι κ R) : IsFullG (fromBlocks (1 : Matrix ι ι R) C 0 1) :=
  isFullG_fromBlocks_upper (isFullG_one _) (isFullG_one _) C

end LinMap

/-! ## The display model `M R` -/

/-- Cohn's display ring `M(Φ)` (FIR §7.4), as a type: displays modulo the equivalence generated
by `Step`.  The ring structure is built in `DisplayRing.lean`. -/
def M (R : Type u) [Ring R] [FullClosed R] : Type (max u 1) := Quot (Step (R := R))

namespace M

variable [FullClosed R]

/-- The class of a display. -/
def mk (d : Disp R) : M R := Quot.mk _ d

theorem mk_eq_of_step {d d' : Disp R} (h : Step d d') : mk d = mk d' := Quot.sound h

@[elab_as_elim]
theorem ind {P : M R → Prop} (h : ∀ d, P (mk d)) (q : M R) : P q := Quot.ind h q

theorem add_left_compat {d d' : Disp R} (h : Step d d') (c : Disp R) :
    mk (d.add c) = mk (d'.add c) := mk_eq_of_step (h.add_left c)

theorem add_right_compat {d d' : Disp R} (h : Step d d') (c : Disp R) :
    mk (c.add d) = mk (c.add d') := by
  rw [mk_eq_of_step (Step.add_comm c d), add_left_compat h c, mk_eq_of_step (Step.add_comm d' c)]

theorem mul_left_compat {d d' : Disp R} (h : Step d d') (c : Disp R) :
    mk (d.mul c) = mk (d'.mul c) := mk_eq_of_step (h.mul_left c)

theorem mul_right_compat {d d' : Disp R} (h : Step d d') (c : Disp R) :
    mk (c.mul d) = mk (c.mul d') := mk_eq_of_step (h.mul_right c)

theorem neg_compat {d d' : Disp R} (h : Step d d') : mk d.neg = mk d'.neg :=
  mk_eq_of_step h.neg

instance : Zero (M R) := ⟨mk (Disp.scalar 0)⟩
instance : One (M R) := ⟨mk (Disp.scalar 1)⟩
instance : Add (M R) :=
  ⟨Quot.lift₂ (fun d c => mk (d.add c)) (fun c _ _ h => add_right_compat h c)
    (fun _ _ c h => add_left_compat h c)⟩
instance : Mul (M R) :=
  ⟨Quot.lift₂ (fun d c => mk (d.mul c)) (fun c _ _ h => mul_right_compat h c)
    (fun _ _ c h => mul_left_compat h c)⟩
instance : Neg (M R) := ⟨Quot.lift (fun d => mk d.neg) (fun _ _ h => neg_compat h)⟩

theorem zero_def : (0 : M R) = mk (Disp.scalar 0) := rfl
theorem one_def : (1 : M R) = mk (Disp.scalar 1) := rfl
@[simp] theorem mk_add_mk (d c : Disp R) : mk d + mk c = mk (d.add c) := rfl
@[simp] theorem mk_mul_mk (d c : Disp R) : mk d * mk c = mk (d.mul c) := rfl
@[simp] theorem neg_mk (d : Disp R) : -mk d = mk d.neg := rfl

/-- "The display matrix is full" — well defined on `M R` by the fullness invariant. -/
def fullPred : M R → Prop :=
  Quot.lift (fun d => IsFullG d.mat) (fun _ _ h => propext h.isFullG_mat_iff)

@[simp] theorem fullPred_mk (d : Disp R) : fullPred (mk d) ↔ IsFullG d.mat := Iff.rfl

theorem isFullG_scalar_mat_iff (r : R) : IsFullG (Disp.scalar r).mat ↔ r ≠ 0 := by
  rw [← isFullG_reindex_iff (Equiv.emptySum Empty Unit), ← isFullG_unit_iff]
  exact Iff.of_eq (congrArg IsFullG (by ext i j; rfl))

theorem fullPred_scalar (r : R) : fullPred (mk (Disp.scalar r)) ↔ r ≠ 0 :=
  isFullG_scalar_mat_iff r

theorem fullPred_one : fullPred (1 : M R) := (fullPred_scalar 1).2 one_ne_zero

theorem not_fullPred_zero : ¬ fullPred (0 : M R) := fun h => (fullPred_scalar 0).1 h rfl

/-- **Nontriviality of the display model**: `0 ≠ 1` in `M R`. -/
theorem zero_ne_one : (0 : M R) ≠ 1 := fun h => not_fullPred_zero (h ▸ fullPred_one)

/-! ### Ring-axiom chains -/

theorem add_assoc' (a b c : M R) : a + b + c = a + (b + c) := by
  induction a using M.ind with | h d => induction b using M.ind with | h e =>
  induction c using M.ind with | h f =>
  exact mk_eq_of_step <| Step.reindex (Equiv.sumAssoc d.ι e.ι f.ι)
    (by rintro ((i | i) | i) ((j | j) | j) <;> rfl) (by rintro ((i | i) | i) <;> rfl)
    (by rintro ((i | i) | i) <;> rfl) (by simp [_root_.add_assoc])

theorem add_comm' (a b : M R) : a + b = b + a := by
  induction a using M.ind with | h d => induction b using M.ind with | h e =>
  exact mk_eq_of_step (Step.add_comm d e)

theorem zero_add' (a : M R) : 0 + a = a := by
  induction a using M.ind with | h d =>
  exact mk_eq_of_step <| Step.reindex (Equiv.emptySum Empty d.ι)
    (by rintro (i | i) (j | j) <;> first | exact i.elim | exact j.elim | rfl)
    (by rintro (i | i) <;> first | exact i.elim | rfl)
    (by rintro (i | i) <;> first | exact i.elim | rfl) (by simp)

theorem add_zero' (a : M R) : a + 0 = a := by
  rw [add_comm', zero_add']

theorem mul_assoc' (a b c : M R) : a * b * c = a * (b * c) := by
  induction a using M.ind with | h d => induction b using M.ind with | h e =>
  induction c using M.ind with | h f =>
  exact mk_eq_of_step <| Step.reindex (Equiv.sumAssoc d.ι e.ι f.ι)
    (by rintro ((i | i) | i) ((j | j) | j) <;> simp [_root_.mul_assoc])
    (by rintro ((i | i) | i) <;> simp [_root_.mul_assoc])
    (by rintro ((i | i) | i) <;> simp [_root_.mul_assoc]) (by simp [_root_.mul_assoc])

theorem one_mul' (a : M R) : 1 * a = a := by
  induction a using M.ind with | h d =>
  exact mk_eq_of_step <| Step.reindex (Equiv.emptySum Empty d.ι)
    (by rintro (i | i) (j | j) <;> first | exact i.elim | exact j.elim | rfl)
    (by rintro (i | i) <;> first | exact i.elim | rfl)
    (by rintro (i | i) <;> first | exact i.elim | simp) (by simp)

theorem mul_one' (a : M R) : a * 1 = a := by
  induction a using M.ind with | h d =>
  exact mk_eq_of_step <| Step.reindex (Equiv.sumEmpty d.ι Empty)
    (by rintro (i | i) (j | j) <;> first | exact i.elim | exact j.elim | rfl)
    (by rintro (i | i) <;> first | exact i.elim | simp)
    (by rintro (i | i) <;> first | exact i.elim | rfl) (by simp)

theorem zero_mul' (a : M R) : 0 * a = 0 := by
  induction a using M.ind with | h d =>
  refine (mk_eq_of_step ?_).symm
  exact Step.removeLow d.ι (Equiv.refl _) d.full (fun i => i.elim) (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim) (fun k => by simp) (by simp)

theorem mul_zero' (a : M R) : a * 0 = 0 := by
  induction a using M.ind with | h d =>
  refine (mk_eq_of_step ?_).symm
  exact Step.removeUp d.ι (Equiv.sumComm _ _) d.full (fun i => i.elim) (fun _ j => j.elim)
    (fun i => i.elim) (fun k => by simp) (fun i => i.elim) (by simp)

/-- `[[A, 0, 0], [0, A, u], [-x, 0, 0]]`, the middle stage of `neg_add_cancel`. -/
@[reducible] def negAddAux (d : Disp R) : Disp R where
  ι := d.ι ⊕ d.ι
  A := fromBlocks d.A 0 0 d.A
  u := Sum.elim 0 d.u
  x := Sum.elim (-d.x) 0
  a := 0
  full := d.full.fromBlocks_diag d.full

/-- `[[A, u], [0, 0]]`. -/
@[reducible] def zeroAux (d : Disp R) : Disp R where
  ι := d.ι
  A := d.A
  u := d.u
  x := 0
  a := 0
  full := d.full

theorem neg_add_cancel' (a : M R) : -a + a = 0 := by
  induction a using M.ind with | h d =>
  have h1 : Step (d.neg.add d) (negAddAux d) := by
    refine Step.lin_of (Equiv.refl _) (fromBlocks 1 (-1) 0 1) (fromBlocks 1 1 0 1)
      (isFullG_fromBlocks_upper (isFullG_one _) (isFullG_one _) _)
      (isFullG_fromBlocks_upper (isFullG_one _) (isFullG_one _) _) 0 0 ?_ ?_ ?_ ?_
    · rintro (i | i) (j | j) <;> simp [negAddAux, fromBlocks_multiply]
    · rintro (i | i) <;> simp [negAddAux, fromBlocks_mulVec, Matrix.neg_mulVec]
    · rintro (i | i) <;> simp [negAddAux, vecMul_fromBlocks]
    · simp
  have h2 : Step (zeroAux d) (negAddAux d) :=
    Step.removeUp d.ι (Equiv.sumComm _ _) d.full (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl
  have h3 : Step (Disp.scalar 0) (zeroAux d) :=
    Step.removeLow d.ι (Equiv.emptySum _ _) d.full (fun i => i.elim) (fun i => i.elim)
      (fun i => i.elim) (fun i => i.elim) (fun _ => rfl) rfl
  change mk (d.neg.add d) = mk (Disp.scalar 0)
  rw [mk_eq_of_step h1, ← mk_eq_of_step h2, ← mk_eq_of_step h3]

/-- Reindexing used by right distributivity. -/
def rdEquiv (α β γ : Type) : ((α ⊕ β) ⊕ γ) ⊕ γ ≃ (α ⊕ γ) ⊕ (β ⊕ γ) where
  toFun
    | .inl (.inl (.inl i)) => .inl (.inl i)
    | .inl (.inl (.inr j)) => .inr (.inl j)
    | .inl (.inr k) => .inr (.inr k)
    | .inr k => .inl (.inr k)
  invFun
    | .inl (.inl i) => .inl (.inl (.inl i))
    | .inr (.inl j) => .inl (.inl (.inr j))
    | .inr (.inr k) => .inl (.inr k)
    | .inl (.inr k) => .inr k
  left_inv := by rintro (((i | i) | i) | i) <;> rfl
  right_inv := by rintro ((i | i) | (i | i)) <;> rfl

theorem right_distrib' (a b c : M R) : (a + b) * c = a * c + b * c := by
  induction a using M.ind with | h d => induction b using M.ind with | h e =>
  induction c using M.ind with | h f =>
  set D := (d.mul f).add (e.mul f)
  have h1 := Step.linMap D (fromBlocks 1 (fromBlocks 0 0 0 (-1)) 0 1)
    (fromBlocks 1 (fromBlocks 0 0 0 1) 0 1) (isFullG_unitUpper _) (isFullG_unitUpper _) 0 0
  have h2 : Step ((d.add e).mul f) (D.linMap _ _ (isFullG_unitUpper (fromBlocks 0 0 0 (-1)))
      (isFullG_unitUpper (fromBlocks 0 0 0 1)) 0 0) := by
    refine Step.removeUp f.ι (rdEquiv d.ι e.ι f.ι) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · convert f.full using 1
      ext k l
      simp [D, rdEquiv, fromBlocks_multiply]
    · rintro ((i | i) | i) ((j | j) | j) <;>
        simp [D, rdEquiv, fromBlocks_multiply]
    · rintro k ((j | j) | j) <;> simp [D, rdEquiv, fromBlocks_multiply]
    · rintro ((i | i) | i) <;> simp [D, rdEquiv, fromBlocks_mulVec]
    · intro k; simp [D, rdEquiv, fromBlocks_mulVec, Matrix.neg_mulVec]
    · rintro ((i | i) | i) <;> simp [D, rdEquiv, vecMul_fromBlocks, add_mul]
    · simp [D, add_mul]
  change mk ((d.add e).mul f) = mk D
  rw [mk_eq_of_step h1, mk_eq_of_step h2]

/-- Reindexing used by left distributivity. -/
def ldEquiv (α β γ : Type) : (α ⊕ (β ⊕ γ)) ⊕ α ≃ (α ⊕ β) ⊕ (α ⊕ γ) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr (.inl j)) => .inl (.inr j)
    | .inl (.inr (.inr k)) => .inr (.inr k)
    | .inr i => .inr (.inl i)
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr j) => .inl (.inr (.inl j))
    | .inr (.inr k) => .inl (.inr (.inr k))
    | .inr (.inl i) => .inr i
  left_inv := by rintro ((i | i | i) | i) <;> rfl
  right_inv := by rintro ((i | i) | (i | i)) <;> rfl

/-- Left distributivity — **not written out in Cohn** (FIR p. 440: "follows similarly").
Chain: in `de + df` do `col d' -= col d`, `row d += row d'` (one `lin` step); then block `d'`
has zero column and arbitrary row, so a (generalized) low-removal leaves `d(e + f)`. -/
theorem left_distrib' (a b c : M R) : a * (b + c) = a * b + a * c := by
  induction a using M.ind with | h d => induction b using M.ind with | h e =>
  induction c using M.ind with | h f =>
  set D := (d.mul e).add (d.mul f)
  have h1 := Step.linMap D (fromBlocks 1 (fromBlocks 1 0 0 0) 0 1)
    (fromBlocks 1 (fromBlocks (-1) 0 0 0) 0 1) (isFullG_unitUpper _) (isFullG_unitUpper _) 0 0
  have h2 : Step (d.mul (e.add f)) (D.linMap _ _ (isFullG_unitUpper (fromBlocks 1 0 0 0))
      (isFullG_unitUpper (fromBlocks (-1) 0 0 0)) 0 0) := by
    refine Step.removeLow d.ι (ldEquiv d.ι e.ι f.ι) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · convert d.full using 1
      ext k l
      simp [D, ldEquiv, fromBlocks_multiply]
    · rintro (i | i | i) (j | j | j) <;>
        simp [D, ldEquiv, fromBlocks_multiply]
    · rintro (i | i | i) k <;> simp [D, ldEquiv, fromBlocks_multiply]
    · rintro (i | i | i) <;> simp [D, ldEquiv, fromBlocks_mulVec, mul_add]
    · rintro (i | i | i) <;> simp [D, ldEquiv, vecMul_fromBlocks]
    · intro k; simp [D, ldEquiv, vecMul_fromBlocks, Matrix.vecMul_neg]
    · simp [D, mul_add]
  change mk (d.mul (e.add f)) = mk D
  rw [mk_eq_of_step h1, mk_eq_of_step h2]

/-- `M R` is a ring (Cohn FIR §7.4 p. 439–440). -/
instance instRing : Ring (M R) where
  add_assoc := add_assoc'
  zero_add := zero_add'
  add_zero := add_zero'
  add_comm := add_comm'
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  neg_add_cancel := neg_add_cancel'
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Nontrivial (M R) := ⟨⟨0, 1, zero_ne_one⟩⟩

theorem mk_scalar_add (r s : R) :
    mk (Disp.scalar (r + s)) = mk (Disp.scalar r) + mk (Disp.scalar s) :=
  mk_eq_of_step <| Step.reindex (Equiv.emptySum Empty Empty).symm (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim) rfl

theorem mk_scalar_mul (r s : R) :
    mk (Disp.scalar (r * s)) = mk (Disp.scalar r) * mk (Disp.scalar s) :=
  mk_eq_of_step <| Step.reindex (Equiv.emptySum Empty Empty).symm (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim) rfl

/-- The canonical map `R → M R`, `r ↦ [(r)]`. -/
def ofR : R →+* M R where
  toFun r := mk (Disp.scalar r)
  map_one' := rfl
  map_mul' := mk_scalar_mul
  map_zero' := rfl
  map_add' := mk_scalar_add

theorem ofR_apply (r : R) : ofR r = mk (Disp.scalar r) := rfl

/-! ### The full-inverting property -/

theorem one_apply_eq_ofR {ι : Type} [DecidableEq ι] (i j : ι) :
    (1 : Matrix ι ι (M R)) i j = ofR ((1 : Matrix ι ι R) i j) := by
  rw [← Matrix.map_one (ofR (R := R)) ofR.map_zero ofR.map_one]; rfl

section Inverting

variable {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R) (hA : IsFullG A)

/-- The display `[[A, u], [x, a]]` on a given index type. -/
@[reducible] def dispOf (u x : ι → R) (a : R) : Disp R := ⟨ι, A, u, x, a, hA⟩

theorem mk_dispOf_zero_row (u : ι → R) : mk (dispOf A hA u 0 0) = 0 :=
  (mk_eq_of_step (Step.removeLow (d := Disp.scalar 0) (d' := dispOf A hA u 0 0) ι
    (Equiv.emptySum Empty ι) hA (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun _ => rfl) rfl)).symm

theorem mk_dispOf_zero_col (x : ι → R) : mk (dispOf A hA 0 x 0) = 0 :=
  (mk_eq_of_step (Step.removeUp (d := Disp.scalar 0) (d' := dispOf A hA 0 x 0) ι
    (Equiv.emptySum Empty ι) hA (fun i => i.elim)
    (fun _ j => j.elim) (fun i => i.elim) (fun _ => rfl) (fun i => i.elim) rfl)).symm

/-- **Row merging**: `[[A, u], [x, a]] + [[A, u], [y, b]] ~ [[A, u], [x + y, a + b]]`. -/
theorem mk_dispOf_add_row (u x y : ι → R) (a b : R) :
    mk (dispOf A hA u x a) + mk (dispOf A hA u y b) = mk (dispOf A hA u (x + y) (a + b)) := by
  set D := (dispOf A hA u x a).add (dispOf A hA u y b)
  have h1 := Step.linMap D (fromBlocks 1 (-1) 0 1) (fromBlocks 1 1 0 1)
    (isFullG_unitUpper _) (isFullG_unitUpper _) 0 0
  have h2 : Step (dispOf A hA u (x + y) (a + b)) (D.linMap _ _ (isFullG_unitUpper (-1))
      (isFullG_unitUpper 1) 0 0) := by
    refine Step.removeUp ι (Equiv.sumComm ι ι) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · convert hA using 1; ext k l; simp [D, fromBlocks_multiply]
    · intro i j; simp [D, fromBlocks_multiply]
    · intro k j; simp [D, fromBlocks_multiply]
    · intro i; simp [D, fromBlocks_mulVec]
    · intro k; simp [D, fromBlocks_mulVec, Matrix.neg_mulVec]
    · intro j; simp [D, vecMul_fromBlocks, _root_.add_comm]
    · simp [D]
  change mk D = _
  rw [mk_eq_of_step h1, ← mk_eq_of_step h2]

/-- **Column merging**: `[[A, u], [x, a]] + [[A, v], [x, b]] ~ [[A, u + v], [x, a + b]]`. -/
theorem mk_dispOf_add_col (u v x : ι → R) (a b : R) :
    mk (dispOf A hA u x a) + mk (dispOf A hA v x b) = mk (dispOf A hA (u + v) x (a + b)) := by
  set D := (dispOf A hA u x a).add (dispOf A hA v x b)
  have h1 := Step.linMap D (fromBlocks 1 1 0 1) (fromBlocks 1 (-1) 0 1)
    (isFullG_unitUpper _) (isFullG_unitUpper _) 0 0
  have h2 : Step (dispOf A hA (u + v) x (a + b)) (D.linMap _ _ (isFullG_unitUpper 1)
      (isFullG_unitUpper (-1)) 0 0) := by
    refine Step.removeLow ι (Equiv.refl _) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · convert hA using 1; ext k l; simp [D, fromBlocks_multiply]
    · intro i j; simp [D, fromBlocks_multiply]
    · intro i k; simp [D, fromBlocks_multiply]
    · intro i; simp [D, fromBlocks_mulVec]
    · intro j; simp [D, vecMul_fromBlocks]
    · intro k; simp [D, vecMul_fromBlocks, Matrix.vecMul_neg]
    · simp [D]
  change mk D = _
  rw [mk_eq_of_step h1, ← mk_eq_of_step h2]

/-- For fixed `A, u`, the map `(x, a) ↦ [[A, u], [x, a]]` is additive. -/
def rowHom (u : ι → R) : (ι → R) × R →+ M R where
  toFun p := mk (dispOf A hA u p.1 p.2)
  map_zero' := mk_dispOf_zero_row A hA u
  map_add' p q := (mk_dispOf_add_row A hA u p.1 q.1 p.2 q.2).symm

/-- For fixed `A, x`, the map `(u, a) ↦ [[A, u], [x, a]]` is additive. -/
def colHom (x : ι → R) : (ι → R) × R →+ M R where
  toFun p := mk (dispOf A hA p.1 x p.2)
  map_zero' := mk_dispOf_zero_col A hA x
  map_add' p q := (mk_dispOf_add_col A hA p.1 q.1 x p.2 q.2).symm

theorem sum_mk_dispOf_row {κ : Type*} (s : Finset κ) (u : ι → R) (x : κ → ι → R) (a : κ → R) :
    ∑ k ∈ s, mk (dispOf A hA u (x k) (a k)) =
      mk (dispOf A hA u (∑ k ∈ s, x k) (∑ k ∈ s, a k)) := by
  change ∑ k ∈ s, rowHom A hA u (x k, a k) = rowHom A hA u (∑ k ∈ s, x k, ∑ k ∈ s, a k)
  rw [← map_sum]
  congr 1
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

theorem sum_mk_dispOf_col {κ : Type*} (s : Finset κ) (x : ι → R) (u : κ → ι → R) (a : κ → R) :
    ∑ k ∈ s, mk (dispOf A hA (u k) x (a k)) =
      mk (dispOf A hA (∑ k ∈ s, u k) x (∑ k ∈ s, a k)) := by
  change ∑ k ∈ s, colHom A hA x (u k, a k) = colHom A hA x (∑ k ∈ s, u k, ∑ k ∈ s, a k)
  rw [← map_sum]
  congr 1
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

theorem ofR_mul_mk_dispOf (c : R) (u x : ι → R) (a : R) :
    ofR c * mk (dispOf A hA u x a) = mk (dispOf A hA u (fun i => c * x i) (c * a)) :=
  (mk_eq_of_step <| Step.reindex (d := dispOf A hA u (fun i => c * x i) (c * a))
    (d' := (Disp.scalar c).mul (dispOf A hA u x a)) (Equiv.emptySum Empty ι).symm
    (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl).symm

theorem mk_dispOf_mul_ofR (c : R) (u x : ι → R) (a : R) :
    mk (dispOf A hA u x a) * ofR c = mk (dispOf A hA (fun i => u i * c) x (a * c)) :=
  (mk_eq_of_step <| Step.reindex (d := dispOf A hA (fun i => u i * c) x (a * c))
    (d' := (dispOf A hA u x a).mul (Disp.scalar c)) (Equiv.sumEmpty ι Empty).symm
    (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl) rfl).symm

/-- The candidate inverse: `W i j = [[A, -eⱼ], [eᵢᵀ, 0]]` (FIR p. 440). -/
def invDisp (i j : ι) : M R := mk (dispOf A hA (-Pi.single j 1) (Pi.single i 1) 0)

theorem map_ofR_mul_invDisp : A.map ofR * of (invDisp A hA) = 1 := by
  ext i j
  simp only [mul_apply, map_apply, of_apply, invDisp, ofR_mul_mk_dispOf, mul_zero,
    sum_mk_dispOf_row, Finset.sum_const_zero]
  rw [one_apply_eq_ofR, ofR_apply]
  -- row operation with `g = -eᵢ`, then remove the (now low-trivial) block `A`
  set D := dispOf A hA (-Pi.single j 1) (∑ k, fun l => A i k * Pi.single (M := fun _ => R) k 1 l) 0
  refine (mk_eq_of_step (Step.linMap D 1 1 (isFullG_one _) (isFullG_one _)
    (-Pi.single i 1) 0)).trans (mk_eq_of_step ?_).symm
  refine Step.removeLow (d := Disp.scalar _) ι (Equiv.emptySum Empty ι)
    (by convert hA using 1; ext; simp [D]) (fun i => i.elim)
    (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim) ?_ ?_
  · intro k
    simp [D, Finset.sum_apply, Pi.single_apply, vecMul, dotProduct]
  · simp [D, one_apply, Pi.single_apply, dotProduct, eq_comm]

theorem invDisp_mul_map_ofR : of (invDisp A hA) * A.map ofR = 1 := by
  ext i j
  simp only [mul_apply, map_apply, of_apply, invDisp, mk_dispOf_mul_ofR, zero_mul,
    sum_mk_dispOf_col, Finset.sum_const_zero]
  rw [one_apply_eq_ofR, ofR_apply]
  set D := dispOf A hA (∑ k, fun l => (-Pi.single (M := fun _ => R) k 1) l * A k j)
    (Pi.single i 1) 0
  refine (mk_eq_of_step (Step.linMap D 1 1 (isFullG_one _) (isFullG_one _)
    0 (Pi.single j 1))).trans (mk_eq_of_step ?_).symm
  refine Step.removeUp (d := Disp.scalar _) ι (Equiv.emptySum Empty ι)
    (by convert hA using 1; ext; simp [D]) (fun i => i.elim)
    (fun _ j => j.elim)
    (fun i => i.elim) ?_ (fun i => i.elim) ?_
  · intro k
    simp [D, Finset.sum_apply, Pi.single_apply, mulVec, dotProduct]
  · simp [D, one_apply, Pi.single_apply, dotProduct, eq_comm]

end Inverting

theorem isUnit_map_ofR_of_isFullG {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R)
    (hA : IsFullG A) : IsUnit (A.map (ofR (R := R))) :=
  ⟨⟨A.map ofR, of (invDisp A hA), map_ofR_mul_invDisp A hA, invDisp_mul_map_ofR A hA⟩, rfl⟩

/-- **`R → M R` is full-inverting.** -/
theorem isUnit_map_ofR {n : ℕ} {A : Matrix (Fin n) (Fin n) R} (hA : IsFull A) :
    IsUnit (A.map (ofR (R := R))) :=
  isUnit_map_ofR_of_isFullG A ((isFullG_iff_isFull A).2 hA)

theorem one_ne_zero_M : (1 : M R) ≠ 0 := fun h => zero_ne_one h.symm

end M

/-- **Nontriviality of the universal localization at the full matrices** (Cohn FIR Thm 7.4.2,
with Malcolmson's criterion replaced by the fullness invariant).  The lift
`R_Φ → M R` of the full-inverting `M.ofR` sends `0 ↦ 0` and `1 ↦ 1`, and `0 ≠ 1` in `M R`.
This is `Nontrivial (FullLoc R)` for `FullLoc R := UnivLoc.Loc (fun n A => IsFull A)`. -/
theorem nontrivial_loc_isFull [FullClosed R] :
    Nontrivial (UnivLoc.Loc (fun n (A : Matrix (Fin n) (Fin n) R) => IsFull A)) :=
  ⟨⟨0, 1, fun h => (M.zero_ne_one (R := R)) (by
    simpa using congrArg (UnivLoc.lift (Sig := fun n (A : Matrix (Fin n) (Fin n) R) => IsFull A)
      (M.ofR (R := R)) (fun _ _ hA => M.isUnit_map_ofR hA)) h)⟩⟩

end LeftPCI.FreeField.Display
