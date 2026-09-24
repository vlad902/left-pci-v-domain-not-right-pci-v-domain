import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Group.Units.Opposite
import Mathlib.Algebra.Ring.Opposite
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# PCI rings and V-domains are not left-right symmetric

*Reference:* `paper/pci_counterexample.tex` (Main Theorem = Theorem 1.1, Corollary 5.3).

A ring `R` is a **left PCI ring** if every proper cyclic left `R`-module (a cyclic module not
isomorphic to `R`) is injective, and a **left V-ring** if every simple left `R`-module is
injective; the right-handed notions are the left-handed ones for the opposite ring. Whether every
right PCI ring is left PCI has been open since Faith (1973), and whether every left V-domain is
a right V-domain goes back to Cozzens–Faith (1975) and is restated as open by Jain–Lam–Leroy
(2009).

Both have negative answers: there is a countable domain (an Ore extension `K̃[t; σ̃, δ̃]` over a
countable division ring built from Cohn's free fields) which is a left PCI ring and a left V-ring,
but is not right Ore, not a right PCI ring and not a right V-ring. Its opposite ring is a right
PCI ring which is not left PCI.

This file is the statement surface a reader should audit: the definitions below and the three
theorems at the end are the compared declarations. They are proved in `Solution.lean` and the
modules it imports (`LeftPCI.Counterexample.Closure`); only the theorems' `sorry`s are filled in
there, and the definitions there (`LeftPCI.Counterexample.Defs`) are literally identical.
-/

universe u

namespace LeftPCI

/-- A ring is a **left PCI ring** ("proper cyclics are injective") if every proper cyclic left
module — a quotient `R ⧸ I` of `R` by a left ideal `I` (`Ideal R = Submodule R R`) which is not
isomorphic to `R` as a left `R`-module — is an injective `R`-module. -/
def IsLeftPCIRing (R : Type u) [Ring R] : Prop :=
  ∀ I : Ideal R, ¬ Nonempty ((R ⧸ I) ≃ₗ[R] R) → Module.Injective R (R ⧸ I)

/-- A ring is a **right PCI ring** if its opposite ring is a left PCI ring: right `R`-modules
are left `Rᵐᵒᵖ`-modules, so this is the right-handed version of `IsLeftPCIRing`. -/
def IsRightPCIRing (R : Type u) [Ring R] : Prop :=
  IsLeftPCIRing Rᵐᵒᵖ

/-- A ring is a **left V-ring** if every simple left `R`-module is injective. -/
def IsLeftVRing (R : Type u) [Ring R] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M], IsSimpleModule R M → Module.Injective R M

/-- A ring is a **right V-ring** if its opposite ring is a left V-ring. -/
def IsRightVRing (R : Type u) [Ring R] : Prop :=
  IsLeftVRing Rᵐᵒᵖ

/-- A domain is **right Ore** if any two non-zero elements have a non-zero common right
multiple: `a R ∩ b R ≠ 0`. For a ring that is not a domain this is not the general right Ore
condition, which is stated for regular elements; it is only used here together with `IsDomain`. -/
def IsRightOre (R : Type u) [Ring R] : Prop :=
  ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ x y : R, a * x = b * y ∧ a * x ≠ 0

/-- **Main Theorem** (Theorem 1.1 of the paper): a countable domain which is a left PCI ring and a
left V-ring but is not right Ore, not a right PCI ring and not a right V-ring. -/
theorem exists_isLeftPCIRing_not_isRightPCIRing :
    ∃ (R : Type) (_ : Ring R), IsDomain R ∧ Countable R ∧ IsLeftPCIRing R ∧ IsLeftVRing R ∧
      ¬ IsRightOre R ∧ ¬ IsRightPCIRing R ∧ ¬ IsRightVRing R := by
  sorry

/-- A left PCI ring need not be right PCI: the Main Theorem's example. Passing to the opposite
ring, this is Corollary 5.3 (1) of the paper, that a right PCI ring need not be left PCI. -/
theorem not_forall_isLeftPCIRing_imp_isRightPCIRing :
    ¬ ∀ (R : Type) [Ring R], IsLeftPCIRing R → IsRightPCIRing R := by
  sorry

/-- A left V-domain need not be a right V-domain (Corollary 5.3 (3)). -/
theorem not_forall_isLeftVRing_imp_isRightVRing :
    ¬ ∀ (R : Type) [Ring R], IsDomain R → IsLeftVRing R → IsRightVRing R := by
  sorry

end LeftPCI
