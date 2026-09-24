module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Group.Units.Opposite
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# PCI rings, V-rings and the right Ore condition

The ring-theoretic notions in the statement of the Main Theorem of the paper
`paper/pci_counterexample.tex`, in plain Mathlib terms. Left modules are Mathlib's modules, left
ideals are `Ideal R = Submodule R R`, and the right-handed notions are the left-handed ones for the
opposite ring `Rᵐᵒᵖ`.

These definitions are literally identical to the ones in `Challenge.lean`.
-/

@[expose] public section

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

end LeftPCI
