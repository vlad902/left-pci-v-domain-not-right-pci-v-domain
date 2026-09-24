module

public import LeftPCI.FreeField.Interface
public import LeftPCI.FreeField.Cramer
public import LeftPCI.FreeField.Sylvester
public import LeftPCI.FreeField.DisplayModel

@[expose] public section

namespace LeftPCI.FreeField

universe u v

/-! # Assembly: the universal field of fractions

For a ring `R` whose full matrices are closed under products and diagonal sums (`FullClosed`,
e.g. any semifir, `fullClosed_of_semifir`), the universal localization `FullLoc R` at the full
matrices is a division ring **as soon as it is nontrivial** (`isUnit_or_eq_zero`, Cohn *FIR*
Prop 7.5.9(i)), and is then the universal field of fractions (Cohn *FIR* Thm 7.5.13,
*Skew Fields* Cor 4.5.9).

The nontriviality input `Nontrivial (FullLoc R)` is supplied by the display ring
(`DisplayModel.lean`); this file is stated relative to it so that it can be checked independently.
-/

variable {R : Type u} [Ring R]

/-- The canonical map `R → FullLoc R` inverts all full matrices. -/
theorem isFullInverting_toFullLoc : IsFullInverting (toFullLoc R) :=
  fun _ _ hA => UnivLoc.isUnit_map_toLoc hA

/-- `FullLoc R` as a division ring, given nontriviality. -/
noncomputable abbrev fullLocDivisionRing [FullClosed R] [Nontrivial (FullLoc R)] :
    DivisionRing (FullLoc R) :=
  DivisionRing.ofIsUnitOrEqZero isUnit_or_eq_zero

theorem isUniversalFieldOfFractions_fullLoc [FullClosed R] [Nontrivial (FullLoc R)] :
    letI := fullLocDivisionRing (R := R)
    IsUniversalFieldOfFractions (FullLoc R) (toFullLoc R) := by
  let _ := fullLocDivisionRing (R := R)
  exact
    { fullInverting := isFullInverting_toFullLoc
      exists_lift := fun _ _ f hf => ⟨UnivLoc.lift f hf, UnivLoc.lift_comp_toLoc f hf⟩
      ext := fun _ _ _ _ h => UnivLoc.hom_ext h }

theorem hasUniversalFieldOfFractions_of_nontrivial [FullClosed R] [Nontrivial (FullLoc R)] :
    HasUniversalFieldOfFractions R :=
  letI := fullLocDivisionRing (R := R)
  ⟨FullLoc R, fullLocDivisionRing, toFullLoc R, isUniversalFieldOfFractions_fullLoc⟩

/-- `FullLoc R` is nontrivial for `FullClosed R`: Cohn's display ring (`Display.M`) is a nonzero
full-inverting target (`LeftPCI/FreeField/DisplayModel.lean`). -/
instance nontrivial_fullLoc [FullClosed R] : Nontrivial (FullLoc R) :=
  Display.nontrivial_loc_isFull

/-- Every `FullClosed` ring (e.g. every Sylvester domain) has a universal field of fractions. -/
theorem hasUniversalFieldOfFractions_of_fullClosed [FullClosed R] :
    HasUniversalFieldOfFractions R :=
  hasUniversalFieldOfFractions_of_nontrivial

/-- **The free field exists**: `k⟨X⟩` has a universal field of fractions. -/
theorem hasUniversalFieldOfFractions_freeAlgebra (k : Type u) [Field k] (X : Type v) :
    HasUniversalFieldOfFractions (FreeAlgebra k X) :=
  hasUniversalFieldOfFractions_of_fullClosed

end LeftPCI.FreeField
