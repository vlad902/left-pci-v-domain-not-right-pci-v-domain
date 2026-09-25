module

public import LeftPCI.Counterexample.Defs

/-!
# PCI rings which are not division rings are V-rings; transport of the PCI property

* `isLeftVRing_of_isLeftPCIRing`: if `R` is not a division ring (some non-zero element is not a
  unit), a left PCI ring is a left V-ring: a simple left module is `R ⧸ M` for a maximal left
  ideal `M`, and `R ⧸ M ≅ R` would make `R` simple as a left module over itself, i.e. a division
  ring (`isSimpleModule_self_iff_isUnit`); so `R ⧸ M` is a proper cyclic module, hence injective.
  This is the "`R` is left V" step in the proof of Proposition 2.2 of
  `paper/pci_counterexample.tex` (there: the zero ideal is not maximal because `Rt` is
  a non-zero proper left ideal), stated for an arbitrary ring; `Closure.lean` applies it to
  `K[t; σ, δ]` with `t` as the non-unit.
* `IsLeftPCIRing.of_ringEquiv`: the left PCI property is invariant under ring isomorphisms, and
  `isLeftPCIRing_iff_isRightPCIRing_op`: `R` is left PCI iff `Rᵐᵒᵖ` is right PCI (via
  `RingEquiv.opOp`).
-/

@[expose] public section

universe u

namespace LeftPCI

/-- **Left PCI ⟹ left V** (the last step of Proposition 2.2 of the paper, for any ring): a left
PCI ring which is not a division ring is a left V-ring. -/
theorem isLeftVRing_of_isLeftPCIRing (R : Type u) [Ring R] (hR : ∃ x : R, x ≠ 0 ∧ ¬ IsUnit x)
    (h : IsLeftPCIRing R) : IsLeftVRing R := by
  intro M _ _ hM
  obtain ⟨I, -, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hM
  have hI : ¬ Nonempty ((R ⧸ I) ≃ₗ[R] R) := by
    rintro ⟨f⟩
    have : IsSimpleModule R (R ⧸ I) := IsSimpleModule.congr e.symm
    have : IsSimpleModule R R := IsSimpleModule.congr f.symm
    obtain ⟨x, hx0, hxu⟩ := hR
    exact hxu ((isSimpleModule_self_iff_isUnit.mp this).2 x hx0)
  have := h I hI
  exact (Module.Baer.of_equiv e.symm (Module.Baer.of_injective this)).injective

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
/-- The left PCI property is invariant under ring isomorphisms: `φ : R ≃+* S` carries `I : Ideal S`
back to `J = I.comap φ`, and `Submodule.Quotient.equiv` upgrades `φ` to a `φ`-semilinear
equivalence `q : (R ⧸ J) ≃ₛₗ[φ] (S ⧸ I)`. Properness transfers by contraposition (conjugating an
`R`-linear `(R ⧸ J) ≃ₗ[R] R` by `q` and `φ` gives an `S`-linear `(S ⧸ I) ≃ₗ[S] S`), and
injectivity transfers along `q` by `Module.Injective.of_ringEquiv`. -/
theorem IsLeftPCIRing.of_ringEquiv {R S : Type u} [Ring R] [Ring S] (φ : R ≃+* S)
    (h : IsLeftPCIRing R) : IsLeftPCIRing S := by
  intro I hI
  have : RingHomSurjective (φ : R →+* S) := ⟨φ.surjective⟩
  have : RingHomSurjective (φ.symm : S →+* R) := ⟨φ.symm.surjective⟩
  set J : Ideal R := Submodule.comap (φ.toSemilinearEquiv : R →ₛₗ[(φ : R →+* S)] S) I
  have hmap : Submodule.map (φ.toSemilinearEquiv : R →ₛₗ[(φ : R →+* S)] S) J = I :=
    Submodule.map_comap_eq_of_surjective φ.toSemilinearEquiv.surjective I
  let q : (R ⧸ J) ≃ₛₗ[(φ : R →+* S)] (S ⧸ I) :=
    Submodule.Quotient.equiv J I φ.toSemilinearEquiv hmap
  have hJ : ¬ Nonempty ((R ⧸ J) ≃ₗ[R] R) := by
    rintro ⟨g⟩
    exact hI ⟨q.symm.trans (g.trans φ.toSemilinearEquiv)⟩
  have := h J hJ
  exact Module.Injective.of_ringEquiv φ q

/-- `R` is left PCI iff `Rᵐᵒᵖ` is right PCI, i.e. iff `Rᵐᵒᵖᵐᵒᵖ ≅ R` is left PCI. -/
theorem isLeftPCIRing_iff_isRightPCIRing_op (R : Type u) [Ring R] :
    IsLeftPCIRing R ↔ IsRightPCIRing Rᵐᵒᵖ :=
  ⟨IsLeftPCIRing.of_ringEquiv (RingEquiv.opOp R),
    IsLeftPCIRing.of_ringEquiv (RingEquiv.opOp R).symm⟩

end LeftPCI
