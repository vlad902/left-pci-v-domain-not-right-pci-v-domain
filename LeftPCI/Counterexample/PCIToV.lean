module

public import LeftPCI.Counterexample.Defs

/-!
# PCI rings which are not division rings are V-rings; transport of the PCI property

* `isLeftVRing_of_isLeftPCIRing`, `isRightVRing_of_isRightPCIRing`: **Lemma 2.6** of the paper
  `paper/pci_counterexample.tex`. If `R` is not a division ring (some non-zero element is not a
  unit), a left PCI ring is a left V-ring: a simple left module is `R ⧸ M` for a maximal left
  ideal `M`, and `R ⧸ M ≅ R` would make `R` simple as a left module over itself, i.e. a division
  ring (`isSimpleModule_self_iff_isUnit`); so `R ⧸ M` is a proper cyclic module, hence injective.
  (The paper states Lemma 2.6 for domains; the argument does not use that `R` is a domain.)
* `IsLeftPCIRing.of_ringEquiv`: the left PCI property is invariant under ring isomorphisms, and
  `isLeftPCIRing_iff_isRightPCIRing_op`: `R` is left PCI iff `Rᵐᵒᵖ` is right PCI (via
  `RingEquiv.opOp`).
-/

@[expose] public section

universe u

namespace LeftPCI

/-- **Lemma 2.6** (left-handed): a left PCI ring which is not a division ring is a left
V-ring. -/
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

/-- **Lemma 2.6** (right-handed): a right PCI ring which is not a division ring is a right
V-ring. -/
theorem isRightVRing_of_isRightPCIRing (R : Type u) [Ring R] (hR : ∃ x : R, x ≠ 0 ∧ ¬ IsUnit x)
    (h : IsRightPCIRing R) : IsRightVRing R := by
  obtain ⟨x, hx0, hxu⟩ := hR
  refine isLeftVRing_of_isLeftPCIRing Rᵐᵒᵖ ⟨MulOpposite.op x, ?_, ?_⟩ h
  · simpa using hx0
  · rwa [isUnit_op]

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
