module

public import LeftPCI.Counterexample.Countable
public import LeftPCI.Counterexample.OreExtension
public import LeftPCI.Counterexample.PCIToV
public import LeftPCI.Counterexample.Tower
public import Mathlib.Data.Finsupp.Encodable

@[expose] public section

namespace LeftPCI

/-! # The Main Theorem and Corollary 5.3

This is the final assembly of the paper `paper/pci_counterexample.tex` (*PCI rings and V-domains are not left-right symmetric*): the **Main Theorem
(Theorem 1.1)** and the parts of **Corollary 5.3** that are statements about all rings.

* **Theorem 2.5** (`exists_isCFClosed_not_surjective`, proved in `Tower.lean` via Construction 5.1
  in the fixed-symbol variant of Remark 5.2, with `k = ℚ`): a countable division ring `K̃` with a
  non-surjective endomorphism `σ̃` and a `σ̃`-derivation `δ̃` over which every proper cyclic left
  `K̃[t; σ̃, δ̃]`-module is divisible.
* **Proposition 2.2** (with Baer's criterion, as in the paragraph after it):
  `isLeftPCIRing_of_isCFClosed` — `R̃ = K̃[t; σ̃, δ̃]` is left PCI (`OreExtension.lean`).
* **Proposition 2.3**: `leftIndep_op_X_of_not_surjective` — `t R̃ ∩ c t R̃ = 0` for `c ∉ σ̃(K̃)`
  (`OreExtension.lean`); hence `not_isRightOre_of_not_surjective`: `R̃` is not right Ore.
* **Lemma 2.4** (a cardinality argument in the spirit of Lawrence): `not_isLeftVRing_of_countable`
  (`Countable.lean`, stated on the left), applied to `R̃ᵐᵒᵖ` in
  `not_isRightVRing_of_not_surjective`: `R̃` is not a right V-ring.
* **Lemma 2.6** (`isLeftVRing_of_isLeftPCIRing`, `isRightVRing_of_isRightPCIRing`,
  `PCIToV.lean`): `R̃` is a left V-ring, and it is not right PCI since it is not a right V-ring
  and `t` is a non-zero non-unit.

The *Proof of the Main Theorem* in §5 is `exists_isLeftPCIRing_not_isRightPCIRing`;
Corollary 5.3 (1), mirrored to the left, is `not_forall_isLeftPCIRing_imp_isRightPCIRing`, and
Corollary 5.3 (3) is `not_forall_isLeftVRing_imp_isRightVRing`.
-/

namespace Counterexample

open OrePoly

variable {K : Type} [DivisionRing K] {σ : K →+* K} (δ : OreDerivation K σ)

/-- `t = X δ` is a non-zero non-unit of `K[t; σ, δ]`, so `K[t; σ, δ]` is not a division ring. -/
theorem exists_ne_zero_not_isUnit : ∃ x : OrePoly δ, x ≠ 0 ∧ ¬ IsUnit x :=
  ⟨X δ, X_ne_zero δ, not_isUnit_X δ σ.injective⟩

/-- The same in the opposite ring: `op t` is a non-zero non-unit of `K[t; σ, δ]ᵐᵒᵖ`. -/
theorem exists_ne_zero_not_isUnit_op : ∃ x : (OrePoly δ)ᵐᵒᵖ, x ≠ 0 ∧ ¬ IsUnit x :=
  ⟨MulOpposite.op (X δ), by simpa using X_ne_zero δ, by
    rw [isUnit_op]; exact not_isUnit_X δ σ.injective⟩

/-- **Proposition 2.3**: `K[t; σ, δ]` with `σ` not onto is not right Ore, since `t R ∩ c t R = 0`
for `c ∉ σ(K)`. -/
theorem not_isRightOre_of_not_surjective (hσ : ¬ Function.Surjective σ) :
    ¬ IsRightOre (OrePoly δ) := by
  obtain ⟨c, hc⟩ : ∃ c : K, c ∉ Set.range σ := by
    by_contra h
    exact hσ fun c => not_not.mp (not_exists.mp h c)
  have hc0 : c ≠ 0 := fun h0 => hc ⟨0, by rw [map_zero, h0]⟩
  have : IsDomain (OrePoly δ) := isDomain_of_injective δ σ.injective
  intro hOre
  obtain ⟨x, y, hxy, hx0⟩ :=
    hOre (X δ) (C δ c * X δ) (X_ne_zero δ) (mul_ne_zero (C_ne_zero δ hc0) (X_ne_zero δ))
  have hy : y ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hxy
    exact hx0 hxy
  exact X_mul_ne_C_mul_X_mul δ hc hy (by rw [hxy, mul_assoc])

/-- **Lemma 2.4** applied as in the *Proof of the Main Theorem*: `K[t; σ, δ]` with `σ` not onto and
`K` countable is not a right V-ring, since `t R ∩ c t R = 0` for `c ∉ σ(K)` (Proposition 2.3) and
`R` is countable (Lemma 2.4 at `Rᵐᵒᵖ`). -/
theorem not_isRightVRing_of_not_surjective [Countable K] (hσ : ¬ Function.Surjective σ) :
    ¬ IsRightVRing (OrePoly δ) := by
  obtain ⟨c, hc⟩ : ∃ c : K, c ∉ Set.range σ := by
    by_contra h
    exact hσ fun c => not_not.mp (not_exists.mp h c)
  have hdom : IsDomain (OrePoly δ) := isDomain_of_injective δ σ.injective
  have hcount : Countable (OrePoly δ) := inferInstanceAs (Countable (ℕ →₀ K))
  have hcount' : Countable (OrePoly δ)ᵐᵒᵖ := MulOpposite.op_surjective.countable
  have hb : MulOpposite.op (C δ c * X δ) ≠ 0 := by
    rw [ne_eq, MulOpposite.op_eq_zero_iff]
    have hc0 : c ≠ 0 := fun h0 => hc ⟨0, by rw [map_zero, h0]⟩
    exact mul_ne_zero (C_ne_zero δ hc0) (X_ne_zero δ)
  exact not_isLeftVRing_of_countable hb (leftIndep_op_X_of_not_surjective δ hc)

/-- **Lemma 2.6** applied as in the *Proof of the Main Theorem*: `K[t; σ, δ]` with `σ` not onto and
`K` countable is not a right PCI ring, as it is not a right V-ring and not a division ring. -/
theorem not_isRightPCIRing_of_not_surjective [Countable K] (hσ : ¬ Function.Surjective σ) :
    ¬ IsRightPCIRing (OrePoly δ) := fun h =>
  not_isRightVRing_of_not_surjective δ hσ
    (isRightVRing_of_isRightPCIRing _ (exists_ne_zero_not_isUnit δ) h)

end Counterexample

open Counterexample OrePoly

/-- **Main Theorem** (Theorem 1.1 of the paper): a countable domain which is a left PCI ring and a
left V-ring but is not right Ore, not a right PCI ring and not a right V-ring. -/
theorem exists_isLeftPCIRing_not_isRightPCIRing :
    ∃ (R : Type) (_ : Ring R), IsDomain R ∧ Countable R ∧ IsLeftPCIRing R ∧ IsLeftVRing R ∧
      ¬ IsRightOre R ∧ ¬ IsRightPCIRing R ∧ ¬ IsRightVRing R := by
  obtain ⟨K, _, σ, δ, hK, hσ, hcf⟩ := exists_isCFClosed_not_surjective
  have hpci : IsLeftPCIRing (OrePoly δ) := isLeftPCIRing_of_isCFClosed δ hcf
  exact ⟨OrePoly δ, inferInstance, isDomain_of_injective δ σ.injective,
    inferInstanceAs (Countable (ℕ →₀ K)), hpci,
    isLeftVRing_of_isLeftPCIRing _ (exists_ne_zero_not_isUnit δ) hpci,
    not_isRightOre_of_not_surjective δ hσ, not_isRightPCIRing_of_not_surjective δ hσ,
    not_isRightVRing_of_not_surjective δ hσ⟩

/-- A right PCI ring need not be left PCI (Corollary 5.3 (1)): the opposite ring of the Main
Theorem's example. -/
theorem not_forall_isLeftPCIRing_imp_isRightPCIRing :
    ¬ ∀ (R : Type) [Ring R], IsLeftPCIRing R → IsRightPCIRing R := by
  intro h
  obtain ⟨R, _, -, -, hl, -, -, hr, -⟩ := exists_isLeftPCIRing_not_isRightPCIRing
  exact hr (h R hl)

/-- A left V-domain need not be a right V-domain (Corollary 5.3 (3)). -/
theorem not_forall_isLeftVRing_imp_isRightVRing :
    ¬ ∀ (R : Type) [Ring R], IsDomain R → IsLeftVRing R → IsRightVRing R := by
  intro h
  obtain ⟨R, _, hd, -, -, hl, -, -, hv⟩ := exists_isLeftPCIRing_not_isRightPCIRing
  exact hv (h R hd hl)

end LeftPCI
