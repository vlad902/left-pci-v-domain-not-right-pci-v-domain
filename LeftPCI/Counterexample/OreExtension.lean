module

public import LeftPCI.OrePoly.Division
public import LeftPCI.OrePoly.RightOre
public import LeftPCI.Counterexample.Defs

@[expose] public section

namespace LeftPCI

universe u

/-! # `K[t; σ, δ]` with all proper cyclics divisible is left PCI; `t R ∩ (c t) R = 0`

This is **Section 2** of the paper `paper/pci_counterexample.tex`, for
`OrePoly δ = K[t; σ, δ]` over a division ring `K` with coefficients on the left and
`t a = σ(a) t + δ(a)` (the paper's convention):

* `IsCFClosed δ` ("Cozzens–Faith closed"): for all nonzero `f, g` and every `m`, there is `y` with
  `m − g y ∈ R f`, i.e. every proper cyclic left module `R ⧸ R f` is divisible.  (By JLL Lemma 4.3
  this is the same as: every `g(T_f)` is onto; by JLL Thm 3.2 it is the same as `R` being a left
  V-domain.)
* `injective_quotient_of_isCFClosed` / `isLeftPCIRing_of_isCFClosed`: divisible ⟹ injective over
  the left principal ideal domain `R` — this is the Baer-criterion argument given after
  Proposition 2.2 of the paper (the paper's Proposition 2.2 itself only needs the target `e₁` and
  quotes Jain–Lam–Leroy Thm 3.2; here we solve for every target, Theorem 2.5 holds in that
  generality, and Baer's criterion is then direct), so `R` is a left PCI ring.
* `leftIndep_op_X_of_not_surjective`: **Proposition 2.3**, if `c ∉ σ(K)` then `t R ∩ (c t) R = 0`
  (`OrePoly.X_mul_ne_C_mul_X_mul`), phrased in the opposite ring as
  `r * op t = s * op (c t) → r = 0`.  The consequences for the right-hand side (not right Ore,
  not right V, not right PCI) are drawn in `Closure.lean`, via Lemma 2.4 and Lemma 2.6 instead of
  Cozzens–Faith 6.17.
-/

namespace Counterexample

open OrePoly

variable {K : Type u} [DivisionRing K] {σ : K →+* K} (δ : OreDerivation K σ)

/-- **Cozzens–Faith closedness**: every proper cyclic left module `R ⧸ R f` of `R = K[t; σ, δ]`
is divisible. -/
def IsCFClosed : Prop :=
  ∀ f : OrePoly δ, f ≠ 0 → ∀ g : OrePoly δ, g ≠ 0 → ∀ m : OrePoly δ,
    ∃ y : OrePoly δ, m - g * y ∈ Ideal.span ({f} : Set (OrePoly δ))

/-- Divisible ⟹ injective over the left PID `K[t; σ, δ]` (Baer). -/
theorem injective_quotient_of_isCFClosed (h : IsCFClosed δ) {I : Ideal (OrePoly δ)}
    (hI : I ≠ ⊥) : Module.Injective (OrePoly δ) (OrePoly δ ⧸ I) := by
  have : IsPrincipalIdealRing (OrePoly δ) := isPrincipalIdealRing δ
  obtain ⟨f, hfI, hf⟩ := Submodule.ne_bot_iff I |>.1 hI
  have hsub : Ideal.span {f} ≤ I := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hfI
  refine Module.Baer.injective ?_
  intro J φ
  obtain ⟨g, hgJ⟩ := (IsPrincipalIdealRing.principal J)
  rcases eq_or_ne g 0 with rfl | hg0
  · refine ⟨0, fun x hx => ?_⟩
    have hx0 : x = 0 := by
      rw [hgJ] at hx
      simpa using hx
    subst hx0
    simp only [LinearMap.zero_apply]
    have : (⟨0, hx⟩ : J) = 0 := Subtype.ext rfl
    rw [this, map_zero]
  · have hgmem : g ∈ J := by rw [hgJ]; exact Ideal.subset_span rfl
    obtain ⟨m₀, hm₀⟩ := Submodule.Quotient.mk_surjective I (φ ⟨g, hgmem⟩)
    obtain ⟨y, hy⟩ := h f hf g hg0 m₀
    refine ⟨LinearMap.toSpanSingleton _ _ (Submodule.Quotient.mk y : OrePoly δ ⧸ I),
      fun x hx => ?_⟩
    have hkey : φ ⟨g, hgmem⟩ = g • (Submodule.Quotient.mk y : OrePoly δ ⧸ I) := by
      rw [← hm₀]
      have : (Submodule.Quotient.mk (g * y) : OrePoly δ ⧸ I)
          = g • (Submodule.Quotient.mk y : OrePoly δ ⧸ I) := rfl
      rw [← this, Submodule.Quotient.eq]
      exact hsub hy
    have hx' : x ∈ Ideal.span ({g} : Set (OrePoly δ)) := by rw [hgJ] at hx; exact hx
    obtain ⟨u, hux⟩ := Ideal.mem_span_singleton'.1 hx'
    have hxe : (⟨x, hx⟩ : J) = u • ⟨g, hgmem⟩ := Subtype.ext hux.symm
    rw [hxe, map_smul, hkey, ← hux]
    simp [LinearMap.toSpanSingleton_apply, mul_smul]

/-- A Cozzens–Faith closed Ore extension is a **left PCI ring**. -/
theorem isLeftPCIRing_of_isCFClosed (h : IsCFClosed δ) : IsLeftPCIRing (OrePoly δ) := by
  intro I hI
  refine injective_quotient_of_isCFClosed δ h ?_
  rintro rfl
  exact hI ⟨Submodule.quotEquivOfEqBot ⊥ rfl⟩

/-- `t R ∩ (c t) R = 0` for `c ∉ σ(K)`, in the opposite ring: `r * op t = s * op (c t) → r = 0`. -/
theorem leftIndep_op_X_of_not_surjective {c : K} (hc : c ∉ Set.range σ) :
    ∀ r s : (OrePoly δ)ᵐᵒᵖ,
      r * MulOpposite.op (X δ) = s * MulOpposite.op (C δ c * X δ) → r = 0 := by
  intro r s hrs
  have heq : X δ * MulOpposite.unop r = C δ c * (X δ * MulOpposite.unop s) := by
    have := congrArg MulOpposite.unop hrs
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_op, mul_assoc] using this
  rcases eq_or_ne (MulOpposite.unop s) 0 with hs | hs
  · have : IsDomain (OrePoly δ) := isDomain_of_injective δ σ.injective
    have hX : X δ ≠ 0 := X_ne_zero δ
    rw [hs, mul_zero, mul_zero] at heq
    exact MulOpposite.unop_injective ((mul_eq_zero.1 heq).resolve_left hX)
  · exact absurd heq (X_mul_ne_C_mul_X_mul δ hc hs)

end Counterexample

end LeftPCI
