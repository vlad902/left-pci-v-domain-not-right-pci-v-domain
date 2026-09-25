module

public import LeftPCI.OrePoly.Degree
public import Mathlib.RingTheory.SimpleRing.Basic

@[expose] public section

namespace LeftPCI

/-! # Failure of the right Ore condition in `k[t; σ, δ]`

If `σ` is not surjective and `c ∉ σ(K)`, then `t R ∩ (c t) R = 0` in `R = K[t; σ, δ]`
(`X_mul_ne_C_mul_X_mul`; the degree computation in the proof of Proposition 2.3 of the paper
`paper/pci_counterexample.tex`, which is also the computation in the proof of
Jain–Lam–Leroy, Proposition 6.1 (1)).
-/

namespace OrePoly

variable {K : Type u} [DivisionRing K] {σ : K →+* K} (δ : OreDerivation K σ)

/-! ## `t·R ∩ (c·t)·R = 0` -/

/-- **The key lemma** (the computation in the proof of Proposition 2.3).

For `c ∈ K ∖ σ(K)` the right ideals `t·R` and `(c·t)·R` of `R = K[t; σ, δ]` meet in `0`: there is
no equation `t · f = (c·t) · g` with `g ≠ 0`.  (Since `R` is a domain and `c ≠ 0`, `g ≠ 0` is
equivalent to the common value being nonzero, and it forces `f ≠ 0` as well.)

*Proof.* Degrees add (`natDegree_mul`, using that `σ` is injective — automatic over a division
ring), so `1 + deg f = 1 + deg g`.  Leading coefficients multiply by
`lc (fg) = lc f · σ^{deg f}(lc g)` (`leadingCoeff_mul`), so `σ(lc f) = c · σ(lc g)` and therefore
`c = σ(lc f) · σ(lc g)⁻¹ = σ(lc f · (lc g)⁻¹) ∈ σ(K)`, a contradiction. ∎

`δ` never appears: it contributes only strictly below the top term.  This is the exact point at
which non-surjectivity of `σ` enters — and if `σ` *were* onto, the same computation would *solve*
`σ(lc f) = c · σ(lc g)`, which is the converse half of Rowen's Prop. 1.6.22. -/
theorem X_mul_ne_C_mul_X_mul {c : K} (hc : c ∉ Set.range σ) {f g : OrePoly δ} (hg : g ≠ 0) :
    X δ * f ≠ C δ c * (X δ * g) := by
  intro h
  have hinj : Function.Injective σ := σ.injective
  have _hnzd : NoZeroDivisors (OrePoly δ) := noZeroDivisors_of_injective δ hinj
  have hc0 : c ≠ 0 := fun h0 => hc ⟨0, by rw [map_zero, h0]⟩
  have hX : X δ ≠ 0 := by
    have h1 := X_pow_ne_zero δ 1
    rwa [pow_one] at h1
  have hCc : C δ c ≠ 0 := C_ne_zero δ hc0
  have hXg : X δ * g ≠ 0 := mul_ne_zero hX hg
  have hrhs : C δ c * (X δ * g) ≠ 0 := mul_ne_zero hCc hXg
  have hf : f ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hrhs h.symm
  have hlcX : leadingCoeff δ (X δ) = 1 := leadingCoeff_monomial δ (one_ne_zero (α := K))
  have hlcC : leadingCoeff δ (C δ c) = c := leadingCoeff_monomial δ hc0
  have hL : leadingCoeff δ (X δ * f) = σ (leadingCoeff δ f) := by
    rw [leadingCoeff_mul δ hinj hX hf, hlcX, one_mul, natDegree_X δ, Function.iterate_one]
  have hR : leadingCoeff δ (C δ c * (X δ * g)) = c * σ (leadingCoeff δ g) := by
    rw [leadingCoeff_mul δ hinj hCc hXg, hlcC, natDegree_C δ c, Function.iterate_zero_apply,
      leadingCoeff_mul δ hinj hX hg, hlcX, one_mul, natDegree_X δ, Function.iterate_one]
  rw [h, hR] at hL
  have hgne : σ (leadingCoeff δ g) ≠ 0 := fun h0 =>
    leadingCoeff_ne_zero δ hg (hinj (by rw [h0, map_zero]))
  refine hc ⟨leadingCoeff δ f * (leadingCoeff δ g)⁻¹, ?_⟩
  rw [map_mul, map_inv₀, ← hL, mul_assoc, mul_inv_cancel₀ hgne, mul_one]

end OrePoly

end LeftPCI
