module

public import LeftPCI.OrePoly.Degree
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.SimpleRing.Basic

@[expose] public section

namespace LeftPCI

/-! # Left division in the Ore extension `k[t; σ, δ]`

The left division algorithm in `K[t; σ, δ]` over a division ring `K`, and its consequence that
`K[t; σ, δ]` is a principal left ideal ring (`isPrincipalIdealRing`), via the general
`isPrincipalIdealRing_of_leftDiv`.
-/

/-- A (possibly noncommutative) ring admitting *left* division with remainder for a
`ℕ`-valued "degree" is a left principal ideal ring: `Ideal A = Submodule A A` is the lattice of
left ideals, and an element of a nonzero ideal of minimal degree generates it.

Mathlib's `EuclideanDomain`/`IsPrincipalIdealRing` development is `CommRing`-based, so this
noncommutative version is proved from scratch here. -/
theorem isPrincipalIdealRing_of_leftDiv {A : Type*} [Ring A] (deg : A → ℕ)
    (hdiv : ∀ g : A, g ≠ 0 → ∀ p : A, ∃ d r : A, p = d * g + r ∧ (r = 0 ∨ deg r < deg g)) :
    IsPrincipalIdealRing A := by
  classical
  constructor
  intro I
  by_cases hI : ∀ x ∈ I, x = 0
  · refine ⟨0, ?_⟩
    ext x
    simp only [Submodule.mem_span_singleton, smul_eq_mul, mul_zero, exists_const]
    exact ⟨fun h => (hI x h).symm, fun h => h ▸ I.zero_mem⟩
  · push Not at hI
    obtain ⟨x, hxI, hx0⟩ := hI
    have hex : ∃ n, ∃ y ∈ I, y ≠ 0 ∧ deg y = n := ⟨deg x, x, hxI, hx0, rfl⟩
    obtain ⟨g, hgI, hg0, hgd⟩ := Nat.find_spec hex
    refine ⟨g, le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem g I).2 hgI)⟩
    intro p hp
    obtain ⟨d, r, hpr, hr⟩ := hdiv g hg0 p
    have hrI : r ∈ I := by
      have hre : r = p - d * g := by rw [hpr]; abel
      rw [hre]; exact I.sub_mem hp (I.mul_mem_left d hgI)
    by_cases hr0 : r = 0
    · exact Submodule.mem_span_singleton.2 ⟨d, by rw [hpr, hr0, add_zero]; rfl⟩
    · exfalso
      have h1 : Nat.find hex ≤ deg r := Nat.find_le ⟨r, hrI, hr0, rfl⟩
      have h2 : deg r < deg g := hr.resolve_left hr0
      omega

namespace OrePoly

variable {K : Type u} [DivisionRing K] {σ : K →+* K} (δ : OreDerivation K σ)

/-- **One step of the left division algorithm**.

If `deg g ≤ deg f` with `f, g ≠ 0`, there is a monomial `q` — explicitly
`q = (lc f · σ^{deg f - deg g}(lc g)⁻¹) · t^{deg f - deg g}` — for which `q * g` has the same
degree *and* the same leading coefficient as `f`, so that `f - q * g` has strictly smaller degree
(or vanishes).

The only property of `K` used is that `σ^{deg f - deg g}(lc g)` is **invertible**; `σ` is not
assumed surjective, and `δ` is arbitrary — it contributes nothing to either the degree or the
leading coefficient of a product (`OrePoly.leadingCoeff_mul`). -/
theorem exists_leftDiv_step {f g : OrePoly δ} (hf : f ≠ 0) (hg : g ≠ 0)
    (hle : natDegree δ g ≤ natDegree δ f) :
    ∃ q : OrePoly δ, f - q * g = 0 ∨ natDegree δ (f - q * g) < natDegree δ f := by
  have hinj : Function.Injective σ := σ.injective
  have hb : (⇑σ)^[natDegree δ f - natDegree δ g] (leadingCoeff δ g) ≠ 0 :=
    iterate_ne_zero hinj _ (leadingCoeff_ne_zero δ hg)
  have hc : leadingCoeff δ f *
      ((⇑σ)^[natDegree δ f - natDegree δ g] (leadingCoeff δ g))⁻¹ ≠ 0 :=
    mul_ne_zero (leadingCoeff_ne_zero δ hf) (inv_ne_zero hb)
  refine ⟨monomial δ (natDegree δ f - natDegree δ g) (leadingCoeff δ f *
    ((⇑σ)^[natDegree δ f - natDegree δ g] (leadingCoeff δ g))⁻¹), ?_⟩
  have hdeg : natDegree δ (monomial δ (natDegree δ f - natDegree δ g) (leadingCoeff δ f *
      ((⇑σ)^[natDegree δ f - natDegree δ g] (leadingCoeff δ g))⁻¹) * g) = natDegree δ f := by
    rw [natDegree_monomial_mul δ hinj _ hc hg]; omega
  have hlc : leadingCoeff δ (monomial δ (natDegree δ f - natDegree δ g) (leadingCoeff δ f *
      ((⇑σ)^[natDegree δ f - natDegree δ g] (leadingCoeff δ g))⁻¹) * g) = leadingCoeff δ f := by
    rw [leadingCoeff_monomial_mul δ hinj _ hc hg, inv_mul_cancel_right₀ hb]
  by_cases hz : f - monomial δ (natDegree δ f - natDegree δ g) (leadingCoeff δ f *
      ((⇑σ)^[natDegree δ f - natDegree δ g] (leadingCoeff δ g))⁻¹) * g = 0
  · exact Or.inl hz
  · exact Or.inr (natDegree_sub_lt_of_leadingCoeff_eq δ hdeg hlc hz)

/-- **Left division with remainder in `K[t; σ, δ]`** (Rowen, *Ring Theory I*, Prop. 1.6.21).

For `g ≠ 0` and any `f` there are `q, r` with `f = q * g + r` and either `r = 0` or
`deg r < deg g`.  Note the quotient stands on the **left**, which is the side that works: the
mirror statement `f = g * q + r` requires `σ` to be surjective.

Proved by strong induction on `deg f`, each step being `exists_leftDiv_step`. -/
theorem exists_leftDiv {g : OrePoly δ} (hg : g ≠ 0) (f : OrePoly δ) :
    ∃ q r : OrePoly δ, f = q * g + r ∧ (r = 0 ∨ natDegree δ r < natDegree δ g) := by
  suffices H : ∀ n : ℕ, ∀ f : OrePoly δ, natDegree δ f = n →
      ∃ q r : OrePoly δ, f = q * g + r ∧ (r = 0 ∨ natDegree δ r < natDegree δ g) from
    H _ f rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hfn
    by_cases hlt : natDegree δ f < natDegree δ g
    · exact ⟨0, f, by rw [zero_mul, zero_add], Or.inr hlt⟩
    by_cases hf0 : f = 0
    · exact ⟨0, 0, by rw [hf0, zero_mul, zero_add], Or.inl rfl⟩
    obtain ⟨q₀, hq₀⟩ := exists_leftDiv_step δ hf0 hg (not_lt.mp hlt)
    rcases hq₀ with hq₀ | hq₀
    · exact ⟨q₀, 0, by rw [add_zero, ← sub_eq_zero]; exact hq₀, Or.inl rfl⟩
    · obtain ⟨q, r, hqr, hr⟩ := ih (natDegree δ (f - q₀ * g)) (hfn ▸ hq₀) _ rfl
      exact ⟨q₀ + q, r, by rw [add_mul, add_assoc, ← hqr]; abel, hr⟩

/-- **`K[t; σ, δ]` is a left principal ideal ring** for any division ring `K`, any endomorphism
`σ` and any `σ`-derivation `δ`.

Mathlib's `Ideal R` is `Submodule R R`, i.e. the lattice of *left* ideals, so
`IsPrincipalIdealRing` is the left-handed statement; a nonzero left ideal is generated by any of
its elements of least degree, by `exists_leftDiv`.  Combined with `isDomain_of_injective` this is
Rowen's Prop. 1.6.21: `K[t; σ, δ]` is a principal left ideal domain. -/
theorem isPrincipalIdealRing : IsPrincipalIdealRing (OrePoly δ) :=
  isPrincipalIdealRing_of_leftDiv (natDegree δ) fun _ hg f => exists_leftDiv δ hg f

end OrePoly

end LeftPCI
