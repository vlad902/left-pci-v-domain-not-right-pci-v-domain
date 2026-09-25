module

public import LeftPCI.Counterexample.PCIToV
public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.RingTheory.SimpleModule.Basic

@[expose] public section

namespace LeftPCI

universe u

/-! # A countable non-Ore domain has no nonzero countable injective modules

This is **Lemma 2.4** of the paper `paper/pci_counterexample.tex`, stated on the **left**
(the mirror of the paper, which is on the right); it is a cardinality argument in the spirit of
J. Lawrence, *A countable self-injective ring is quasi-Frobenius*, Proc. Amer. Math. Soc. **65**
(1977) 217–220, Theorem 4.

Let `R` be a domain and `a, b ∈ R` with `R a ∩ R b = 0` (`LeftIndep a b`: `r a = s b ⟹ r = 0`).
Then the left ideals `R a bⁱ` (`i ∈ ℕ`) are independent (`linearIndependent_mul_pow`): from
`Σ rᵢ a bⁱ = 0` one gets `r₀ a = −(Σ_{i ≥ 1} rᵢ a bⁱ⁻¹) b ∈ R a ∩ R b = 0`, so `r₀ = 0`, and then
`b` cancels on the right.  So `I := ⊕ᵢ R a bⁱ` is a free left ideal of countably infinite rank.

If `S` is an injective left module, every `R`-linear map `I → S` extends to `R`, so it is
`x ↦ x • s` for some `s ∈ S`; since a map on the free module `I` may send the basis element `a bⁱ`
to an arbitrary `sᵢ`, the map `S → (ℕ → S)`, `s ↦ (a bⁱ • s)ᵢ`, is **surjective**
(`surjective_smul_family_of_injective`).  For countable nontrivial `S` this is impossible, as
`ℕ → S` has cardinality `≥ 2^ℵ₀` (`not_injective_of_countable`).

Consequently a countable domain with `R a ∩ R b = 0` for some nonzero `a, b` is not a left
V-ring (`not_isLeftVRing_of_countable`): a simple module `R ⧸ M` is countable and nontrivial, and
over a left V-ring it would be injective.
-/

namespace Counterexample

variable {R : Type u} [Ring R]

/-- `R a ∩ R b = 0`, in elementary form: `r * a = s * b` forces `r = 0`. -/
def LeftIndep (a b : R) : Prop := ∀ r s : R, r * a = s * b → r = 0

/-- `LeftIndep` is symmetric for `b ≠ 0`.  (The hypothesis `b ≠ 0` is needed: `LeftIndep a 0`
just says `a` is not a left zero-divisor, while `LeftIndep 0 a` fails for `r = 1`, `s = 0` in any
nontrivial ring.) -/
theorem LeftIndep.symm [IsDomain R] {a b : R} (hb : b ≠ 0) (h : LeftIndep a b) :
    LeftIndep b a := by
  intro r s hrs
  have hs : s = 0 := h s r hrs.symm
  subst hs
  rw [zero_mul, mul_eq_zero] at hrs
  exact hrs.resolve_right hb

/-- The key computation behind `linearIndependent_mul_pow`: a vanishing combination of
`a, a b, …, a b ^ (n - 1)` has all coefficients zero. -/
theorem coeff_eq_zero_of_sum_mul_pow [IsDomain R] {a b : R} (hb : b ≠ 0) (h : LeftIndep a b) :
    ∀ (n : ℕ) (g : ℕ → R), (∑ i ∈ Finset.range n, g i * (a * b ^ i)) = 0 →
      ∀ i < n, g i = 0 := by
  intro n
  induction n with
  | zero => intro g _ i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro g hg i hi
    rw [Finset.sum_range_succ'] at hg
    have hT : ∑ i ∈ Finset.range n, g (i + 1) * (a * b ^ (i + 1)) =
        (∑ i ∈ Finset.range n, g (i + 1) * (a * b ^ i)) * b := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ, mul_assoc, mul_assoc]
    rw [hT, pow_zero, mul_one] at hg
    set T := ∑ i ∈ Finset.range n, g (i + 1) * (a * b ^ i) with hTdef
    have hg0 : g 0 = 0 := by
      apply h (g 0) (-T)
      rw [neg_mul, eq_neg_iff_add_eq_zero, add_comm]
      exact hg
    have hT0 : T = 0 := by
      rw [hg0, zero_mul, add_zero, mul_eq_zero] at hg
      exact hg.resolve_right hb
    rcases i with _ | i
    · exact hg0
    · exact ih (fun i => g (i + 1)) hT0 i (Nat.lt_of_succ_lt_succ hi)

/-- The family `a, a b, a b², …` is left linearly independent over `R` when `R a ∩ R b = 0`. -/
theorem linearIndependent_mul_pow [IsDomain R] {a b : R} (hb : b ≠ 0) (h : LeftIndep a b) :
    LinearIndependent R (fun i : ℕ => a * b ^ i) := by
  rw [linearIndependent_iff'']
  intro s g hgs hsum i
  obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range s
  have hsum' : (∑ j ∈ Finset.range n, g j * (a * b ^ j)) = 0 := by
    rw [← hsum]
    simp_rw [smul_eq_mul]
    refine (Finset.sum_subset hn fun j _ hj => ?_).symm
    rw [hgs j hj, zero_mul]
  by_cases hi : i ∈ s
  · exact coeff_eq_zero_of_sum_mul_pow hb h n g hsum' i (Finset.mem_range.mp (hn hi))
  · exact hgs i hi

/-- Over an injective module `S`, the map `s ↦ (a bⁱ • s)ᵢ` is onto `ℕ → S`. -/
theorem surjective_smul_family_of_injective [IsDomain R] {a b : R} (hb : b ≠ 0)
    (h : LeftIndep a b) (S : Type u) [AddCommGroup S] [Module R S] [Module.Injective R S] :
    Function.Surjective (fun (s : S) (i : ℕ) => (a * b ^ i) • s) := by
  intro t
  let v : ℕ → R := fun i => a * b ^ i
  have hli : Function.Injective (Finsupp.linearCombination R v) := linearIndependent_mul_pow hb h
  let ι : (ℕ →₀ R) →ₗ[R] R := Finsupp.linearCombination R v
  let I : Ideal R := LinearMap.range ι
  let e : (ℕ →₀ R) ≃ₗ[R] LinearMap.range ι := LinearEquiv.ofInjective ι hli
  let g : I →ₗ[R] S := (Finsupp.linearCombination R t) ∘ₗ e.symm.toLinearMap
  obtain ⟨g', hg'⟩ := Module.Baer.of_injective ‹Module.Injective R S› I g
  refine ⟨g' 1, ?_⟩
  funext i
  have hmem : a * b ^ i ∈ I := ⟨Finsupp.single i 1, by simp [ι, v]⟩
  have he : e.symm ⟨a * b ^ i, hmem⟩ = Finsupp.single i 1 := by
    apply e.injective
    rw [e.apply_symm_apply]
    ext
    simp [e, ι, v]
  calc (a * b ^ i) • g' 1 = g' ((a * b ^ i) • (1 : R)) := (g'.map_smul _ _).symm
    _ = g' (a * b ^ i) := by rw [smul_eq_mul, mul_one]
    _ = g ⟨a * b ^ i, hmem⟩ := hg' _ hmem
    _ = t i := by
      simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe, he,
        Finsupp.linearCombination_single, one_smul]

/-- **Lemma 2.4.** Over a countable domain with `R a ∩ R b = 0` (`b ≠ 0`), no nontrivial countable
module is injective. -/
theorem not_injective_of_countable [IsDomain R] [Countable R] {a b : R} (hb : b ≠ 0)
    (h : LeftIndep a b) (S : Type u) [AddCommGroup S] [Module R S] [Nontrivial S] [Countable S] :
    ¬ Module.Injective R S := by
  classical
  intro hinj
  have hsurj := surjective_smul_family_of_injective hb h S
  have hc : Countable (ℕ → S) := hsurj.countable
  obtain ⟨x, y, hxy⟩ := exists_pair_ne S
  have hinj' : Function.Injective (fun A : Set ℕ => fun i => if i ∈ A then x else y) := by
    intro A B hAB
    ext i
    have := congrFun hAB i
    simp only at this
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp_all
  have hcs : Countable (Set ℕ) := hinj'.countable
  have h1 : Cardinal.mk (Set ℕ) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr hcs
  have h2 : Cardinal.aleph0 < Cardinal.mk (Set ℕ) := by
    rw [Cardinal.mk_set, Cardinal.mk_nat]
    exact Cardinal.cantor _
  exact absurd h1 (not_le.mpr h2)

/-- A countable domain with `R a ∩ R b = 0` for some `b ≠ 0` is not a left V-ring. -/
theorem not_isLeftVRing_of_countable [IsDomain R] [Countable R] {a b : R} (hb : b ≠ 0)
    (h : LeftIndep a b) : ¬ IsLeftVRing R := by
  intro hV
  obtain ⟨M, hM⟩ := Ideal.exists_maximal R
  have hS : IsSimpleModule R (R ⧸ M) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp hM)
  have : Nontrivial (R ⧸ M) := Submodule.Quotient.nontrivial_iff.mpr hM.ne_top
  have : Countable (R ⧸ M) := Quotient.countable
  exact not_injective_of_countable hb h (R ⧸ M) (hV (R ⧸ M) hS)

/-- Nor is it a left PCI ring: `R` is not simple as a module, since `b` is not a unit. -/
theorem not_isLeftPCIRing_of_countable [IsDomain R] [Countable R] {a b : R} (hb : b ≠ 0)
    (h : LeftIndep a b) : ¬ IsLeftPCIRing R := fun hP =>
  not_isLeftVRing_of_countable hb h <| isLeftVRing_of_isLeftPCIRing R ⟨b, hb, fun hu =>
    one_ne_zero (h 1 (a * ↑hu.unit⁻¹) (by rw [one_mul, mul_assoc, hu.val_inv_mul, mul_one]))⟩ hP

end Counterexample

end LeftPCI
