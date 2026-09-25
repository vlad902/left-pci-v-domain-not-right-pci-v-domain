module

public import LeftPCI.FreeField.Full
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

namespace LeftPCI.FreeField

universe u v

/-! # The universal field of fractions — interface (Theorem 3.1)

This file states, as a `Prop`-valued structure (never an axiom), Cohn's universal field of
fractions, Theorem 3.1 (Cohn) of the paper `paper/pci_counterexample.tex`:

> (Cohn, *Skew Fields* 1995, Cor. 4.5.9 p. 182; *FIR* 2006 Thm 7.5.13).  A semifir `R` has
> a universal field of fractions, namely the universal localization `R_Φ` of `R` at the set `Φ` of
> all full matrices, and `R_Φ` is a division ring.

`IsUniversalFieldOfFractions K ι` says exactly that `ι : R →+* K` is the universal `Φ`-inverting
homomorphism (existence *and* uniqueness of factorizations), with `K` a division ring.  The
consequences used in the paper are **derived** here:

* `IsUniversalFieldOfFractions.ext` (the rigidity Lemma 3.2): two homomorphisms out of `K` that
  agree on `ι(R)` are equal.
* `IsUniversalFieldOfFractions.subfield_eq_top` (Lemma 3.3): a division subring of `K`
  containing `ι(R)` is all of `K`.  Derived from uniqueness plus the linear-algebra fact that a
  matrix over a division subring `L ⊆ K` invertible over `K` is invertible over `L`.
* `exists_extend_of_isHonest`: an honest endomorphism of `R` extends to `K`.  The paper gets
  this directly from Theorem 3.1 (in the proofs of Proposition 3.5 and Lemma 3.6, after
  Lemma 3.4 has shown the endomorphism honest).
* Homomorphisms with a left inverse are honest (Lemma 3.4) —
  `LeftPCI.FreeField.isHonest_of_leftInverse` in `Full.lean`.

The existence of the universal field of fractions is **proved** in `UniversalField.lean`
(`hasUniversalFieldOfFractions_of_fullClosed`, and `hasUniversalFieldOfFractions_freeAlgebra`
for `FreeAlgebra k X`), via the universal localization `FullLoc R` at the full matrices.
-/

/-- **The universal field of fractions**: `ι : R →+* K` is the universal localization of `R` at the full
matrices, and `K` is a division ring.

* `fullInverting` — `ι` inverts every full matrix;
* `exists_lift` — every full-inverting homomorphism into a ring (in `K`'s universe) factors through
  `ι`;
* `ext` — that factorization is unique (`ι` is an epimorphism of rings). -/
structure IsUniversalFieldOfFractions {R : Type u} [Ring R] (K : Type v) [DivisionRing K]
    (ι : R →+* K) : Prop where
  fullInverting : IsFullInverting ι
  exists_lift : ∀ (S : Type v) [Ring S] (f : R →+* S), IsFullInverting f →
    ∃ g : K →+* S, g.comp ι = f
  ext : ∀ (S : Type v) [Ring S] (g₁ g₂ : K →+* S), g₁.comp ι = g₂.comp ι → g₁ = g₂

/-- `R` has a universal field of fractions (in its own universe).  For `R = FreeAlgebra k X` this
is proved by `hasUniversalFieldOfFractions_freeAlgebra` in `UniversalField.lean`. -/
def HasUniversalFieldOfFractions (R : Type u) [Ring R] : Prop :=
  ∃ (K : Type u) (_ : DivisionRing K) (ι : R →+* K), IsUniversalFieldOfFractions K ι

namespace IsUniversalFieldOfFractions

open Matrix

variable {R : Type u} [Ring R] {K : Type v} [DivisionRing K] {ι : R →+* K}

/-- `ι` is injective: a nonzero `r` is a full `1 × 1` matrix, hence becomes invertible. -/
theorem injective (h : IsUniversalFieldOfFractions K ι) : Function.Injective ι := by
  refine (injective_iff_map_eq_zero ι).2 fun r hr => ?_
  by_contra hne
  have hu := h.fullInverting 1 _ ((isFull_one_iff r).2 hne)
  have h0 : (Matrix.of fun (_ _ : Fin 1) => r).map ι = 0 := by
    ext i j; simp [hr]
  rw [h0] at hu
  exact not_isUnit_zero hu

/-- A square matrix over a division subring `L` of a division ring `K` that is invertible over `K`
is invertible over `L`. -/
theorem _root_.LeftPCI.FreeField.isUnit_of_isUnit_map_subfield {K : Type v} [DivisionRing K]
    (L : Subfield K) {n : ℕ} (A : Matrix (Fin n) (Fin n) L)
    (hA : IsUnit (A.map (L.subtype : L →+* K))) : IsUnit A := by
  obtain ⟨B, hB⟩ := hA.exists_right_inv
  set A' := A.map (L.subtype : L →+* K)
  -- the left-`L`-linear map `v ↦ v ᵥ* A`
  let φ : (Fin n → L) →ₗ[L] (Fin n → L) :=
    { toFun := fun v => v ᵥ* A
      map_add' := fun v w => Matrix.add_vecMul A v w
      map_smul' := fun c v => by
        ext j
        simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc] }
  have hmap : ∀ v : Fin n → L, (fun i => (v i : K)) ᵥ* A' = fun j => ((v ᵥ* A) j : K) := by
    intro v; ext j
    simp [A', Matrix.vecMul, dotProduct]
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun v hv => ?_
    have hv' : (fun i => (v i : K)) ᵥ* A' = 0 := by
      rw [hmap]; ext j
      have := congrFun hv j
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk] at this
      simp [this]
    have : (fun i => (v i : K)) = 0 := by
      calc (fun i => (v i : K)) = (fun i => (v i : K)) ᵥ* (A' * B) := by rw [hB, Matrix.vecMul_one]
        _ = 0 := by rw [← Matrix.vecMul_vecMul, hv', Matrix.zero_vecMul]
    ext i
    simpa using congrFun this i
  have hsurj : Function.Surjective φ := LinearMap.injective_iff_surjective.1 hinj
  choose w hw using hsurj
  let W : Matrix (Fin n) (Fin n) L := Matrix.of fun i => w (Pi.single i 1)
  have hWA : W * A = 1 := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hw (Pi.single i 1)) j
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [Matrix.mul_apply]
    rw [Matrix.vecMul, dotProduct] at this
    simpa [W, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  exact ⟨⟨A, W, mul_eq_one_comm.1 hWA, hWA⟩, rfl⟩

/-- **`K` is epic** (Lemma 3.3): the only division subring of `K` containing `ι(R)` is `K` itself. -/
theorem subfield_eq_top (h : IsUniversalFieldOfFractions K ι) {L : Subfield K}
    (hL : ∀ r, ι r ∈ L) : L = ⊤ := by
  let ι' : R →+* L := ι.codRestrict L hL
  have hι' : IsFullInverting ι' := by
    intro n A hA
    apply isUnit_of_isUnit_map_subfield L
    rw [Matrix.map_map]
    exact h.fullInverting n A hA
  obtain ⟨g, hg⟩ := h.exists_lift L ι' hι'
  have hext := h.ext K (L.subtype.comp g) (RingHom.id K) (by
    ext r
    simp [← RingHom.comp_apply, hg, ι'])
  rw [eq_top_iff]
  intro a _
  have := congrArg (fun φ : K →+* K => φ a) hext
  simp only [RingHom.comp_apply, RingHom.id_apply] at this
  rw [← this]
  exact (g a).2

/-- Membership form of `subfield_eq_top`. -/
theorem mem_of_forall (h : IsUniversalFieldOfFractions K ι) {L : Subfield K}
    (hL : ∀ r, ι r ∈ L) (a : K) : a ∈ L := by
  rw [h.subfield_eq_top hL]; exact Subfield.mem_top a

/-- **Honest endomorphisms extend** (paper: Theorem 3.1 applied after Lemma 3.4, in the proofs of
Proposition 3.5 and Lemma 3.6): an honest endomorphism of `R` extends to an endomorphism of
`K`. -/
theorem exists_extend_of_isHonest (h : IsUniversalFieldOfFractions K ι) {f : R →+* R}
    (hf : IsHonest f) : ∃ g : K →+* K, ∀ r, g (ι r) = ι (f r) := by
  obtain ⟨g, hg⟩ := h.exists_lift K (ι.comp f) (h.fullInverting.comp_of_isHonest hf)
  exact ⟨g, fun r => by simpa using congrArg (fun φ : R →+* K => φ r) hg⟩

/-- Central elements of `R` stay central in `K` (the centralizer is a division subring containing
`ι(R)`).  Used to make `K` an algebra over the scalars of `R`. -/
theorem commute_of_forall_commute (h : IsUniversalFieldOfFractions K ι) {r : R}
    (hr : ∀ s, Commute r s) (a : K) : Commute (ι r) a := by
  let L : Subfield K :=
    { Subring.centralizer {ι r} with
      inv_mem' := fun x hx => by
        have hx' : x ∈ Subring.centralizer {ι r} := hx
        change x⁻¹ ∈ Subring.centralizer {ι r}
        rw [Subring.mem_centralizer_iff] at hx' ⊢
        intro c hc
        exact (Commute.inv_right₀ (hx' c hc)).eq }
  have hmem : ∀ s, ι s ∈ L := by
    intro s
    change ι s ∈ Subring.centralizer {ι r}
    rw [Subring.mem_centralizer_iff]
    rintro c rfl
    rw [← map_mul, ← map_mul, (hr s).eq]
  have ha := h.mem_of_forall hmem a
  have ha' : a ∈ Subring.centralizer {ι r} := ha
  rw [Subring.mem_centralizer_iff] at ha'
  exact ha' _ rfl

end IsUniversalFieldOfFractions

end LeftPCI.FreeField
