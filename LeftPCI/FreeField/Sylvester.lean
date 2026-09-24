module

public import LeftPCI.FreeField.FullCalculus
public import LeftPCI.FreeAlgebra.Fir
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

/-! # Semifirs satisfy the law of nullity and (FC)

* `lawOfNullity` — Cohn's **law of nullity** (*Free Ideal Rings and Localization in General
  Rings*, Prop 5.5.1 p. 290; *Skew Fields*, Prop 4.5.5 p. 180): over a ring whose f.g. left
  ideals are free and which has IBN, `P * Q = 0` with `P : m × k`, `Q : k × s` forces
  `ρP + ρQ ≤ k` (`ρ` = inner rank, expressed via `FactorsThrough`).

  The proof is not Cohn's (he goes through trivializable relations, FIR Prop 3.1.3); it is
  the split-kernel argument: `φ := Q.vecMulLinear : Rᵏ → Rˢ` has f.g., hence free, hence
  projective range, so `Rᵏ ≃ ker φ × range φ`; both are free of finite ranks `a`, `b` with
  `a + b = k` by IBN; the rows of `P` lie in `ker φ` (since `PQ = 0`) and the rows of `Q` lie
  in `range φ`, so `P` factors through `a` and `Q` through `b`.
* `fullClosed_of_lawOfNullity` — FIR Cor 5.5.2 (products of full matrices are full) and
  Lemma 5.5.3 (5) (`ρ(A ⊕ B) = ρA + ρB`), giving the class `FullClosed`.
* `fullClosed_of_semifir`, and the instance `fullClosed_freeAlgebra`
  (via Cohn's theorem that `k⟨X⟩` is a fir, `FA.free_of_ideal`).
-/

namespace LeftPCI.FreeField

open _root_.Matrix

universe u v

/-! ## Module-theoretic input

Two standard facts: a linear map with projective range splits, and over a ring whose f.g. left
ideals are free, f.g. submodules of `Rⁿ` are free. -/

section SemifirModules

variable {R : Type*} [Ring R]

/-- A linear map with projective range splits: `M ≃ₗ ker f × range f`, by an equivalence
that is the canonical inclusion on `ker f`. -/
theorem semifir_split_ker' {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    [Module.Projective R ↥(LinearMap.range f)] :
    ∃ e : M ≃ₗ[R] ↥(LinearMap.ker f) × ↥(LinearMap.range f),
      ∀ (x : M) (hx : x ∈ LinearMap.ker f), e x = (⟨x, hx⟩, 0) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict LinearMap.id
    f.surjective_rangeRestrict
  have hexact : Function.Exact ⇑(LinearMap.ker f).subtype ⇑f.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  obtain ⟨e, he, -⟩ := hexact.splitSurjectiveEquiv (Submodule.injective_subtype _) ⟨s, hs⟩
  refine ⟨e, fun x hx => ?_⟩
  have h1 := LinearMap.congr_fun he ⟨x, hx⟩
  simp only [Submodule.subtype_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearMap.inl_apply] at h1
  have h2 := congrArg (⇑e) h1
  rwa [LinearEquiv.apply_symm_apply] at h2

/-- In a ring all of whose f.g. left ideals are free, every f.g. submodule of `Fin n → R` is
free (Cohn, FIR Theorem 1.1.1, semifir case). -/
theorem semifir_free_fg_submodule'
    (hfree : ∀ I : Ideal R, I.FG → Module.Free R I) :
    ∀ (n : ℕ) (M : Submodule R (Fin n → R)), M.FG → Module.Free R ↥M := by
  intro n
  induction n with
  | zero =>
    intro M _
    have : Subsingleton ↥M := ⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩
    exact Module.Free.of_subsingleton R ↥M
  | succ n ih =>
    intro M hM
    have : Module.Finite R ↥M := Module.Finite.iff_fg.mpr hM
    set ψ : ↥M →ₗ[R] R := (LinearMap.proj (Fin.last n)).comp M.subtype with hψdef
    have : Module.Finite R ↥(LinearMap.range ψ) := Module.Finite.range ψ
    have : Module.Free R ↥(LinearMap.range ψ) :=
      hfree (LinearMap.range ψ) (Module.Finite.iff_fg.mp ‹_›)
    have : Module.Projective R ↥(LinearMap.range ψ) := Module.Projective.of_free
    obtain ⟨e, -⟩ := semifir_split_ker' ψ
    have : Module.Finite R ↥(LinearMap.ker ψ) :=
      Module.Finite.of_surjective ((LinearMap.fst R _ _).comp e.toLinearMap)
        (Prod.fst_surjective.comp e.surjective)
    set j : ↥(LinearMap.ker ψ) →ₗ[R] (Fin n → R) :=
      (LinearMap.funLeft R R Fin.castSucc).comp (M.subtype.comp (LinearMap.ker ψ).subtype)
      with hjdef
    have hjinj : Function.Injective j := by
      intro a b hab
      have ha := LinearMap.mem_ker.mp a.2
      have hb := LinearMap.mem_ker.mp b.2
      simp only [hψdef, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.proj_apply] at ha hb
      simp only [hjdef, LinearMap.comp_apply, Submodule.subtype_apply] at hab
      apply Subtype.ext; apply Subtype.ext
      funext i
      induction i using Fin.lastCases with
      | last => rw [ha, hb]
      | cast i => exact congrFun hab i
    have : Module.Finite R ↥(LinearMap.range j) := Module.Finite.range j
    have : Module.Free R ↥(LinearMap.range j) := ih _ (Module.Finite.iff_fg.mp ‹_›)
    have : Module.Free R ↥(LinearMap.ker ψ) :=
      Module.Free.of_equiv (LinearEquiv.ofInjective j hjinj).symm
    exact Module.Free.of_equiv e.symm

/-- Index-general version of `semifir_free_fg_submodule'`. -/
theorem semifir_free_fg_submodule_pi
    (hfree : ∀ I : Ideal R, I.FG → Module.Free R I) {k : Type*} [Finite k]
    (M : Submodule R (k → R)) (hM : M.FG) : Module.Free R ↥M := by
  have := Fintype.ofFinite k
  let e : (k → R) ≃ₗ[R] (Fin (Fintype.card k) → R) :=
    LinearEquiv.funCongrLeft R R (Fintype.equivFin k).symm
  have := semifir_free_fg_submodule' hfree (Fintype.card k) (M.map e.toLinearMap) (hM.map _)
  exact Module.Free.of_equiv (e.submoduleMap M).symm

end SemifirModules

/-! ## The law of nullity -/

variable {R : Type u} [Ring R]

/-- If every row of `M` lies in a submodule `N` with a basis of size `a`, then `M` factors
through `a`. -/
theorem factorsThrough_of_rows_mem {m n : Type*} {M : Matrix m n R} {N : Submodule R (n → R)}
    {a : ℕ} (b : Module.Basis (Fin a) R N) (h : ∀ i, M i ∈ N) : FactorsThrough M a := by
  refine ⟨Matrix.of fun i j => b.repr ⟨M i, h i⟩ j, Matrix.of fun j l => (b j : n → R) l, ?_⟩
  ext i l
  have h1 := congrFun (congrArg Subtype.val (b.sum_repr ⟨M i, h i⟩)) l
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h1
  rw [mul_apply]
  simpa only [of_apply] using h1

/-- **Law of nullity** (Cohn FIR Prop 5.5.1 p. 290, SF Prop 4.5.5 p. 180), for rings whose f.g.
left ideals are free and which have IBN: if `P * Q = 0` then `ρP + ρQ ≤ k`. -/
theorem lawOfNullity (hfree : ∀ I : Ideal R, I.FG → Module.Free R I) [InvariantBasisNumber R]
    {m k s : Type*} [Fintype k] [Finite s]
    {P : Matrix m k R} {Q : Matrix k s R} (hPQ : P * Q = 0) :
    ∃ a b : ℕ, a + b ≤ Fintype.card k ∧ FactorsThrough P a ∧ FactorsThrough Q b := by
  classical
  set φ : (k → R) →ₗ[R] (s → R) := Q.vecMulLinear with hφ
  have : Module.Finite R ↥(LinearMap.range φ) := Module.Finite.range φ
  have : Module.Free R ↥(LinearMap.range φ) :=
    semifir_free_fg_submodule_pi hfree _ (Module.Finite.iff_fg.mp ‹_›)
  have : Module.Projective R ↥(LinearMap.range φ) := Module.Projective.of_free
  obtain ⟨e, -⟩ := semifir_split_ker' φ
  have : Module.Finite R ↥(LinearMap.ker φ) :=
    Module.Finite.of_surjective ((LinearMap.fst R _ _).comp e.toLinearMap)
      (Prod.fst_surjective.comp e.surjective)
  have : Module.Free R ↥(LinearMap.ker φ) :=
    semifir_free_fg_submodule_pi hfree _ (Module.Finite.iff_fg.mp ‹_›)
  have := Module.Free.ChooseBasisIndex.fintype R ↥(LinearMap.ker φ)
  have := Module.Free.ChooseBasisIndex.fintype R ↥(LinearMap.range φ)
  let bK := (Module.Free.chooseBasis R ↥(LinearMap.ker φ)).reindex (Fintype.equivFin _)
  let bI := (Module.Free.chooseBasis R ↥(LinearMap.range φ)).reindex (Fintype.equivFin _)
  refine ⟨_, _, le_of_eq ?_, factorsThrough_of_rows_mem bK ?_, factorsThrough_of_rows_mem bI ?_⟩
  · exact eq_of_fin_equiv R ((LinearEquiv.funCongrLeft R R finSumFinEquiv).trans
      ((LinearEquiv.sumArrowLequivProdArrow _ _ R R).trans
        ((bK.equivFun.symm.prodCongr bI.equivFun.symm).trans
          (e.symm.trans (LinearEquiv.funCongrLeft R R (Fintype.equivFin k).symm)))))
  · intro i
    rw [LinearMap.mem_ker, hφ, vecMulLinear_apply]
    funext l
    simpa [vecMul, dotProduct, mul_apply] using congrFun (congrFun hPQ i) l
  · intro j
    refine ⟨Pi.single j 1, ?_⟩
    rw [hφ, vecMulLinear_apply]
    funext l
    simp [vecMul, dotProduct, Pi.single_apply]

/-- The law of nullity, as a property of a ring (index types in `Type`, enough for
`FullClosed`). -/
def HasLawOfNullity (R : Type u) [Ring R] : Prop :=
  ∀ {m k s : Type} [Fintype k] [Finite s] (P : Matrix m k R) (Q : Matrix k s R), P * Q = 0 →
    ∃ a b : ℕ, a + b ≤ Fintype.card k ∧ FactorsThrough P a ∧ FactorsThrough Q b

/-- The law of nullity implies (FC): products of full matrices are full (FIR Cor 5.5.2 p. 291)
and diagonal sums of full matrices are full (FIR Lemma 5.5.3 (5) p. 291–292). -/
theorem fullClosed_of_lawOfNullity [Nontrivial R] (h : HasLawOfNullity R) : FullClosed R := by
  refine ⟨inferInstance, ?_, ?_⟩
  · -- if `AB = P'Q'` through `r < n`, then `(A | P') (B ; -Q') = 0`
    intro ι _ _ A B hA hB r hr ⟨P', Q', hPQ⟩
    obtain ⟨a, b, hab, hPa, hQb⟩ := h (Matrix.fromCols A P') (Matrix.fromRows B (-Q'))
      (by rw [Matrix.fromCols_mul_fromRows, Matrix.mul_neg, hPQ, add_neg_cancel])
    have hA' : (Matrix.fromCols A P').submatrix id Sum.inl = A := by ext; simp
    have hB' : (Matrix.fromRows B (-Q')).submatrix Sum.inl id = B := by ext; simp
    have ha : Fintype.card ι ≤ a := by
      by_contra hlt
      exact hA a (by omega) (hA' ▸ hPa.submatrix id Sum.inl)
    have hb : Fintype.card ι ≤ b := by
      by_contra hlt
      exact hB b (by omega) (hB' ▸ hQb.submatrix Sum.inl id)
    simp only [Fintype.card_sum, Fintype.card_fin] at hab
    omega
  · -- partition a factorization of `A ⊕ B` as `(P₁; P₂)(Q₁ Q₂)`; then `P₁ Q₂ = 0`
    intro ι κ _ _ _ _ A B hA hB r hr ⟨P, Q, hPQ⟩
    have hent : ∀ i j, (P * Q) i j = Matrix.fromBlocks A 0 0 B i j := fun i j => by rw [hPQ]
    obtain ⟨a, b, hab, hPa, hQb⟩ := h (P.submatrix Sum.inl id) (Q.submatrix id Sum.inr) (by
      ext i j
      have := hent (Sum.inl i) (Sum.inr j)
      simp only [mul_apply, fromBlocks_apply₁₂, Matrix.zero_apply] at this
      simpa [mul_apply] using this)
    have hA' : P.submatrix Sum.inl id * Q.submatrix id Sum.inl = A := by
      ext i j
      simpa [mul_apply] using hent (Sum.inl i) (Sum.inl j)
    have hB' : P.submatrix Sum.inr id * Q.submatrix id Sum.inr = B := by
      ext i j
      simpa [mul_apply] using hent (Sum.inr i) (Sum.inr j)
    have ha : Fintype.card ι ≤ a := by
      by_contra hlt
      exact hA a (by omega) (hA' ▸ hPa.mul_right _)
    have hb : Fintype.card κ ≤ b := by
      by_contra hlt
      exact hB b (by omega) (hB' ▸ hQb.mul_left _)
    simp only [Fintype.card_sum, Fintype.card_fin] at hab hr
    omega

/-- A ring whose f.g. left ideals are free and which has IBN (a semifir) satisfies (FC)
(FIR Thm 7.5.13, via the law of nullity). -/
theorem fullClosed_of_semifir (hfree : ∀ I : Ideal R, I.FG → Module.Free R I)
    [InvariantBasisNumber R] : FullClosed R := by
  have := nontrivial_of_invariantBasisNumber R
  exact fullClosed_of_lawOfNullity fun _ _ hPQ => lawOfNullity hfree hPQ

/-- Freeness of all left ideals transfers along a ring isomorphism: pull `I` back to
`J := I.comap φ`, which is free, and `φ` restricts to a `φ`-semilinear equivalence `J ≃ I`. -/
theorem free_of_ideal_of_ringEquiv {R S : Type*} [Ring R] [Ring S] (φ : R ≃+* S)
    (h : ∀ I : Ideal R, Module.Free R I) (I : Ideal S) : Module.Free S I := by
  set J : Ideal R := I.comap (φ : R →+* S) with hJdef
  have hmemJ : ∀ x : R, x ∈ J ↔ φ x ∈ I := fun _ ↦ Iff.rfl
  have hJfree := h J
  have := RingHomInvPair.of_ringEquiv φ
  have := RingHomInvPair.of_ringEquiv_symm φ
  let e : J ≃ₛₗ[(φ : R →+* S)] I :=
    { toFun := fun x ↦ ⟨φ x.1, (hmemJ x.1).mp x.2⟩
      invFun := fun y ↦ ⟨φ.symm y.1, (hmemJ _).mpr (by simp)⟩
      left_inv := fun x ↦ by ext; simp
      right_inv := fun y ↦ by ext; simp
      map_add' := fun x y ↦ by ext; simp
      map_smul' := fun r x ↦ by ext; simp }
  exact Module.Free.of_equiv e

/-- The free algebra `k⟨X⟩` over a field satisfies (FC): it is a fir (`FA.free_of_ideal`,
Cohn FIR Thm 2.5.3 + 2.4.6), in particular a semifir, and it has invariant basis number
(`FA.invariantBasisNumber_fa`); both are transported from the word model `FA k X` along
`FreeAlgebra.equivMonoidAlgebraFreeMonoid`. -/
instance fullClosed_freeAlgebra (k : Type u) [Field k] (X : Type v) :
    FullClosed (FreeAlgebra k X) := by
  let φ := (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := k) (X := X)).symm.toRingEquiv
  have : InvariantBasisNumber (FA k X) := FA.invariantBasisNumber_fa
  have : InvariantBasisNumber (FreeAlgebra k X) := invariantBasisNumber_of_ringHom φ.symm.toRingHom
  exact fullClosed_of_semifir (fun I _ => free_of_ideal_of_ringEquiv φ (fun J => FA.free_of_ideal J) I)

end LeftPCI.FreeField
