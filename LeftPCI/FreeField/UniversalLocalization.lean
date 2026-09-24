module

public import Mathlib.Algebra.RingQuot
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.GroupWithZero.Units.Basic

@[expose] public section

/-! # The universal `Σ`-inverting ring `R_Σ` (Cohn, *FIR* Thm 7.2.4 p. 423; *SF* §4.1)

For a ring `R` and any family `Sig` of square matrices over `R` (indexed by `Fin n`), we build
the universal `Sig`-inverting ring `UnivLoc.Loc Sig` **by generators and relations**, as a
`RingQuot` of the free `ℤ`-algebra on

* one generator `ofR r` for every `r : R`, and
* one generator `gW A hA i j` for every `A ∈ Sig` and every entry `(i, j)` of its putative inverse,

subject to "`r ↦ ofR r` is a ring homomorphism" and `A · W = 1 = W · A` entrywise.
It lives in `R`'s universe.  Provided:

* `toLoc : R →+* Loc Sig`, `invMat A hA`, the two inverse identities and `isUnit_map_toLoc`;
* `lift f hf : Loc Sig →+* S` for any `Sig`-inverting `f : R →+* S` into a ring in **any**
  universe, `lift_comp_toLoc`, `lift_toLoc`, `lift_invMat`, `lift_unique`;
* `hom_ext` (homomorphisms out of `Loc Sig` are determined on `R`);
* `induction` (every element is built from `toLoc r` and entries of `invMat`s by `+`, `*`);
* `invMat_eq_inverse` (`invMat = Ring.inverse (A.map toLoc)`), `map_invMat`.
-/

namespace LeftPCI.FreeField.UnivLoc

universe u w

variable {R : Type u} [Ring R] (Sig : ∀ n : ℕ, Matrix (Fin n) (Fin n) R → Prop)

/-- Generators: elements of `R`, and one symbol per entry of the inverse of each `A ∈ Sig`. -/
abbrev Gen : Type u :=
  R ⊕ (Σ n : ℕ, {A : Matrix (Fin n) (Fin n) R // Sig n A} × Fin n × Fin n)

/-- The free `ℤ`-algebra on the generators. -/
abbrev FA : Type u := FreeAlgebra ℤ (Gen Sig)

/-- The generator attached to `r : R`. -/
def ofR (r : R) : FA Sig := FreeAlgebra.ι ℤ (Sum.inl r)

/-- The generator standing for the `(i, j)` entry of `A⁻¹`. -/
def gW {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (hA : Sig n A) (i j : Fin n) : FA Sig :=
  FreeAlgebra.ι ℤ (Sum.inr ⟨n, ⟨A, hA⟩, i, j⟩)

/-- The defining relations of `R_Σ`. -/
inductive Rel : FA Sig → FA Sig → Prop
  | add (r s : R) : Rel (ofR Sig (r + s)) (ofR Sig r + ofR Sig s)
  | mul (r s : R) : Rel (ofR Sig (r * s)) (ofR Sig r * ofR Sig s)
  | one : Rel (ofR Sig 1) 1
  | right_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (hA : Sig n A) (i j : Fin n) :
      Rel (∑ k, ofR Sig (A i k) * gW Sig A hA k j) ((1 : Matrix (Fin n) (Fin n) (FA Sig)) i j)
  | left_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (hA : Sig n A) (i j : Fin n) :
      Rel (∑ k, gW Sig A hA i k * ofR Sig (A k j)) ((1 : Matrix (Fin n) (Fin n) (FA Sig)) i j)

/-- The universal `Sig`-inverting ring. -/
def Loc : Type u := RingQuot (Rel Sig)

instance : Ring (Loc Sig) := inferInstanceAs (Ring (RingQuot (Rel Sig)))

instance : Inhabited (Loc Sig) := ⟨0⟩

/-- The quotient map from the free algebra. -/
noncomputable def mk : FA Sig →+* Loc Sig := RingQuot.mkRingHom (Rel Sig)

theorem mk_surjective : Function.Surjective (mk Sig) := RingQuot.mkRingHom_surjective _

theorem mk_rel {x y : FA Sig} (h : Rel Sig x y) : mk Sig x = mk Sig y :=
  RingQuot.mkRingHom_rel h

/-- The canonical map `R → R_Σ`. -/
noncomputable def toLoc : R →+* Loc Sig where
  toFun r := mk Sig (ofR Sig r)
  map_one' := by rw [mk_rel Sig Rel.one, map_one]
  map_mul' r s := by rw [mk_rel Sig (Rel.mul r s), map_mul]
  map_zero' := by
    have h := mk_rel Sig (Rel.add (0 : R) 0)
    rw [map_add, add_zero] at h
    exact (left_eq_add.1 h)
  map_add' r s := by rw [mk_rel Sig (Rel.add r s), map_add]

theorem toLoc_apply (r : R) : toLoc Sig r = mk Sig (ofR Sig r) := rfl

/-- The inverse of `A ∈ Sig` inside `R_Σ`. -/
noncomputable def invMat {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (hA : Sig n A) :
    Matrix (Fin n) (Fin n) (Loc Sig) :=
  Matrix.of fun i j => mk Sig (gW Sig A hA i j)

theorem invMat_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (hA : Sig n A) (i j : Fin n) :
    invMat Sig A hA i j = mk Sig (gW Sig A hA i j) := rfl

variable {Sig}

theorem map_toLoc_mul_invMat {n : ℕ} {A : Matrix (Fin n) (Fin n) R} (hA : Sig n A) :
    A.map (toLoc Sig) * invMat Sig A hA = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have := mk_rel Sig (Rel.right_inv A hA i j)
  rw [map_sum] at this
  simp only [map_mul] at this
  simpa [toLoc_apply, invMat_apply, Matrix.one_apply] using this

theorem invMat_mul_map_toLoc {n : ℕ} {A : Matrix (Fin n) (Fin n) R} (hA : Sig n A) :
    invMat Sig A hA * A.map (toLoc Sig) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have := mk_rel Sig (Rel.left_inv A hA i j)
  rw [map_sum] at this
  simp only [map_mul] at this
  simpa [toLoc_apply, invMat_apply, Matrix.one_apply] using this

theorem isUnit_map_toLoc {n : ℕ} {A : Matrix (Fin n) (Fin n) R} (hA : Sig n A) :
    IsUnit (A.map (toLoc Sig)) :=
  ⟨⟨_, _, map_toLoc_mul_invMat hA, invMat_mul_map_toLoc hA⟩, rfl⟩

/-- `invMat` is the ring inverse of `A.map toLoc`. -/
theorem invMat_eq_inverse {n : ℕ} {A : Matrix (Fin n) (Fin n) R} (hA : Sig n A) :
    invMat Sig A hA = Ring.inverse (A.map (toLoc Sig)) := by
  rw [Ring.inverse_of_isUnit (isUnit_map_toLoc hA)]
  exact (left_inv_eq_right_inv (invMat_mul_map_toLoc hA) (isUnit_map_toLoc hA).unit.mul_inv).trans
    rfl

/-- Any homomorphism out of `R_Σ` maps `invMat A` to the inverse of `A.map (g ∘ toLoc)`. -/
theorem map_invMat {S : Type w} [Ring S] (g : Loc Sig →+* S) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) R} (hA : Sig n A) :
    A.map (g.comp (toLoc Sig)) * (invMat Sig A hA).map g = 1 ∧
      (invMat Sig A hA).map g * A.map (g.comp (toLoc Sig)) = 1 := by
  constructor
  · rw [RingHom.coe_comp, ← Matrix.map_map, ← Matrix.map_mul, map_toLoc_mul_invMat hA,
      Matrix.map_one _ (map_zero g) (map_one g)]
  · rw [RingHom.coe_comp, ← Matrix.map_map, ← Matrix.map_mul, invMat_mul_map_toLoc hA,
      Matrix.map_one _ (map_zero g) (map_one g)]

/-- Composites `g ∘ toLoc` are `Sig`-inverting. -/
theorem isUnit_map_comp_toLoc {S : Type w} [Ring S] (g : Loc Sig →+* S) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) R} (hA : Sig n A) : IsUnit (A.map (g.comp (toLoc Sig))) :=
  ⟨⟨_, _, (map_invMat g hA).1, (map_invMat g hA).2⟩, rfl⟩

/-! ### The universal property -/

section lift

variable {S : Type w} [Ring S] (f : R →+* S) (hf : ∀ n A, Sig n A → IsUnit (A.map f))

/-- Values of the generators under the lift. -/
noncomputable def liftGen : Gen Sig → S
  | Sum.inl r => f r
  | Sum.inr ⟨n, ⟨A, hA⟩, i, j⟩ => ((hf n A hA).unit⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ).1 i j

/-- The lift on the free algebra. -/
noncomputable def liftFA : FA Sig →+* S :=
  (FreeAlgebra.lift ℤ (liftGen f hf)).toRingHom

theorem liftFA_ofR (r : R) : liftFA f hf (ofR Sig r) = f r := by
  change FreeAlgebra.lift ℤ (liftGen f hf) (FreeAlgebra.ι ℤ _) = _
  rw [FreeAlgebra.lift_ι_apply]; rfl

theorem liftFA_gW {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (hA : Sig n A) (i j : Fin n) :
    liftFA f hf (gW Sig A hA i j) = ((hf n A hA).unit⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ).1 i j := by
  change FreeAlgebra.lift ℤ (liftGen f hf) (FreeAlgebra.ι ℤ _) = _
  rw [FreeAlgebra.lift_ι_apply]; rfl

theorem liftFA_rel ⦃x y : FA Sig⦄ (h : Rel Sig x y) : liftFA f hf x = liftFA f hf y := by
  induction h with
  | add r s => simp [liftFA_ofR]
  | mul r s => simp [liftFA_ofR]
  | one => simp [liftFA_ofR]
  | right_inv A hA i j =>
    have h1 := (hf _ A hA).unit.mul_inv
    have := congrFun (congrFun (congrArg (fun M : Matrix _ _ S => M) h1) i) j
    rw [IsUnit.unit_spec, Matrix.mul_apply] at this
    rw [map_sum]
    simp only [map_mul, liftFA_ofR, liftFA_gW, Matrix.map_apply] at this ⊢
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  | left_inv A hA i j =>
    have h1 := (hf _ A hA).unit.inv_mul
    have := congrFun (congrFun (congrArg (fun M : Matrix _ _ S => M) h1) i) j
    rw [IsUnit.unit_spec, Matrix.mul_apply] at this
    rw [map_sum]
    simp only [map_mul, liftFA_ofR, liftFA_gW, Matrix.map_apply] at this ⊢
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

/-- **Universal property**: a `Sig`-inverting homomorphism factors through `R_Σ`. -/
noncomputable def lift : Loc Sig →+* S :=
  RingQuot.lift ⟨liftFA f hf, liftFA_rel f hf⟩

theorem lift_mk (x : FA Sig) : lift f hf (mk Sig x) = liftFA f hf x :=
  RingQuot.lift_mkRingHom_apply _ _ x

@[simp]
theorem lift_toLoc (r : R) : lift f hf (toLoc Sig r) = f r := by
  rw [toLoc_apply, lift_mk, liftFA_ofR]

theorem lift_comp_toLoc : (lift f hf).comp (toLoc Sig) = f :=
  RingHom.ext (lift_toLoc f hf)

@[simp]
theorem lift_invMat {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (hA : Sig n A) (i j : Fin n) :
    lift f hf (invMat Sig A hA i j) =
      ((hf n A hA).unit⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ).1 i j := by
  rw [invMat_apply, lift_mk, liftFA_gW]

theorem map_lift_invMat {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (hA : Sig n A) :
    (invMat Sig A hA).map (lift f hf) =
      ((hf n A hA).unit⁻¹ : (Matrix (Fin n) (Fin n) S)ˣ).1 := by
  ext i j; simp

end lift

/-- **Uniqueness**: homomorphisms out of `R_Σ` agreeing on `R` are equal. -/
theorem hom_ext {S : Type w} [Ring S] {g₁ g₂ : Loc Sig →+* S}
    (h : g₁.comp (toLoc Sig) = g₂.comp (toLoc Sig)) : g₁ = g₂ := by
  apply RingQuot.ringQuot_ext
  have key : (g₁.comp (mk Sig)).toIntAlgHom = (g₂.comp (mk Sig)).toIntAlgHom := by
    apply FreeAlgebra.hom_ext
    funext x
    rcases x with r | ⟨n, ⟨A, hA⟩, i, j⟩
    · exact RingHom.congr_fun h r
    · -- uniqueness of two-sided inverses
      have e₁ := map_invMat g₁ hA
      have e₂ := map_invMat g₂ hA
      rw [h] at e₁
      have hW : (invMat Sig A hA).map g₁ = (invMat Sig A hA).map g₂ := by
        calc (invMat Sig A hA).map g₁
            = (invMat Sig A hA).map g₁ * (A.map (g₂.comp (toLoc Sig)) *
                (invMat Sig A hA).map g₂) := by rw [e₂.1, mul_one]
          _ = ((invMat Sig A hA).map g₁ * A.map (g₂.comp (toLoc Sig))) *
                (invMat Sig A hA).map g₂ := by rw [mul_assoc]
          _ = (invMat Sig A hA).map g₂ := by rw [e₁.2, one_mul]
      exact congrFun (congrFun hW i) j
  exact RingHom.ext fun x => AlgHom.congr_fun key x

theorem lift_unique {S : Type w} [Ring S] (f : R →+* S) (hf : ∀ n A, Sig n A → IsUnit (A.map f))
    (g : Loc Sig →+* S) (hg : g.comp (toLoc Sig) = f) : g = lift f hf :=
  hom_ext (by rw [hg, lift_comp_toLoc])

@[simp]
theorem lift_comp_toLoc_eq {S : Type w} [Ring S] (g : Loc Sig →+* S) :
    lift (g.comp (toLoc Sig)) (fun _ _ hA => isUnit_map_comp_toLoc g hA) = g :=
  (lift_unique _ _ g rfl).symm

/-- **Induction principle**: everything is generated by `toLoc R` and the entries of the
`invMat`s under `+` and `*`. -/
@[elab_as_elim]
theorem induction {P : Loc Sig → Prop} (h_of : ∀ r, P (toLoc Sig r))
    (h_inv : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R) (hA : Sig n A) (i j : Fin n),
      P (invMat Sig A hA i j))
    (h_add : ∀ a b, P a → P b → P (a + b)) (h_mul : ∀ a b, P a → P b → P (a * b))
    (p : Loc Sig) : P p := by
  obtain ⟨x, rfl⟩ := mk_surjective Sig p
  induction x using FreeAlgebra.induction with
  | grade0 z =>
    have : mk Sig (algebraMap ℤ (FA Sig) z) = toLoc Sig (z : R) := by
      rw [eq_intCast, map_intCast, map_intCast]
    rw [this]; exact h_of _
  | grade1 g =>
    rcases g with r | ⟨n, ⟨A, hA⟩, i, j⟩
    · exact h_of r
    · exact h_inv n A hA i j
  | mul a b ha hb => rw [map_mul]; exact h_mul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact h_add _ _ ha hb

end LeftPCI.FreeField.UnivLoc
