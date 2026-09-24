module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.End
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Ext
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Tactic.NoncommRing

@[expose] public section

universe u v

namespace LeftPCI

/-! # Ore extensions `k[t; σ, δ]`

For a ring `k` (**not** assumed commutative), a ring endomorphism `σ : k →+* k` and a
`σ`-derivation `δ`, the *Ore extension* (skew polynomial ring) `k[t; σ, δ]` is the free left
`k`-module on `1, t, t², …` with multiplication forced by

  `t * a = σ a * t + δ a`  for `a ∈ k`.

This is the general two-parameter Ore extension.  Its two degenerate cases are already available:

* `δ = 0` is Mathlib's `SkewPolynomial R` (`= SkewMonoidAlgebra R (Multiplicative ℕ)`, with the
  twist read off a `MulSemiringAction (Multiplicative ℕ) R`);
* `σ = id` is the ring of differential polynomials `k[t; d]`.

Neither covers the *simultaneous* twist-and-derivation case, which is what the rings
`K[t; σ, δ]` of the paper `paper/pci_counterexample.tex` are, so it is carried out here.

## Construction

Writing out a product in the `t`-basis produces a sum over all the ways of
interleaving `σ`'s and `δ`'s, and proving associativity of *that* formula directly is painful.
Instead the multiplication is **defined as an action**, so associativity becomes composition of
operators, which is associative for free:

* `lmul a` is left multiplication by `a : k` on `ℕ →₀ k`;
* `twistShift σ` sends `single n a` to `single (n+1) (σ a)`;
* `coeffDeriv δ` applies `δ` to every coefficient;
* `Xop σ δ = twistShift σ + coeffDeriv δ` is "left multiplication by `t`" — indeed
  `t * (b tⁿ) = (t b) tⁿ = (σ b * t + δ b) tⁿ = (σ b) tⁿ⁺¹ + (δ b) tⁿ`;
* `act σ δ : (ℕ →₀ k) →+ AddMonoid.End (ℕ →₀ k)` sends `f` to "left multiplication by `f`",
  namely `Σ_n lmul (f n) * (Xop σ δ) ^ n`, and the product is `f * g := act σ δ f g`.

The single computation that carries the whole file is `Xop_mul_lmul`:

  `Xop σ δ * lmul a = lmul (σ a) * Xop σ δ + lmul (δ a)`,

which is the twisted Leibniz rule.  From it one gets `act_lmul` and `act_Xop`, hence
`act (f * g) = act f * act g` (`act_act`), hence associativity.

## Scope

Only the ring structure is built here: the `Ring` instance, the coefficient embedding `C`, the
variable `X`, the defining relation `X_mul_C`, and the left `k`-basis `monomial_eq`.  Degree
theory, the domain property and the left-principal-ideal property are developed in
`LeftPCI/OrePoly/Degree.lean` and `LeftPCI/OrePoly/Division.lean`.
-/

/-! ## `σ`-derivations of a possibly noncommutative ring -/

/-- A **`σ`-derivation** of a ring `k`, for a ring endomorphism `σ : k →+* k`: an additive map
satisfying the twisted Leibniz rule `δ (a * b) = σ a * δ b + δ a * b`.

This is Cozzens–Faith's "`ρ`-derivation" (*Simple Noetherian Rings*, §3 p. 53):
*`δ(a + b) = δ(a) + δ(b)` and `δ(ab) = ρ(a)δ(b) + δ(a)b`*.

With `σ = id` this is `LeftPCI.RingDerivation`; Mathlib's `Derivation R A M` is the untwisted
notion and additionally insists that `A` be commutative. -/
structure OreDerivation (k : Type u) [Ring k] (σ : k →+* k) where
  /-- The underlying function. -/
  toFun : k → k
  /-- A `σ`-derivation is additive. -/
  map_add' : ∀ a b : k, toFun (a + b) = toFun a + toFun b
  /-- The twisted Leibniz rule `δ (a * b) = σ a * δ b + δ a * b`. -/
  leibniz' : ∀ a b : k, toFun (a * b) = σ a * toFun b + toFun a * b

namespace OreDerivation

variable {k : Type u} [Ring k] {σ : k →+* k}

instance instFunLike : FunLike (OreDerivation k σ) k k where
  coe := OreDerivation.toFun
  coe_injective f g h := by cases f; cases g; congr

@[simp] theorem coe_mk (f : k → k) (h₁ h₂) : ⇑(OreDerivation.mk (σ := σ) f h₁ h₂) = f := rfl

@[ext] theorem ext {δ₁ δ₂ : OreDerivation k σ} (h : ∀ a, δ₁ a = δ₂ a) : δ₁ = δ₂ :=
  DFunLike.ext _ _ h

@[simp] theorem map_add (δ : OreDerivation k σ) (a b : k) : δ (a + b) = δ a + δ b := δ.map_add' a b

theorem leibniz (δ : OreDerivation k σ) (a b : k) : δ (a * b) = σ a * δ b + δ a * b :=
  δ.leibniz' a b

@[simp] theorem map_zero (δ : OreDerivation k σ) : δ 0 = 0 := by
  have h : δ 0 + δ 0 = δ 0 := by
    have h0 := (δ.map_add' 0 0).symm
    rwa [add_zero] at h0
  exact add_eq_left.mp h

@[simp] theorem map_one (δ : OreDerivation k σ) : δ 1 = 0 := by
  have h1 := δ.leibniz (1 : k) 1
  simp only [mul_one, _root_.map_one, one_mul] at h1
  exact add_eq_left.mp h1.symm

@[simp] theorem map_neg (δ : OreDerivation k σ) (a : k) : δ (-a) = -δ a := by
  have h : δ (-a) + δ a = 0 := by rw [← δ.map_add, neg_add_cancel, δ.map_zero]
  exact eq_neg_of_add_eq_zero_left h

@[simp] theorem map_sub (δ : OreDerivation k σ) (a b : k) : δ (a - b) = δ a - δ b := by
  rw [sub_eq_add_neg, δ.map_add, δ.map_neg, ← sub_eq_add_neg]

/-- A `σ`-derivation as an additive monoid homomorphism. -/
def toAddMonoidHom (δ : OreDerivation k σ) : k →+ k := AddMonoidHom.mk' δ δ.map_add'

@[simp] theorem coe_toAddMonoidHom (δ : OreDerivation k σ) : ⇑δ.toAddMonoidHom = ⇑δ := rfl

/-- The **inner** `σ`-derivation attached to `c : k`, namely `a ↦ σ a * c - c * a`.

By a lemma of Cohn, over a *commutative* `k` every `σ`-derivation is of this form unless `σ` is
an inner automorphism (Cohn 1977, §2; cf. §6 of the paper). -/
def inner (σ : k →+* k) (c : k) : OreDerivation k σ where
  toFun a := σ a * c - c * a
  map_add' a b := by simp only [_root_.map_add]; noncomm_ring
  leibniz' a b := by simp only [_root_.map_mul]; noncomm_ring

@[simp] theorem inner_apply (σ : k →+* k) (c a : k) : inner σ c a = σ a * c - c * a := rfl

/-- Transport a `σ`-derivation along a ring isomorphism. -/
def congr {k : Type u} {k' : Type v} [Ring k] [Ring k'] (e : k ≃+* k') {σ : k →+* k}
    (δ : OreDerivation k σ) :
    OreDerivation k' ((e : k →+* k').comp (σ.comp (e.symm : k' →+* k))) where
  toFun a := e (δ (e.symm a))
  map_add' a b := by simp
  leibniz' a b := by
    change e (δ (e.symm (a * b))) = e (σ (e.symm a)) * e (δ (e.symm b)) + e (δ (e.symm a)) * b
    rw [map_mul, δ.leibniz, _root_.map_add, _root_.map_mul, _root_.map_mul,
      RingEquiv.apply_symm_apply]

end OreDerivation

/-! ## The operators making up the multiplication -/

namespace OrePoly

variable {k : Type u} [Ring k] {σ : k →+* k}

/-- Two additive endomorphisms of `ℕ →₀ k` agreeing on monomials are equal. -/
theorem end_ext {f g : AddMonoid.End (ℕ →₀ k)}
    (h : ∀ (n : ℕ) (a : k), f (Finsupp.single n a) = g (Finsupp.single n a)) : f = g :=
  Finsupp.addHom_ext h

theorem end_mul_apply (f g : AddMonoid.End (ℕ →₀ k)) (p : ℕ →₀ k) : (f * g) p = f (g p) := rfl

theorem end_add_apply (f g : AddMonoid.End (ℕ →₀ k)) (p : ℕ →₀ k) : (f + g) p = f p + g p := rfl

/-- Left multiplication by `a : k` on `ℕ →₀ k`. -/
noncomputable def lmul (a : k) : AddMonoid.End (ℕ →₀ k) := Module.toAddMonoidEnd k (ℕ →₀ k) a

theorem lmul_apply (a : k) (p : ℕ →₀ k) : lmul a p = a • p := rfl

@[simp] theorem lmul_single (a : k) (n : ℕ) (b : k) :
    lmul a (Finsupp.single n b) = Finsupp.single n (a * b) := by
  rw [lmul_apply, Finsupp.smul_single, smul_eq_mul]

theorem lmul_mul (a b : k) : lmul (a * b) = lmul a * lmul b :=
  map_mul (Module.toAddMonoidEnd k (ℕ →₀ k)) a b

@[simp] theorem lmul_one : lmul (1 : k) = 1 := map_one (Module.toAddMonoidEnd k (ℕ →₀ k))

theorem lmul_add (a b : k) : lmul (a + b) = lmul a + lmul b :=
  map_add (Module.toAddMonoidEnd k (ℕ →₀ k)) a b

/-- The **twisted shift** `single n a ↦ single (n+1) (σ a)`: multiplication by `t` in the
derivation-free part. -/
noncomputable def twistShift (σ : k →+* k) : AddMonoid.End (ℕ →₀ k) :=
  (Finsupp.mapDomain.addMonoidHom Nat.succ).comp (Finsupp.mapRange.addMonoidHom σ.toAddMonoidHom)

@[simp] theorem twistShift_single (n : ℕ) (a : k) :
    twistShift σ (Finsupp.single n a) = Finsupp.single (n + 1) (σ a) := by
  change Finsupp.mapDomain Nat.succ (Finsupp.mapRange σ σ.map_zero (Finsupp.single n a)) = _
  rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]

/-- Apply the `σ`-derivation to every coefficient. -/
noncomputable def coeffDeriv (δ : OreDerivation k σ) : AddMonoid.End (ℕ →₀ k) :=
  Finsupp.mapRange.addMonoidHom δ.toAddMonoidHom

@[simp] theorem coeffDeriv_single (δ : OreDerivation k σ) (n : ℕ) (a : k) :
    coeffDeriv δ (Finsupp.single n a) = Finsupp.single n (δ a) :=
  Finsupp.mapRange_single (hf := δ.toAddMonoidHom.map_zero)

/-- Left multiplication by `t`: `t * (b tⁿ) = (σ b) tⁿ⁺¹ + (δ b) tⁿ`. -/
noncomputable def Xop (δ : OreDerivation k σ) : AddMonoid.End (ℕ →₀ k) :=
  twistShift σ + coeffDeriv δ

@[simp] theorem Xop_single (δ : OreDerivation k σ) (n : ℕ) (a : k) :
    Xop δ (Finsupp.single n a) = Finsupp.single (n + 1) (σ a) + Finsupp.single n (δ a) := by
  rw [Xop, end_add_apply, twistShift_single, coeffDeriv_single]

/-- **The twisted Leibniz rule, as an operator identity.**  This is the only place the defining
relation `t * a = σ a * t + δ a` enters. -/
theorem Xop_mul_lmul (δ : OreDerivation k σ) (a : k) :
    Xop δ * lmul a = lmul (σ a) * Xop δ + lmul (δ a) := by
  refine end_ext fun n b => ?_
  rw [end_mul_apply, lmul_single, Xop_single, end_add_apply, end_mul_apply, Xop_single,
    map_add, lmul_single, lmul_single, lmul_single, δ.leibniz, map_mul, Finsupp.single_add]
  abel

/-! ## Left multiplication by a polynomial -/

variable (δ : OreDerivation k σ)

/-- `act δ f` is "left multiplication by the polynomial `f`", `Σₙ lmul (f n) * (Xop δ) ^ n`. -/
noncomputable def act : (ℕ →₀ k) →+ AddMonoid.End (ℕ →₀ k) :=
  Finsupp.liftAddHom fun n =>
    (AddMonoidHom.mulRight (Xop δ ^ n)).comp (Module.toAddMonoidEnd k (ℕ →₀ k)).toAddMonoidHom

@[simp] theorem act_single (n : ℕ) (a : k) : act δ (Finsupp.single n a) = lmul a * Xop δ ^ n := by
  rw [act, Finsupp.liftAddHom_apply, Finsupp.sum_single_index] <;> simp [lmul]

theorem act_lmul (a : k) (p : ℕ →₀ k) : act δ (lmul a p) = lmul a * act δ p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq, mul_add]
  | single n b => rw [lmul_single, act_single, act_single, ← mul_assoc, ← lmul_mul]

theorem act_Xop (p : ℕ →₀ k) : act δ (Xop δ p) = Xop δ * act δ p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq, mul_add]
  | single n b =>
      rw [Xop_single, map_add, act_single, act_single, act_single]
      rw [show Xop δ * (lmul b * Xop δ ^ n) = Xop δ * lmul b * Xop δ ^ n from
        (mul_assoc _ _ _).symm, Xop_mul_lmul, add_mul, mul_assoc, ← pow_succ']

theorem act_Xop_pow (m : ℕ) (p : ℕ →₀ k) : act δ ((Xop δ ^ m) p) = Xop δ ^ m * act δ p := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', end_mul_apply, act_Xop, ih, ← mul_assoc, ← pow_succ']

/-- **`act` is multiplicative**: left multiplication by `f * g` is left multiplication by `f`
composed with left multiplication by `g`.  This is where associativity comes from. -/
theorem act_act (f g : ℕ →₀ k) : act δ (act δ f g) = act δ f * act δ g := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
      rw [map_add, end_add_apply, map_add, h₁, h₂, add_mul]
  | single n a =>
      rw [act_single, end_mul_apply, act_lmul, act_Xop_pow]
      exact (mul_assoc _ _ _).symm

theorem Xop_pow_single_one (m n : ℕ) :
    (Xop δ ^ m) (Finsupp.single n (1 : k)) = Finsupp.single (n + m) 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', end_mul_apply, ih, Xop_single, OreDerivation.map_one,
        Finsupp.single_zero, add_zero, map_one, Nat.add_assoc]

/-! ### The ring axioms, stated for `act` -/

theorem act_mul_assoc (f g h : ℕ →₀ k) : act δ (act δ f g) h = act δ f (act δ g h) := by
  rw [act_act, end_mul_apply]

theorem act_one : act δ (Finsupp.single 0 (1 : k)) = 1 := by
  rw [act_single, pow_zero, lmul_one, mul_one]

theorem act_one_mul (f : ℕ →₀ k) : act δ (Finsupp.single 0 1) f = f := by
  rw [act_one]; rfl

theorem act_mul_one (f : ℕ →₀ k) : act δ f (Finsupp.single 0 1) = f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [map_zero]; rfl
  | add f₁ f₂ h₁ h₂ => rw [map_add, end_add_apply, h₁, h₂]
  | single n a =>
      rw [act_single, end_mul_apply, Xop_pow_single_one, zero_add, lmul_single, mul_one]

theorem act_zero_mul (f : ℕ →₀ k) : act δ 0 f = 0 := by rw [map_zero]; rfl

theorem act_mul_zero (f : ℕ →₀ k) : act δ f 0 = 0 := map_zero (act δ f)

theorem act_left_distrib (f g h : ℕ →₀ k) : act δ f (g + h) = act δ f g + act δ f h :=
  map_add (act δ f) g h

theorem act_right_distrib (f g h : ℕ →₀ k) : act δ (f + g) h = act δ f h + act δ g h := by
  rw [map_add]; rfl

/-! ### Products of monomials that the ring structure is described by -/

theorem act_single_zero_single_zero (a b : k) :
    act δ (Finsupp.single 0 a) (Finsupp.single 0 b) = Finsupp.single 0 (a * b) := by
  rw [act_single, pow_zero, mul_one, lmul_single]

theorem act_single_zero_single (a : k) (n : ℕ) :
    act δ (Finsupp.single 0 a) (Finsupp.single n 1) = Finsupp.single n a := by
  rw [act_single, pow_zero, mul_one, lmul_single, mul_one]

theorem act_single_one_single_zero (a : k) :
    act δ (Finsupp.single 1 1) (Finsupp.single 0 a)
      = Finsupp.single 1 (σ a) + Finsupp.single 0 (δ a) := by
  rw [act_single, lmul_one, one_mul, pow_one, Xop_single]

theorem act_single_single_one (n : ℕ) :
    act δ (Finsupp.single n (1 : k)) (Finsupp.single 1 1) = Finsupp.single (n + 1) 1 := by
  rw [act_single, end_mul_apply, Xop_pow_single_one, lmul_single, mul_one, add_comm]

end OrePoly

/-! ## The ring `k[t; σ, δ]` -/

/-- The **Ore extension** `k[t; σ, δ]`: the free left `k`-module `ℕ →₀ k` on the powers of `t`,
with multiplication determined by `t * a = σ a * t + δ a`. -/
def OrePoly {k : Type u} [Ring k] {σ : k →+* k} (_δ : OreDerivation k σ) : Type u := ℕ →₀ k

namespace OrePoly

variable {k : Type u} [Ring k] {σ : k →+* k} (δ : OreDerivation k σ)

noncomputable instance instAddCommGroup : AddCommGroup (OrePoly δ) :=
  inferInstanceAs (AddCommGroup (ℕ →₀ k))

noncomputable instance instInhabited : Inhabited (OrePoly δ) := ⟨(0 : ℕ →₀ k)⟩

/-- The monomial `a * tⁿ`. -/
noncomputable def monomial (n : ℕ) (a : k) : OrePoly δ := Finsupp.single n a

/-- The `n`-th coefficient of `f`, so that `f = Σₙ (coeff f n) * tⁿ`. -/
def coeff (f : OrePoly δ) (n : ℕ) : k := (show ℕ →₀ k from f) n

@[simp] theorem coeff_monomial (n m : ℕ) (a : k) :
    coeff δ (monomial δ n a) m = if n = m then a else 0 := Finsupp.single_apply

theorem monomial_injective (n : ℕ) : Function.Injective (monomial δ n) :=
  Finsupp.single_injective n

noncomputable instance instRing : Ring (OrePoly δ) :=
  { (inferInstance : AddCommGroup (OrePoly δ)) with
    mul := fun f g => act δ f g
    one := (Finsupp.single 0 1 : ℕ →₀ k)
    mul_assoc := act_mul_assoc δ
    one_mul := act_one_mul δ
    mul_one := act_mul_one δ
    left_distrib := act_left_distrib δ
    right_distrib := act_right_distrib δ
    zero_mul := act_zero_mul δ
    mul_zero := act_mul_zero δ }

theorem mul_def (f g : OrePoly δ) : f * g = act δ f g := rfl

theorem one_def : (1 : OrePoly δ) = monomial δ 0 1 := rfl

instance instNontrivial [Nontrivial k] : Nontrivial (OrePoly δ) :=
  ⟨⟨1, 0, by
    change (Finsupp.single 0 (1 : k)) ≠ 0
    simp⟩⟩

/-- The coefficient ring sits inside `k[t; σ, δ]` as the constants. -/
noncomputable def C : k →+* OrePoly δ where
  toFun a := monomial δ 0 a
  map_one' := rfl
  map_zero' := Finsupp.single_zero 0
  map_add' a b := Finsupp.single_add 0 a b
  map_mul' a b := (act_single_zero_single_zero δ a b).symm

@[simp] theorem C_apply (a : k) : C δ a = monomial δ 0 a := rfl

theorem C_injective : Function.Injective (C δ) := monomial_injective δ 0

/-- The variable `t`. -/
noncomputable def X : OrePoly δ := monomial δ 1 1

/-- **The defining relation of `k[t; σ, δ]`**: `t * a = σ a * t + δ a`. -/
theorem X_mul_C (a : k) : X δ * C δ a = C δ (σ a) * X δ + C δ (δ a) := by
  change act δ (Finsupp.single 1 1) (Finsupp.single 0 a)
      = act δ (Finsupp.single 0 (σ a)) (Finsupp.single 1 1) + Finsupp.single 0 (δ a)
  rw [act_single_one_single_zero, act_single_zero_single]
  rfl

@[simp] theorem X_pow (n : ℕ) : X δ ^ n = monomial δ n 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, ih]
      change act δ (Finsupp.single n (1 : k)) (Finsupp.single 1 1) = Finsupp.single (n + 1) 1
      exact act_single_single_one δ n

/-- Every monomial is `a * tⁿ`: the powers of `t` are a left `k`-basis. -/
theorem monomial_eq (n : ℕ) (a : k) : monomial δ n a = C δ a * X δ ^ n := by
  rw [X_pow]
  change Finsupp.single n a = act δ (Finsupp.single 0 a) (Finsupp.single n 1)
  exact (act_single_zero_single δ a n).symm

end OrePoly

end LeftPCI
