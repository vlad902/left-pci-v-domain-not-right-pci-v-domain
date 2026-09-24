module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Order.Zorn
public import Mathlib.RingTheory.Ideal.Defs

@[expose] public section

/-!
# Cohn's weak algorithm on a filtered ring

This file develops, for a general ring, the machinery of P. M. Cohn's *weak algorithm*:
filtrations, `v`-dependence, the `n`-term weak algorithm and the dependence number, and the
theorem that a filtered ring with the weak algorithm is a **fir** — every one-sided ideal is
free.

References:

* P. M. Cohn, *Free Ideal Rings and Localization in General Rings*, Cambridge University Press
  2006, §2.4 (`V.1`–`V.4`, formulas (1) and (2), Theorem 2.4.6).
* P. M. Cohn, *Some remarks on the invariant basis property*, Topology **5** (1966) 215–228
  §4 (dependence number, Theorem 4.3).

## Side convention

Cohn writes everything on the **right**: `a` is right `v`-dependent on `(aᵢ)` when
`v (a - ∑ aᵢ * bᵢ) < v a`, and the weak algorithm makes *right* ideals free.  Mathlib's
`Ideal R` is a **left** ideal and `Module.Free R I` is freeness as a *left* module, and this
repository formalizes one-sided properties left-handedly, so everything below is the mirror
image: `LeftDepOn` is Cohn's right-dependence read in `Rᵐᵒᵖ`, and `Filtration.free_of_ideal`
makes *left* ideals free.  Every statement of Cohn's quoted in a docstring has been mirrored
accordingly; no mathematical content changes, since `v` is a filtration of `R` iff it is one of
`Rᵐᵒᵖ`.

## `Filtration` is a structure, not a class

Cohn's dependence number `λ(R)` is a supremum **over all filtrations of `R`** (Cohn 1966
§4), so a ring must be able to carry many filtrations at once; a `class` would force a canonical
one.  Hence `Filtration R` is a bundled structure and every definition below takes it as an
explicit argument.

## Main definitions

* `LeftPCI.Filtration R` — Cohn's `V.1`–`V.4`.
* `Filtration.LeftDepOn v a u` — Cohn (1), mirrored.
* `Filtration.LeftDep v u` — Cohn (2), mirrored: the family `u` is left `v`-dependent.
* `Filtration.StronglyLeftDep v u` — Cohn's *strong* dependence: however the family is listed
  in weakly increasing degree, some member is left `v`-dependent on its predecessors.  The
  listing is encoded as an injective `w : ι → ℕ` compatible with degrees, which is exactly the
  data of a linear ordering of the family refining the degree preorder.
* `Filtration.HasNTermWeakAlgorithm v n`, `Filtration.HasWeakAlgorithm v` — the `n`-term weak
  algorithm and the weak algorithm.
* `Filtration.depNum v`, `LeftPCI.ringDepNum R` — Cohn's `λ_v(R)` and `λ(R)`.

## Main results

* `Filtration.deg_mul_of_oneTerm`, `Filtration.isDomain_of_oneTerm` — the 1-term weak algorithm
  says `v` is a degree function, so the ring is a domain (Cohn 1966 Prop. 4.1 and its
  corollary).
* `Filtration.isUnit_of_deg_eq_zero` — with the 2-term weak algorithm every element of degree
  `0` is a unit, i.e. `R⁽⁰⁾` is a division ring (Cohn *FIR* p. 126).
* `Filtration.free_of_hasWeakAlgorithm` — **Theorem A**: a filtered ring with the weak algorithm
  is a left fir (Cohn *FIR* Theorem 2.4.6).

The proof of Theorem A given here is not Cohn's.  Cohn constructs a weak `v`-basis of a right
ideal `𝔞` degree by degree, as a set of representatives for bases of the `K`-spaces
`𝔞⁽ʰ⁾/𝔞̃⁽ʰ⁾`, which needs `R⁽⁰⁾ = K` to be a field.  Instead we take, by Zorn's lemma, a maximal
element of the family of left `v`-independent subsets `B ⊆ I` that are *saturated*, meaning that
every element of `I` of degree below some degree occurring in `B` is already left `v`-dependent
on `B`.  Saturation is exactly what makes the maximal `B` absorb a hypothetical
lowest-degree element of `I` not dependent on `B`, and it removes the need for `R⁽⁰⁾` to be a
field.
-/

namespace LeftPCI

universe u

variable {R : Type u} [Ring R]

/-- A **filtration** on a ring, in Cohn's sense (Cohn *FIR* §2.4, `V.1`–`V.4`):
`deg x = ⊥` exactly for `x = 0` (this is `V.1`, `v x ≥ 0` for `x ≠ 0` and `v 0 = -∞`),
`deg 1 = 0`, `deg (x - y) ≤ max (deg x) (deg y)` and `deg (x * y) ≤ deg x + deg y`. -/
structure Filtration (R : Type u) [Ring R] where
  /-- The value (degree) function of the filtration. -/
  deg : R → WithBot ℕ
  /-- `V.1`: only `0` has degree `-∞`. -/
  deg_eq_bot : ∀ x : R, deg x = ⊥ ↔ x = 0
  /-- `V.4`. -/
  deg_one : deg 1 = 0
  /-- `V.2`. -/
  deg_sub_le : ∀ x y : R, deg (x - y) ≤ max (deg x) (deg y)
  /-- `V.3`. -/
  deg_mul_le : ∀ x y : R, deg (x * y) ≤ deg x + deg y

/-- A finite subset of the union of a nonempty chain of sets already lies in one member of the
chain. -/
theorem exists_mem_of_coe_subset_sUnion {α : Type*} {c : Set (Set α)}
    (hchain : IsChain (· ⊆ ·) c) (hne : c.Nonempty) (t : Finset α) (ht : ↑t ⊆ ⋃₀ c) :
    ∃ B ∈ c, ↑t ⊆ B := by
  classical
  induction t using Finset.induction with
  | empty => obtain ⟨B, hB⟩ := hne; exact ⟨B, hB, by simp⟩
  | insert a t ha ih =>
      obtain ⟨B, hB, htB⟩ := ih fun y hy => ht (by simp [Finset.mem_coe.1 hy])
      obtain ⟨B', hB', haB'⟩ := ht (show a ∈ (↑(insert a t) : Set α) by simp)
      rcases hchain.total hB hB' with hle | hle
      · exact ⟨B', hB', fun y hy => by
          rcases Finset.mem_insert.1 (Finset.mem_coe.1 hy) with rfl | hy'
          exacts [haB', hle (htB (Finset.mem_coe.2 hy'))]⟩
      · exact ⟨B, hB, fun y hy => by
          rcases Finset.mem_insert.1 (Finset.mem_coe.1 hy) with rfl | hy'
          exacts [hle haB', htB (Finset.mem_coe.2 hy')]⟩

namespace Filtration

variable (v : Filtration R)

@[simp] theorem deg_zero : v.deg 0 = ⊥ := (v.deg_eq_bot 0).2 rfl

theorem deg_ne_bot {x : R} (hx : x ≠ 0) : v.deg x ≠ ⊥ := fun h => hx ((v.deg_eq_bot x).1 h)

theorem bot_lt_deg {x : R} (hx : x ≠ 0) : ⊥ < v.deg x :=
  lt_of_le_of_ne bot_le (Ne.symm (v.deg_ne_bot hx))

theorem eq_zero_of_deg_eq_bot {x : R} (hx : v.deg x = ⊥) : x = 0 := (v.deg_eq_bot x).1 hx

@[simp] theorem deg_neg (x : R) : v.deg (-x) = v.deg x := by
  refine le_antisymm ?_ ?_
  · simpa using v.deg_sub_le 0 x
  · simpa using v.deg_sub_le 0 (-x)

theorem deg_add_le (x y : R) : v.deg (x + y) ≤ max (v.deg x) (v.deg y) := by
  simpa using v.deg_sub_le x (-y)

theorem deg_sum_le {ι : Type*} (s : Finset ι) (f : ι → R) :
    v.deg (∑ i ∈ s, f i) ≤ s.sup fun i => v.deg (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sup_insert]
      exact le_trans (v.deg_add_le _ _) (max_le_max le_rfl ih)

/-- The **opposite filtration** on `Rᵐᵒᵖ`.  Cohn's axioms `V.1`–`V.4` are left–right symmetric,
so a filtration of `R` is one of `Rᵐᵒᵖ`; left `v`-dependence for `Filtration.op v` is Cohn's
own (right-handed) dependence in `R`.  This is what makes the *right*-handed half of a chiral
conclusion — e.g. a ring that is a right but not a left fir — reachable from the development
below without mirroring any proof. -/
def op (v : Filtration R) : Filtration Rᵐᵒᵖ where
  deg x := v.deg x.unop
  deg_eq_bot x := by
    rw [v.deg_eq_bot]
    exact ⟨fun h => MulOpposite.unop_injective h, fun h => by rw [h]; rfl⟩
  deg_one := v.deg_one
  deg_sub_le x y := v.deg_sub_le _ _
  deg_mul_le x y := by
    simpa [MulOpposite.unop_mul, add_comm] using v.deg_mul_le y.unop x.unop

@[simp] theorem op_deg (v : Filtration R) (x : Rᵐᵒᵖ) : v.op.deg x = v.deg x.unop := rfl

/-! ## Dependence -/

/-- Formula (1) of Cohn *FIR* §2.4, mirrored to the left: `a` is **left `v`-dependent** on the
family `u` if `a = 0`, or there are coefficients `c` with `deg (a - ∑ cᵢ uᵢ) < deg a` and
`deg cᵢ + deg uᵢ ≤ deg a` for every `i`. -/
def LeftDepOn {ι : Type u} [Fintype ι] (a : R) (u : ι → R) : Prop :=
  a = 0 ∨ ∃ c : ι → R, v.deg (a - ∑ i, c i * u i) < v.deg a ∧
    ∀ i, v.deg (c i) + v.deg (u i) ≤ v.deg a

/-- `a` is left `v`-dependent on the **set** `S`. -/
def LeftDepOnSet (a : R) (S : Set R) : Prop :=
  a = 0 ∨ ∃ (t : Finset R) (c : R → R), ↑t ⊆ S ∧
    v.deg (a - ∑ s ∈ t, c s * s) < v.deg a ∧ ∀ s ∈ t, v.deg (c s) + v.deg s ≤ v.deg a

/-- Formula (2) of Cohn *FIR* §2.4, mirrored: the family `u` is **left `v`-dependent**. -/
def LeftDep {ι : Type u} [Fintype ι] (u : ι → R) : Prop :=
  (∃ i, u i = 0) ∨ ∃ c : ι → R,
    v.deg (∑ i, c i * u i) < Finset.univ.sup fun i => v.deg (c i) + v.deg (u i)

/-- A finite set of (distinct) elements is left `v`-dependent. -/
def FinsetDep (t : Finset R) : Prop := v.LeftDep fun s : ↥t => (s : R)

/-- A set is **left `v`-independent** when no finite subset of it is left `v`-dependent.
(Cohn takes families; for a family with a repeated non-zero entry dependence is automatic, so
nothing is lost by using sets of distinct elements.) -/
def SetIndep (S : Set R) : Prop := ∀ t : Finset R, ↑t ⊆ S → ¬ v.FinsetDep t

/-- Cohn's **strong left `v`-dependence** (Cohn *FIR* §2.4): however the family is listed in
weakly increasing degree, some member is left `v`-dependent on its predecessors.  A listing is
encoded by an injective `w : ι → ℕ` with `deg (u i) < deg (u j) → w i < w j`; such `w` are
exactly the linear orderings of the index set refining the degree preorder. -/
def StronglyLeftDep {ι : Type u} [Fintype ι] (u : ι → R) : Prop :=
  ∀ w : ι → ℕ, Function.Injective w → (∀ i j, v.deg (u i) < v.deg (u j) → w i < w j) →
    ∃ i, v.LeftDepOn (u i) fun j => if w j < w i then u j else 0

/-- Cohn's **`n`-term weak algorithm** (Cohn *FIR* §2.4): every left `v`-dependent family of
at most `n` elements is strongly left `v`-dependent. -/
def HasNTermWeakAlgorithm (n : ℕ) : Prop :=
  ∀ (ι : Type u) [Fintype ι] (u : ι → R), Fintype.card ι ≤ n → v.LeftDep u → v.StronglyLeftDep u

/-- Cohn's **weak algorithm** (Cohn *FIR* §2.4): every left `v`-dependent family is strongly
left `v`-dependent. -/
def HasWeakAlgorithm : Prop :=
  ∀ (ι : Type u) [Fintype ι] (u : ι → R), v.LeftDep u → v.StronglyLeftDep u

theorem hasNTermWeakAlgorithm_of_hasWeakAlgorithm (h : v.HasWeakAlgorithm) (n : ℕ) :
    v.HasNTermWeakAlgorithm n := fun ι _ u _ => h ι u

theorem hasNTermWeakAlgorithm_mono {m n : ℕ} (hmn : m ≤ n) (h : v.HasNTermWeakAlgorithm n) :
    v.HasNTermWeakAlgorithm m := fun ι _ u hc => h ι u (hc.trans hmn)

/-- Cohn's **dependence number** `λ_v(R)` relative to the filtration `v`: the greatest `n` for
which the `n`-term weak algorithm holds, or `⊤` if it holds for all `n`.

**Convention warning — Cohn's two sources differ by one, and this is the *book's* convention.**

* *Free Ideal Rings and Localization in General Rings*, CUP 2006 p. 128
  defines `λ_v(R)` as "*the greatest integer `n` for which the `n`-term weak algorithm holds, or
  `∞` if it holds for all `n`*", and adds that "*`λ_v(R) ≥ 1` means that the 1-term weak algorithm
  holds, i.e. `v` is a degree-function.  In particular, such a ring will be an integral domain*".
  **This is the definition used here.**
* *Some remarks on the invariant basis property*, Topology **5** (1966) 215–228
  p. 219 defines it instead as "*the **least** integer `n` for which there
  exists a right `R`-dependent set of `n` elements which is not strongly right `R`-dependent*",
  whence his Prop. 4.1 "`v` is a valuation iff `λ_v(R) > 1`" and its Corollary "*any ring whose
  dependence number is greater than 1 is an integral domain*".

So `depNum = (1966 paper's λ_v) − 1`.  Concretely, when applying the 1966 paper's Thm. 5.2
(`λ(V_{m,n}) = m`), translate it to `depNum = m − 1`: for `V_{2,3}` the 1966 value is `2` and the
value here is `1`, i.e. exactly `HasNTermWeakAlgorithm v 1`. -/
noncomputable def depNum : ℕ∞ :=
  sSup {n : ℕ∞ | ∀ (ι : Type u) [Fintype ι] (u : ι → R), (Fintype.card ι : ℕ∞) ≤ n →
    v.LeftDep u → v.StronglyLeftDep u}

theorem le_depNum_iff {n : ℕ} : (n : ℕ∞) ≤ v.depNum ↔ v.HasNTermWeakAlgorithm n := by
  classical
  constructor
  · intro h
    by_contra hcon
    have hlt : ∀ m ∈ {n : ℕ∞ | ∀ (ι : Type u) [Fintype ι] (u : ι → R),
        (Fintype.card ι : ℕ∞) ≤ m → v.LeftDep u → v.StronglyLeftDep u}, m < (n : ℕ∞) := by
      intro m hm
      by_contra hle
      exact hcon fun ι _ u hc hd => hm ι u (le_trans (by exact_mod_cast hc) (not_lt.1 hle)) hd
    have : v.depNum ≤ (n : ℕ∞) - 1 := by
      refine sSup_le fun m hm => ?_
      have := hlt m hm
      exact ENat.le_sub_one_of_lt this
    have hn : n ≠ 0 := by
      rintro rfl
      exact hcon fun ι _ u hc hd => absurd (Nat.le_zero.1 hc) (by
        intro h0
        rcases hd with ⟨i, _⟩ | ⟨c, hc'⟩
        · exact absurd (Fintype.card_eq_zero_iff.1 h0) (fun he => he.elim i)
        · rw [Finset.univ_eq_empty_iff.2 (Fintype.card_eq_zero_iff.1 h0)] at hc'
          simp at hc')
    have h1 : (n : ℕ∞) ≤ (n : ℕ∞) - 1 := le_trans h this
    have hlt' : (n : ℕ∞) - 1 < (n : ℕ∞) := by
      have hc : ((n - 1 : ℕ) : ℕ∞) = (n : ℕ∞) - 1 := by
        push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hn)]; rfl
      rw [← hc]
      exact_mod_cast Nat.sub_lt (Nat.pos_of_ne_zero hn) one_pos
    exact absurd h1 (not_le.2 hlt')
  · intro h
    refine le_sSup ?_
    intro ι _ u hc hd
    exact h ι u (by exact_mod_cast hc) hd

theorem depNum_eq_top_iff : v.depNum = ⊤ ↔ v.HasWeakAlgorithm := by
  classical
  constructor
  · intro h ι _ u hd
    have : ((Fintype.card ι : ℕ) : ℕ∞) ≤ v.depNum := by rw [h]; exact le_top
    exact (v.le_depNum_iff.1 this) ι u le_rfl hd
  · intro h
    refine top_le_iff.1 (le_sSup ?_)
    intro ι _ u _ hd
    exact h ι u hd

/-! ## Elementary consequences of the weak algorithm -/

theorem eq_zero_of_deg_lt_zero {z : R} (h : v.deg z < 0) : z = 0 := by
  refine v.eq_zero_of_deg_eq_bot ?_
  rcases eq_or_ne (v.deg z) ⊥ with h' | h'
  · exact h'
  · obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 h'
    rw [← hm] at h
    simp at h

/-- Proposition 4.1 of Cohn 1966: the **1-term weak algorithm** says exactly that `v` is a
degree function. -/
theorem deg_mul_of_oneTerm (h : v.HasNTermWeakAlgorithm 1) (b a : R) :
    v.deg (b * a) = v.deg b + v.deg a := by
  refine le_antisymm (v.deg_mul_le b a) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hstrong : v.StronglyLeftDep (fun _ : PUnit.{u + 1} => a) :=
    h PUnit.{u + 1} _ (by simp) (Or.inr ⟨fun _ => b, by simpa using hcon⟩)
  obtain ⟨i, hi⟩ := hstrong (fun _ => 0) (fun p q _ => Subsingleton.elim p q) (by simp)
  rcases hi with hi | ⟨c, hlt, -⟩
  · rw [show a = 0 from hi] at hcon
    simp at hcon
  · simp at hlt

/-- Corollary to Proposition 4.1 of Cohn 1966: a nontrivial ring carrying a filtration with
the 1-term weak algorithm is an integral domain. -/
theorem isDomain_of_oneTerm [Nontrivial R] (h : v.HasNTermWeakAlgorithm 1) : IsDomain R := by
  have hnzd : NoZeroDivisors R := by
    refine ⟨fun {b a} hba => ?_⟩
    by_contra hcon
    have hd := v.deg_mul_of_oneTerm h b a
    rw [hba, v.deg_zero] at hd
    rcases WithBot.add_eq_bot.1 hd.symm with h' | h'
    exacts [hcon (Or.inl (v.eq_zero_of_deg_eq_bot h')),
      hcon (Or.inr (v.eq_zero_of_deg_eq_bot h'))]
  exact NoZeroDivisors.to_isDomain R

/-- Cohn, *FIR* p. 126: when the **2-term weak algorithm** holds, every element of
degree `0` is a unit; that is, `R⁽⁰⁾` is a division ring. -/
theorem isUnit_of_deg_eq_zero [Nontrivial R] (h : v.HasNTermWeakAlgorithm 2) {a : R}
    (ha : v.deg a = 0) : IsUnit a := by
  have hdom : IsDomain R := v.isDomain_of_oneTerm (v.hasNTermWeakAlgorithm_mono one_le_two h)
  have ha0 : a ≠ 0 := fun h0 => by simp [h0] at ha
  have hsum2 : ∀ f : ULift.{u} (Fin 2) → R, ∑ i, f i = f (ULift.up 0) + f (ULift.up 1) := by
    intro f
    rw [Fintype.sum_equiv (Equiv.ulift (α := Fin 2)) f (fun j => f (ULift.up j))
      (fun i => by cases i; rfl), Fin.sum_univ_two]
  set u : ULift.{u} (Fin 2) → R := fun i => if i.down = 0 then a else 1 with hu
  have hu0 : u (ULift.up (0 : Fin 2)) = a := by simp [hu]
  have hu1 : u (ULift.up (1 : Fin 2)) = 1 := by simp [hu]
  have hdegu : ∀ i, v.deg (u i) = 0 := by
    rintro ⟨i⟩
    fin_cases i
    · simpa [hu] using ha
    · simpa [hu] using v.deg_one
  have hdep : v.LeftDep u := by
    refine Or.inr ⟨fun i => if i.down = 0 then 1 else -a, ?_⟩
    have hz : (∑ i : ULift.{u} (Fin 2), (if i.down = 0 then (1 : R) else -a) * u i) = 0 := by
      rw [hsum2]; simp [hu]
    rw [hz, v.deg_zero]
    refine lt_of_lt_of_le ?_ (Finset.le_sup (Finset.mem_univ (ULift.up (0 : Fin 2))))
    simp [hu, ha, v.deg_one]
  obtain ⟨i, hi⟩ := h _ u (by simp) hdep (fun i => i.down.val)
    (fun p q hpq => by cases p; cases q; simpa using Fin.val_injective hpq)
    (fun p q hpq => by simp [hdegu] at hpq)
  have hcases : i = ULift.up (0 : Fin 2) ∨ i = ULift.up (1 : Fin 2) := by
    rcases i with ⟨i⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hinv : ∃ c : R, c * a = 1 := by
    rcases hcases with rfl | rfl
    · exfalso
      rcases hi with hi | ⟨c, hlt, -⟩
      · exact ha0 (by rw [← hu0]; exact hi)
      · simp at hlt
    · rcases hi with hi | ⟨c, hlt, -⟩
      · exact absurd (by rw [← hu1]; exact hi) one_ne_zero
      · refine ⟨c (ULift.up 0), ?_⟩
        have hfam : (fun j : ULift.{u} (Fin 2) =>
            if j.down.val < (ULift.up (1 : Fin 2) : ULift.{u} (Fin 2)).down.val then u j else 0)
            = fun j => if j.down = 0 then a else 0 := by
          funext j; rcases j with ⟨j⟩; fin_cases j <;> simp [hu]
        rw [hfam, hsum2] at hlt
        have hzz : (c (ULift.up 0)
              * (if (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)).down = 0 then a else 0)
            + c (ULift.up 1)
              * (if (ULift.up (1 : Fin 2) : ULift.{u} (Fin 2)).down = 0 then a else 0))
            = c (ULift.up 0) * a := by simp
        rw [hzz, hu1, v.deg_one] at hlt
        exact (sub_eq_zero.1 (v.eq_zero_of_deg_lt_zero hlt)).symm
  obtain ⟨c, hc⟩ := hinv
  have ha' : a * c = 1 := mul_right_cancel₀ ha0 (by rw [mul_assoc, hc, mul_one, one_mul])
  exact ⟨⟨a, c, ha', hc⟩, rfl⟩

/-! ## Basic lemmas on dependence -/

theorem leftDepOnSet_self {a : R} {S : Set R} (ha : a ∈ S) (ha0 : a ≠ 0) :
    v.LeftDepOnSet a S := by
  classical
  refine Or.inr ⟨{a}, fun _ => 1, by simpa using ha, ?_, ?_⟩
  · simp only [Finset.sum_singleton, one_mul, sub_self, v.deg_zero]
    exact v.bot_lt_deg ha0
  · intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    simp [v.deg_one]

theorem leftDepOnSet_mono {a : R} {S T : Set R} (hST : S ⊆ T) (h : v.LeftDepOnSet a S) :
    v.LeftDepOnSet a T := by
  rcases h with h | ⟨t, c, hts, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨t, c, hts.trans hST, h1, h2⟩

/-- Dependence on a `0`-padded subfamily of an *injective* family is dependence on the set of
the retained entries.  (Cohn: "dependence on a family is unaffected by adjoining `0` to or
removing `0` from the family".) -/
theorem leftDepOnSet_of_leftDepOn_filter {ι : Type u} [Fintype ι] {a : R} {u : ι → R}
    (hu : Function.Injective u) {p : ι → Prop} [DecidablePred p] {S : Set R}
    (hS : ∀ i, p i → u i ∈ S)
    (h : v.LeftDepOn a fun j => if p j then u j else 0) : v.LeftDepOnSet a S := by
  classical
  rcases h with h | ⟨c, hlt, hdeg⟩
  · exact Or.inl h
  refine Or.inr ⟨{i ∈ (Finset.univ : Finset ι) | p i}.image u, Function.extend u c 0, ?_, ?_, ?_⟩
  · intro s hs
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    exact hS i hi
  · have hsum : ∑ s ∈ {i ∈ (Finset.univ : Finset ι) | p i}.image u, Function.extend u c 0 s * s
        = ∑ i, c i * (if p i then u i else 0) := by
      rw [Finset.sum_image fun x _ y _ hxy => hu hxy, Finset.sum_filter]
      exact Finset.sum_congr rfl fun i _ => by
        by_cases hp : p i <;> simp [hp, hu.extend_apply]
    rw [hsum]
    exact hlt
  · intro s hs
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    rw [hu.extend_apply]
    simpa [hi] using hdeg i

theorem finsetDep_of_coeffs {t : Finset R} (c : R → R)
    (h : v.deg (∑ s ∈ t, c s * s) < t.sup fun s => v.deg (c s) + v.deg s) : v.FinsetDep t := by
  refine Or.inr ⟨fun s : ↥t => c (s : R), ?_⟩
  rw [Finset.sum_coe_sort t fun s => c s * s, Finset.univ_eq_attach,
    Finset.sup_attach t fun s => v.deg (c s) + v.deg s]
  exact h

theorem not_setIndep_of_leftDepOnSet_diff {B : Set R} {b : R} (hb : b ∈ B) (hb0 : b ≠ 0)
    (h : v.LeftDepOnSet b (B \ {b})) : ¬ v.SetIndep B := by
  classical
  intro hindep
  rcases h with h | ⟨t, c, hts, hlt, hdeg⟩
  · exact hb0 h
  have hbt : b ∉ t := fun hbt => (hts hbt).2 rfl
  have hne : ∀ s ∈ t, s ≠ b := fun s hs hsb => hbt (hsb ▸ hs)
  set c' : R → R := Function.update (fun s => -c s) b 1 with hc'
  have hc'b : c' b = 1 := Function.update_self b 1 _
  have hc'ne : ∀ s, s ≠ b → c' s = -c s := fun s hs => Function.update_of_ne hs 1 _
  refine hindep (insert b t) ?_ (v.finsetDep_of_coeffs c' ?_)
  · intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact hb
    · exact (hts hs).1
  · have hsum : (∑ s ∈ insert b t, c' s * s) = b - ∑ s ∈ t, c s * s := by
      rw [Finset.sum_insert hbt, hc'b, one_mul, sub_eq_add_neg]
      congr 1
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun s hs => by rw [hc'ne s (hne s hs), neg_mul]
    have hsup : ((insert b t).sup fun s => v.deg (c' s) + v.deg s) = v.deg b := by
      rw [Finset.sup_insert, hc'b, v.deg_one, zero_add]
      refine max_eq_left (Finset.sup_le fun s hs => ?_)
      rw [hc'ne s (hne s hs), v.deg_neg]
      exact hdeg s hs
    rw [hsum, hsup]
    exact hlt

theorem zero_notMem_of_setIndep {B : Set R} (h : v.SetIndep B) : (0 : R) ∉ B := by
  intro h0
  exact h {0} (by simpa using h0) (Or.inl ⟨⟨0, by simp⟩, rfl⟩)

/-! ## Listings in weakly increasing degree -/

/-- A finite set `t` of elements of maximal degree at `x ∈ t` can be listed in weakly increasing
degree with `x` **last**.  The listing is encoded by the position function `w`. -/
theorem exists_listing_last {t : Finset R} {x : R} (hxt : x ∈ t)
    (hmax : ∀ s ∈ t, v.deg s ≤ v.deg x) :
    ∃ w : ↥t → ℕ, Function.Injective w ∧
      (∀ j j' : ↥t, v.deg (j : R) < v.deg (j' : R) → w j < w j') ∧
      (∀ j : ↥t, (j : R) ≠ x → w j < w ⟨x, hxt⟩) := by
  classical
  set X : ↥t := ⟨x, hxt⟩ with hX
  have hXne : ∀ j : ↥t, (j : R) ≠ x ↔ j ≠ X := fun j =>
    ⟨fun h hj => h (by rw [hj]), fun h hj => h (Subtype.ext hj)⟩
  set K := t.card + 1 with hK
  set dr : ↥t → ℕ := fun j => {s ∈ t | v.deg s < v.deg (j : R)}.card with hdr
  set ix : ↥t → ℕ := Function.update (fun j => (t.equivFin j : ℕ)) X t.card with hix
  have hix_X : ix X = t.card := Function.update_self _ _ _
  have hix_ne : ∀ j : ↥t, j ≠ X → ix j = (t.equivFin j : ℕ) := fun j hj =>
    Function.update_of_ne hj _ _
  have hix_lt : ∀ j : ↥t, j ≠ X → ix j < t.card := fun j hj => by
    rw [hix_ne j hj]; exact (t.equivFin j).isLt
  have hix_le : ∀ j, ix j ≤ t.card := by
    intro j
    by_cases h : j = X
    · rw [h, hix_X]
    · exact le_of_lt (hix_lt j h)
  have hix_inj : Function.Injective ix := by
    intro j j' hjj'
    by_cases h : j = X
    · by_cases h' : j' = X
      · rw [h, h']
      · exact absurd (by rw [← hix_X, ← h]; exact hjj' : t.card = ix j')
          (Nat.ne_of_gt (hix_lt j' h'))
    · by_cases h' : j' = X
      · exact absurd (by rw [← hix_X, ← h']; exact hjj'.symm : t.card = ix j)
          (Nat.ne_of_gt (hix_lt j h))
      · rw [hix_ne j h, hix_ne j' h'] at hjj'
        exact t.equivFin.injective (Fin.val_injective hjj')
  have hdr_mono : ∀ j j' : ↥t, v.deg (j : R) < v.deg (j' : R) → dr j < dr j' := by
    intro j j' hlt
    refine Finset.card_lt_card ⟨fun s hs => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter] at hs ⊢
      exact ⟨hs.1, hs.2.trans hlt⟩
    · have hmem : (j : R) ∈ {s ∈ t | v.deg s < v.deg (j : R)} :=
        hsub (by simp only [Finset.mem_filter]; exact ⟨j.2, hlt⟩)
      simp only [Finset.mem_filter] at hmem
      exact absurd hmem.2 (lt_irrefl _)
  have hdr_eq : ∀ j j' : ↥t, v.deg (j : R) = v.deg (j' : R) → dr j = dr j' := by
    intro j j' h
    simp only [hdr, h]
  set w : ↥t → ℕ := fun j => K * dr j + ix j with hw
  have hwlt : ∀ j j' : ↥t, dr j < dr j' → w j < w j' := by
    intro j j' h
    have h1 : ix j < K := Nat.lt_succ_of_le (hix_le j)
    simp only [hw]
    calc K * dr j + ix j < K * dr j + K := Nat.add_lt_add_left h1 _
      _ = K * (dr j + 1) := (Nat.mul_succ K (dr j)).symm
      _ ≤ K * dr j' := Nat.mul_le_mul (le_refl K) h
      _ ≤ K * dr j' + ix j' := Nat.le_add_right _ _
  refine ⟨w, ?_, fun j j' h => hwlt j j' (hdr_mono j j' h), ?_⟩
  · intro j j' hjj'
    rcases lt_trichotomy (dr j) (dr j') with h | h | h
    · exact absurd hjj' (Nat.ne_of_lt (hwlt j j' h))
    · simp only [hw, h] at hjj'
      exact hix_inj (Nat.add_left_cancel hjj')
    · exact absurd hjj'.symm (Nat.ne_of_lt (hwlt j' j h))
  · intro j hj
    rcases lt_or_eq_of_le (hmax (j : R) j.2) with h | h
    · exact hwlt j X (hdr_mono j X h)
    · have hdreq : dr j = dr X := hdr_eq j X h
      have hixlt : ix j < ix X := by
        rw [hix_X]
        exact hix_lt j ((hXne j).1 hj)
      simp only [hw, hdreq]
      exact Nat.add_lt_add_left hixlt _

/-! ## Theorem A: a filtered ring with the weak algorithm is a left fir -/

theorem not_finsetDep_empty : ¬ v.FinsetDep (∅ : Finset R) := by
  rintro (⟨i, -⟩ | ⟨c, hc⟩)
  · exact (Finset.notMem_empty (i : R)) i.2
  · simp at hc

theorem setIndep_empty : v.SetIndep (∅ : Set R) := by
  intro t ht
  rw [Finset.coe_eq_empty.1 (Set.subset_empty_iff.1 ht)]
  exact v.not_finsetDep_empty

/-- The **saturated** left `v`-independent subsets of a left ideal `I`: left `v`-independent
`B ⊆ I` such that every element of `I` of degree below some degree occurring in `B` is already
left `v`-dependent on `B`. -/
def SatIndep (I : Ideal R) : Set (Set R) :=
  {B | B ⊆ (I : Set R) ∧ v.SetIndep B ∧
    ∀ b ∈ B, ∀ x ∈ I, v.deg x < v.deg b → v.LeftDepOnSet x B}

theorem exists_maximal_satIndep (I : Ideal R) : ∃ B, Maximal (· ∈ v.SatIndep I) B := by
  classical
  refine zorn_subset _ fun c hcS hchain => ?_
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, ⟨Set.empty_subset _, v.setIndep_empty, by simp⟩, by simp⟩
  · refine ⟨⋃₀ c, ⟨?_, ?_, ?_⟩, fun B hB => Set.subset_sUnion_of_mem hB⟩
    · rintro y ⟨B, hB, hyB⟩
      exact (hcS hB).1 hyB
    · intro t ht hdep
      obtain ⟨B, hB, htB⟩ := exists_mem_of_coe_subset_sUnion hchain hne t ht
      exact (hcS hB).2.1 t htB hdep
    · rintro b ⟨B, hB, hbB⟩ y hyI hlt
      exact v.leftDepOnSet_mono (Set.subset_sUnion_of_mem hB) ((hcS hB).2.2 b hbB y hyI hlt)

/-- **The key step.**  Under the weak algorithm, a maximal saturated left `v`-independent subset
`B` of a left ideal `I` is a *weak `v`-basis*: every element of `I` is left `v`-dependent on
`B`. -/
theorem leftDepOnSet_of_maximal_satIndep (hWA : v.HasWeakAlgorithm) {I : Ideal R} {B : Set R}
    (hB : Maximal (· ∈ v.SatIndep I) B) : ∀ x ∈ I, v.LeftDepOnSet x B := by
  classical
  obtain ⟨⟨hBI, hBindep, hBsat⟩, hBmax⟩ := hB
  by_contra hcon
  obtain ⟨x₀, hx₀I, hx₀dep⟩ : ∃ y ∈ I, ¬ v.LeftDepOnSet y B := by
    by_contra hno
    exact hcon fun y hy => by
      by_contra hd
      exact hno ⟨y, hy, hd⟩
  have hbad : ∃ n : ℕ, ∃ y ∈ I, ¬ v.LeftDepOnSet y B ∧ v.deg y = (n : WithBot ℕ) := by
    have hx₀0 : x₀ ≠ 0 := fun h => hx₀dep (Or.inl h)
    obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.1 (v.deg_ne_bot hx₀0)
    exact ⟨n, x₀, hx₀I, hx₀dep, hn.symm⟩
  obtain ⟨x, hxI, hxdep, hxdeg⟩ := Nat.find_spec hbad
  have hmin : ∀ y ∈ I, v.deg y < ((Nat.find hbad : ℕ) : WithBot ℕ) → v.LeftDepOnSet y B := by
    intro y hyI hy
    by_contra hy'
    have hy0 : y ≠ 0 := fun h => hy' (Or.inl h)
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 (v.deg_ne_bot hy0)
    rw [← hm] at hy
    exact Nat.find_min hbad (WithBot.coe_lt_coe.1 hy) ⟨y, hyI, hy', hm.symm⟩
  have hx0 : x ≠ 0 := fun h => hxdep (Or.inl h)
  have hBdeg : ∀ b ∈ B, v.deg b ≤ v.deg x := fun b hb =>
    le_of_not_gt fun hlt => hxdep (hBsat b hb x hxI hlt)
  have hxB : x ∉ B := fun h => hxdep (v.leftDepOnSet_self h hx0)
  have h0B : (0 : R) ∉ B := v.zero_notMem_of_setIndep hBindep
  have hins : insert x B ∈ v.SatIndep I := by
    refine ⟨Set.insert_subset hxI hBI, ?_, ?_⟩
    · intro t htsub htdep
      by_cases hxt : x ∈ t
      · have htdegs : ∀ s ∈ t, v.deg s ≤ v.deg x := by
          intro s hs
          rcases htsub (Finset.mem_coe.2 hs) with heq | hsB
          · exact le_of_eq (by rw [heq])
          · exact hBdeg s hsB
        have hnotx : ∀ j : ↥t, (j : R) ≠ x → (j : R) ∈ B := by
          intro j hj
          exact (htsub (Finset.mem_coe.2 j.2)).resolve_left hj
        obtain ⟨w, hwinj, hwref, hwmax⟩ := v.exists_listing_last hxt htdegs
        obtain ⟨i, hi⟩ := hWA ↥t (fun s : ↥t => (s : R)) htdep w hwinj
          (fun j j' h => hwref j j' h)
        by_cases hix : (i : R) = x
        · refine hxdep ?_
          have hpred : ∀ j : ↥t, w j < w i → (j : R) ∈ B := by
            intro j hj
            refine hnotx j fun hjx => ?_
            have hji : j = i := Subtype.ext (hjx.trans hix.symm)
            rw [hji] at hj
            exact absurd hj (lt_irrefl _)
          have hres : v.LeftDepOnSet (i : R) B :=
            v.leftDepOnSet_of_leftDepOn_filter Subtype.coe_injective hpred hi
          rwa [hix] at hres
        · have hib : (i : R) ∈ B := hnotx i hix
          have hi0 : (i : R) ≠ 0 := fun h => h0B (h ▸ hib)
          have hiX : w i < w ⟨x, hxt⟩ := hwmax i hix
          have hpred : ∀ j : ↥t, w j < w i → (j : R) ∈ B \ {(i : R)} := by
            intro j hj
            have hjX : j ≠ ⟨x, hxt⟩ := by
              intro hjeq
              rw [hjeq] at hj
              exact absurd (lt_trans hj hiX) (lt_irrefl _)
            refine ⟨hnotx j fun hjx => hjX (Subtype.ext hjx), fun hji => ?_⟩
            have hji' : j = i := Subtype.ext hji
            rw [hji'] at hj
            exact absurd hj (lt_irrefl _)
          have hres : v.LeftDepOnSet (i : R) (B \ {(i : R)}) :=
            v.leftDepOnSet_of_leftDepOn_filter Subtype.coe_injective hpred hi
          exact v.not_setIndep_of_leftDepOnSet_diff hib hi0 hres hBindep
      · refine hBindep t (fun s hs => ?_) htdep
        rcases htsub hs with heq | hsB
        · exact absurd (heq ▸ Finset.mem_coe.1 hs) hxt
        · exact hsB
    · rintro b (rfl | hb) y hyI hylt
      · exact v.leftDepOnSet_mono (Set.subset_insert _ _) (hmin y hyI (hxdeg ▸ hylt))
      · exact v.leftDepOnSet_mono (Set.subset_insert _ _)
          (hmin y hyI (hxdeg ▸ lt_of_lt_of_le hylt (hBdeg b hb)))
  exact hxB (hBmax hins (Set.subset_insert x B) (Set.mem_insert x B))

/-- **Theorem A** (Cohn, *Free Ideal Rings and Localization in General Rings*, Theorem 2.4.6,
mirrored to the left): a filtered ring satisfying the weak algorithm is a **left fir** — every
left ideal is a free module, with any weak `v`-basis as a free generating set. -/
theorem free_of_hasWeakAlgorithm (hWA : v.HasWeakAlgorithm) (I : Ideal R) : Module.Free R I := by
  classical
  obtain ⟨B, hBmax⟩ := v.exists_maximal_satIndep I
  obtain ⟨hBI, hBindep, -⟩ := hBmax.1
  have hdep := v.leftDepOnSet_of_maximal_satIndep hWA hBmax
  have h0B : (0 : R) ∉ B := v.zero_notMem_of_setIndep hBindep
  -- `B` spans `I`: subtract off a dependence relation and induct on the degree.
  have hspan : ∀ n : ℕ, ∀ y ∈ I, v.deg y ≤ (n : WithBot ℕ) → y ∈ Submodule.span R B := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y hyI hdegy
      rcases eq_or_ne y 0 with rfl | hy0
      · exact Submodule.zero_mem _
      obtain h | ⟨t, c, htB, hlt, -⟩ := hdep y hyI
      · exact absurd h hy0
      have hmem : ∑ s ∈ t, c s * s ∈ Submodule.span R B :=
        Submodule.sum_mem _ fun s hs => by
          rw [← smul_eq_mul]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (htB hs))
      have hzI : y - ∑ s ∈ t, c s * s ∈ I :=
        I.sub_mem hyI (Submodule.sum_mem _ fun s hs => I.mul_mem_left _ (hBI (htB hs)))
      have hz : y - ∑ s ∈ t, c s * s ∈ Submodule.span R B := by
        rcases eq_or_ne (y - ∑ s ∈ t, c s * s) 0 with h0 | h0
        · rw [h0]
          exact Submodule.zero_mem _
        obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 (v.deg_ne_bot h0)
        rw [← hm] at hlt
        exact ih m (WithBot.coe_lt_coe.1 (lt_of_lt_of_le hlt hdegy)) _ hzI (le_of_eq hm.symm)
      simpa using Submodule.add_mem _ hz hmem
  have hspanI : Submodule.span R B = I := by
    refine le_antisymm (Submodule.span_le.2 hBI) fun y hy => ?_
    rcases eq_or_ne y 0 with rfl | hy0
    · exact Submodule.zero_mem _
    obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.1 (v.deg_ne_bot hy0)
    exact hspan n y hy (le_of_eq hn.symm)
  -- `B`, viewed inside `I`, is a basis.
  set e : ↥B → I := fun b => ⟨(b : R), hBI b.2⟩ with he
  have hcoe : Function.Injective (fun b : ↥B => (b : R)) := Subtype.coe_injective
  have hli : LinearIndependent R e := by
    rw [linearIndependent_iff']
    intro sfin g hg i hi
    by_contra hgi
    set c : R → R := Function.extend (fun b : ↥B => (b : R)) g 0 with hc
    have hsum : ∑ s ∈ sfin.image (fun b : ↥B => (b : R)), c s * s = 0 := by
      rw [Finset.sum_image fun p _ q _ hpq => hcoe hpq]
      have hterm : ∀ j ∈ sfin, c (j : R) * (j : R) = ((g j • e j : I) : R) := by
        intro j _
        simp [hc, he]
      rw [Finset.sum_congr rfl hterm, ← Submodule.coe_sum, hg]
      rfl
    refine hBindep (sfin.image fun b : ↥B => (b : R)) ?_ (v.finsetDep_of_coeffs c ?_)
    · intro s hs
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hs
      obtain ⟨j, -, rfl⟩ := hs
      exact j.2
    · rw [hsum, v.deg_zero]
      refine lt_of_lt_of_le ?_ (Finset.le_sup (b := (i : R)) (Finset.mem_image_of_mem _ hi))
      have h1 : v.deg (c (i : R)) ≠ ⊥ := by
        simp only [hc, hcoe.extend_apply]
        exact v.deg_ne_bot hgi
      have h2 : v.deg (i : R) ≠ ⊥ := v.deg_ne_bot fun h => h0B (h ▸ i.2)
      refine bot_lt_iff_ne_bot.2 fun hb => ?_
      rcases WithBot.add_eq_bot.1 hb with h | h
      exacts [h1 h, h2 h]
  have htop : ⊤ ≤ Submodule.span R (Set.range e) := by
    rw [top_le_iff]
    refine Submodule.map_injective_of_injective I.injective_subtype ?_
    rw [Submodule.map_span, Submodule.map_subtype_top]
    have himg : I.subtype '' (Set.range e) = B := by
      ext y
      constructor
      · rintro ⟨-, ⟨b, rfl⟩, rfl⟩
        exact b.2
      · intro hy
        exact ⟨e ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
    rw [himg, hspanI]
  exact Module.Free.of_basis (Module.Basis.mk hli htop)

end Filtration

/-- Cohn's **dependence number** `λ(R)` of a ring (Cohn 1966 §4): the supremum of
`λ_v(R)` over all filtrations `v` of `R`. -/
noncomputable def ringDepNum (R : Type u) [Ring R] : ℕ∞ := ⨆ v : Filtration R, v.depNum

end LeftPCI
