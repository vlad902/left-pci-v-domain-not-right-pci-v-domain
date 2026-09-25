module

public import LeftPCI.Counterexample.FreeFieldExt
public import LeftPCI.Counterexample.Adjoin
public import LeftPCI.Counterexample.OreExtension
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.Nat.Pairing

@[expose] public section

namespace LeftPCI.Counterexample

/-! # The construction in one step (Construction 4.1 of `paper/pci_counterexample.tex`)

`Y = Y₀ ⊔ ℕ` (the paper's `Z` is `ℕ`), `U = 𝓕(Y)`, `s` the shift on `Y₀` and the identity on
`ℕ`. Every task `τ = (f, g, e)` over `U` (coefficient data only, which does not depend on
`(σ, δ)`) gets its own generators `x^τ_{l,j} = inr ⟨code τ, l, j⟩` (the paper's `X_τ ⊆ Z`), and
`d` is prescribed on them by the paper's formula (1), so that `T_f(x_j) = x_{j+1}` (`j + 1 < m`)
and `T_f(x_{m-1}) = e - Σ_{j<m} g_j x_j` (`g` monic). There is no tower: `(σ, δ)` is the pair
determined by `(s, d)` (Proposition 3.5).

To avoid circularity the triples are written as polynomials over the reference pair
`δ₀ = δOf 0`; `OrePoly δ` is `ℕ →₀ U` for every `δ`, and degree, coefficients and companion
matrices do not depend on `δ` (definitionally).
-/

open LeftPCI.OrePoly FreeField FreeFieldExt

namespace Direct

/-- `Y = Y₀ ⊔ ℕ`. -/
abbrev Y : Type := ℕ ⊕ ℕ

/-- The shift on `Y₀`, the identity on `ℕ`. -/
def s : Y → Y := Sum.map Nat.succ id

theorem s_injective : Function.Injective s :=
  Sum.map_injective.2 ⟨Nat.succ_injective, Function.injective_id⟩

theorem inl_zero_not_mem_range_s : (Sum.inl 0 : Y) ∉ Set.range s := by
  rintro ⟨y, hy⟩
  cases y with
  | inl a => simp [s] at hy
  | inr p => simp [s] at hy

abbrev U : Type := FreeFieldOn Y

theorem isUniversal : IsUniversalFieldOfFractions U (toFreeField Y) := isUniversal_toFreeField Y

instance : Countable U := FreeFieldExt.countable isUniversal

noncomputable def σOf (di : Y → U) : U →+* U := (exists_pair isUniversal s_injective di).choose

noncomputable def δOf (di : Y → U) : OreDerivation U (σOf di) :=
  (exists_pair isUniversal s_injective di).choose_spec.choose

theorem σOf_gen (di : Y → U) (y : Y) : σOf di (gen Y y) = gen Y (s y) :=
  (exists_pair isUniversal s_injective di).choose_spec.choose_spec.1 y

theorem δOf_gen (di : Y → U) (y : Y) : δOf di (gen Y y) = di y :=
  (exists_pair isUniversal s_injective di).choose_spec.choose_spec.2 y

/-- The reference pair, used only to name coefficient data. -/
noncomputable abbrev δ₀ : OreDerivation U (σOf 0) := δOf 0

/-- A triple `(f, g, e)`: `f, g` monic of degree `≥ 1`, `e ∈ Uⁿ` with `n = deg f`. -/
structure Task where
  f : OrePoly δ₀
  g : OrePoly δ₀
  e : Fin (natDegree δ₀ f) → U
  f_monic : leadingCoeff δ₀ f = 1
  f_deg : 0 < natDegree δ₀ f
  g_monic : leadingCoeff δ₀ g = 1
  g_deg : 0 < natDegree δ₀ g

instance : Countable Task := by
  have : Countable (OrePoly δ₀) := inferInstanceAs (Countable (ℕ →₀ U))
  refine Function.Injective.countable
    (f := fun τ : Task => (τ.f, τ.g, (⟨_, τ.e⟩ : Σ n, Fin n → U))) ?_
  rintro ⟨f, g, e, _, _, _, _⟩ ⟨f', g', e', _, _, _, _⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, h⟩ := h
  cases h
  rfl

noncomputable def code : Task → ℕ := (Countable.exists_injective_nat Task).choose

theorem code_injective : Function.Injective code :=
  (Countable.exists_injective_nat Task).choose_spec

def enc (c l j : ℕ) : ℕ := Nat.pair c (Nat.pair l j)

/-- The generator vector `x^τ_j`. -/
noncomputable def xg (τ : Task) (j : ℕ) : Fin (natDegree δ₀ τ.f) → U :=
  fun l => gen Y (Sum.inr (enc (code τ) l j))

/-- The prescribed value of `T_f(x^τ_j)`. -/
noncomputable def tgt (τ : Task) (j : ℕ) : Fin (natDegree δ₀ τ.f) → U :=
  if j + 1 < natDegree δ₀ τ.g then xg τ (j + 1)
  else τ.e - ∑ i ∈ Finset.range (natDegree δ₀ τ.g), coeff δ₀ τ.g i • xg τ i

/-- `d(x^τ_j) = T_f(x^τ_j) − x^τ_j C_f`, as a vector. -/
noncomputable def dvec (τ : Task) (j : ℕ) : Fin (natDegree δ₀ τ.f) → U :=
  tgt τ j - Matrix.vecMul (xg τ j) (Adjoin.companion δ₀ τ.f)

open Classical in
/-- The value of `d` on the symbol `⟨c, l, j⟩`: the recipe for the task coded by `c`, if any. -/
noncomputable def dval (c l j : ℕ) : U :=
  if h : ∃ τ, code τ = c then
    if hl : l < natDegree δ₀ h.choose.f then dvec h.choose j ⟨l, hl⟩ else 0
  else 0

/-- The map `d : Y → U`. -/
noncomputable def d : Y → U
  | Sum.inl _ => 0
  | Sum.inr k => dval (Nat.unpair k).1 (Nat.unpair (Nat.unpair k).2).1
      (Nat.unpair (Nat.unpair k).2).2

theorem d_xg (τ : Task) (j : ℕ) (l : Fin (natDegree δ₀ τ.f)) :
    d (Sum.inr (enc (code τ) l j)) = dvec τ j l := by
  have h : ∃ τ', code τ' = code τ := ⟨τ, rfl⟩
  have key : ∀ τ' : Task, τ' = τ →
      (if hl : (l : ℕ) < natDegree δ₀ τ'.f then dvec τ' j ⟨l, hl⟩ else 0) = dvec τ j l := by
    rintro _ rfl; simp [l.2]
  simp only [d, enc, Nat.unpair_pair]
  rw [dval]
  simp only [h, ↓reduceDIte]
  exact key _ (code_injective h.choose_spec)

noncomputable abbrev σt : U →+* U := σOf d
noncomputable abbrev δt : OreDerivation U σt := δOf d

/-- `T_f(x^τ_j) = tgt τ j`: `σ` fixes the `x^τ_j`, and `δ(x^τ_j) = tgt − x^τ_j C_f`. -/
theorem T_xg (τ : Task) (j : ℕ) :
    Adjoin.T δt (Adjoin.companion δ₀ τ.f) (xg τ j) = tgt τ j := by
  have hσ : σt ∘ xg τ j = xg τ j := by
    funext l; exact σOf_gen d _
  have hδ : δt ∘ xg τ j = dvec τ j := by
    funext l
    change δt (gen Y _) = _
    rw [δOf_gen, d_xg]
  unfold Adjoin.T
  rw [hσ, hδ, dvec, add_sub_cancel]

theorem iterate_T (τ : Task) :
    ∀ i < natDegree δ₀ τ.g, (Adjoin.T δt (Adjoin.companion δ₀ τ.f))^[i] (xg τ 0) = xg τ i
  | 0, _ => rfl
  | i + 1, hi => by
    rw [Function.iterate_succ_apply', iterate_T τ i (by omega), T_xg, tgt]
    simp only [hi, ↓reduceIte]

/-- The equation `g(T_f)(x^τ_0) = e` holds in `U`, computed with `(σt, δt)`. -/
theorem solves (τ : Task) :
    Adjoin.evalT δt (Adjoin.companion δ₀ τ.f) (show OrePoly δt from τ.g) (xg τ 0) = τ.e := by
  have hm := τ.g_deg
  set m := natDegree δ₀ τ.g with hmdef
  have hlast : (Adjoin.T δt (Adjoin.companion δ₀ τ.f))^[m] (xg τ 0) =
      τ.e - ∑ i ∈ Finset.range m, coeff δ₀ τ.g i • xg τ i := by
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [hk, Function.iterate_succ_apply', iterate_T τ k (by omega), T_xg, tgt, ← hk]
    rw [← hmdef]
    simp only [lt_irrefl, ↓reduceIte]
  unfold Adjoin.evalT
  change ∑ i ∈ Finset.range (m + 1), coeff δ₀ τ.g i • _ = _
  rw [Finset.sum_range_succ, hlast]
  rw [Finset.sum_congr rfl fun i hi => by
    rw [iterate_T τ i (Finset.mem_range.1 hi)]]
  change _ + leadingCoeff δ₀ τ.g • _ = _
  rw [τ.g_monic, one_smul, add_sub_cancel]

/-! ### The theorem -/

section CMul

variable {σ : U →+* U} {δ : OreDerivation U σ}

theorem support_C_mul {a : U} (ha : a ≠ 0) (f : OrePoly δ) :
    support δ (C δ a * f) = support δ f := by
  ext n
  rw [mem_support_iff, mem_support_iff, coeff_C_mul, mul_ne_zero_iff_left ha]

theorem natDegree_C_mul {a : U} (ha : a ≠ 0) (f : OrePoly δ) :
    natDegree δ (C δ a * f) = natDegree δ f := by
  unfold natDegree
  rw [support_C_mul ha]

theorem leadingCoeff_C_mul {a : U} (ha : a ≠ 0) (f : OrePoly δ) :
    leadingCoeff δ (C δ a * f) = a * leadingCoeff δ f := by
  unfold leadingCoeff
  rw [natDegree_C_mul ha, coeff_C_mul]

end CMul

theorem isCFClosed : IsCFClosed δt := by
  intro f hf g hg m
  by_cases hf0 : natDegree δt f = 0
  · have hfC := eq_C_of_natDegree_eq_zero δt hf0
    set c := coeff δt f 0
    have hc : c ≠ 0 := by
      intro hc
      exact hf (by rw [hfC, hc, map_zero])
    refine ⟨0, Ideal.mem_span_singleton'.mpr ⟨m * C δt c⁻¹, ?_⟩⟩
    rw [hfC, mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, mul_one, mul_zero, sub_zero]
  by_cases hg0 : natDegree δt g = 0
  · have hgC := eq_C_of_natDegree_eq_zero δt hg0
    set c := coeff δt g 0
    have hc : c ≠ 0 := by
      intro hc
      exact hg (by rw [hgC, hc, map_zero])
    refine ⟨C δt c⁻¹ * m, ?_⟩
    rw [hgC, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul, sub_self]
    exact zero_mem _
  have hlc : leadingCoeff δt f ≠ 0 := leadingCoeff_ne_zero δt hf
  have hlc' : (leadingCoeff δt f)⁻¹ ≠ 0 := inv_ne_zero hlc
  set f₁ := C δt (leadingCoeff δt f)⁻¹ * f with hf₁
  have hmon : leadingCoeff δt f₁ = 1 := by rw [leadingCoeff_C_mul hlc', inv_mul_cancel₀ hlc]
  have hdeg : 0 < natDegree δt f₁ := by rw [natDegree_C_mul hlc']; omega
  have hf₁0 : f₁ ≠ 0 := ne_zero_of_leadingCoeff_ne_zero δt (by rw [hmon]; exact one_ne_zero)
  -- make `g` monic: `g = a g₁`, and solve `g₁ y ≡ a⁻¹ m`
  have ha : leadingCoeff δt g ≠ 0 := leadingCoeff_ne_zero δt hg
  have ha' : (leadingCoeff δt g)⁻¹ ≠ 0 := inv_ne_zero ha
  set g₁ := C δt (leadingCoeff δt g)⁻¹ * g with hg₁
  set m' := C δt (leadingCoeff δt g)⁻¹ * m with hm'
  let τ : Task :=
    { f := (show OrePoly δ₀ from f₁)
      g := (show OrePoly δ₀ from g₁)
      e := Adjoin.remVec δt f₁ hf₁0 m'
      f_monic := hmon
      f_deg := hdeg
      g_monic := by
        change leadingCoeff δt g₁ = 1
        rw [leadingCoeff_C_mul ha', inv_mul_cancel₀ ha]
      g_deg := by change 0 < natDegree δt g₁; rw [natDegree_C_mul ha']; omega }
  have hv : Adjoin.evalT δt (Adjoin.companion δt f₁) g₁ (xg τ 0) =
      Adjoin.remVec δt f₁ hf₁0 m' := solves τ
  have hmem₁ := Adjoin.sub_mul_mem_of_evalT_eq δt f₁ hmon hdeg hf₁0 g₁ m' _ hv
  refine ⟨Adjoin.ofVec δt (xg τ 0), ?_⟩
  have hmem : m - g * Adjoin.ofVec δt (xg τ 0) ∈ Ideal.span ({f₁} : Set (OrePoly δt)) := by
    have : m - g * Adjoin.ofVec δt (xg τ 0) =
        C δt (leadingCoeff δt g) * (m' - g₁ * Adjoin.ofVec δt (xg τ 0)) := by
      rw [hm', hg₁, mul_sub, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ ha, map_one, one_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ hmem₁
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  refine Ideal.mem_span_singleton'.mpr ⟨c * C δt (leadingCoeff δt f)⁻¹, ?_⟩
  rw [mul_assoc]
  exact hc

theorem not_surjective : ¬ Function.Surjective σt := fun h =>
  gen_not_mem_range isUniversal s_injective inl_zero_not_mem_range_s (σOf_gen d)
    (h (gen Y (Sum.inl 0)))

end Direct

/-- **Theorem 2.5**, via Construction 4.1 (with `k = ℚ`). -/
theorem exists_isCFClosed_not_surjective :
    ∃ (K : Type) (_ : DivisionRing K) (σ : K →+* K) (δ : OreDerivation K σ),
      Countable K ∧ ¬ Function.Surjective σ ∧ IsCFClosed δ :=
  ⟨Direct.U, inferInstance, Direct.σt, Direct.δt, inferInstance, Direct.not_surjective,
    Direct.isCFClosed⟩

end LeftPCI.Counterexample
