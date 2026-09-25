> **Note.** This whole repository (the paper in `paper/`, the Lean development and this
> metadata) was machine-written by Claude models (Anthropic). No human has checked the
> mathematics, only the `Challenge.lean`.

# PCI rings and V-domains are not left-right symmetric

[![CI](https://github.com/vlad902/left-pci-v-domain-not-right-pci-v-domain/actions/workflows/ci.yml/badge.svg)](https://github.com/vlad902/left-pci-v-domain-not-right-pci-v-domain/actions/workflows/ci.yml)

This repository contains a Lean 4 / Mathlib formalization of a counterexample in
noncommutative ring theory, and the paper it formalizes,
[`paper/pci_counterexample.tex`](paper/pci_counterexample.tex)
([PDF](paper/pci_counterexample.pdf)). It is packaged for the
[Palomar registry](https://palomar-registry.org/). `Challenge.lean` contains the statements a
reader audits. `Solution.lean` imports the library `LeftPCI`, which proves them.

## The result

A ring is a *left PCI ring* ("proper cyclics are injective") if every cyclic left module
that is not isomorphic to the ring itself is injective. It is a *left V-ring* if every
simple left module is injective. Right PCI and right V-rings are defined in the same way
with right modules.

Faith (1973) showed that a right PCI ring is either semisimple Artinian or a simple right
semihereditary right Ore domain. Damiano (1979) showed that it is then right Noetherian.
Faith (1973) and Cozzens and Faith (*Simple Noetherian Rings*, 1975) proved, using a theorem
of Boyle, that a right Noetherian right PCI domain that is also left Ore is left PCI; by
Damiano's theorem the Noetherian hypothesis is automatic. Whether every right PCI ring is left
PCI has been open since Faith (1973); Boyle and Goodearl (1975), Cozzens and Faith (1975),
Damiano (1979) and a survey preprint of Jain and Srivastava (2009) repeat the question. A
related question goes back to Cozzens and Faith (1975, §7): must a left V-domain be a right
V-domain? Jain–Lam–Leroy (2009) and Behboodi–Daneshvar–Vedadi (2018) restate it as open.

Cozzens and Faith (§7) suggested looking for a counterexample among Ore extensions
`K[t; σ, δ]` over a division ring `K`, where `σ` is an endomorphism that is not onto.
Jain, Lam and Leroy showed that a left V-domain of this form is right PCI if and only if `σ`
is onto. They also said they had no example of a left V-domain `K[t; σ, δ]` with `σ` not
onto.

The paper constructs such an example. It is a countable domain `R = K[t; σ, δ]` with the
following properties:

- `K` is a free field: Cohn's universal field of fractions of a free algebra over `ℚ`.
- `σ` is an endomorphism of `K` that is not surjective, and `δ` is a `σ`-derivation.
- `R` is a left PCI ring and a left V-ring.
- `R` is not right Ore, not a right PCI ring and not a right V-ring.

It follows that:

- `Rᵒᵖ` is a right PCI ring that is not left PCI (Corollary 2.6 (1)). This answers the
  Cozzens–Faith and Damiano question in the negative.
- `Rᵒᵖ` is a right PCI domain, and a right V-domain, that is not left Ore (Corollary 2.6 (2)).
- `R` is a left V-domain that is not a right V-domain (Corollary 2.6 (3)). This answers the
  Cozzens–Faith V-domain question in the negative.
- `R` is an Ore extension `K[t; σ, δ]` that is a left V-domain with `σ` not onto
  (Corollary 2.6 (4)). Jain, Lam and Leroy said they had no such example.

The paper's Main Theorem also states that `R` is simple, a principal left ideal domain, left
Noetherian and left hereditary. These claims are not among the compared statements.

## The compared statements

`comparator.json` names three theorems in the `LeftPCI` namespace. The statements and the
definitions they use are in `Challenge.lean`:

```lean
universe u

namespace LeftPCI

/-- A ring is a **left PCI ring** ("proper cyclics are injective") if every proper cyclic left
module — a quotient `R ⧸ I` of `R` by a left ideal `I` (`Ideal R = Submodule R R`) which is not
isomorphic to `R` as a left `R`-module — is an injective `R`-module. -/
def IsLeftPCIRing (R : Type u) [Ring R] : Prop :=
  ∀ I : Ideal R, ¬ Nonempty ((R ⧸ I) ≃ₗ[R] R) → Module.Injective R (R ⧸ I)

/-- A ring is a **right PCI ring** if its opposite ring is a left PCI ring: right `R`-modules
are left `Rᵐᵒᵖ`-modules, so this is the right-handed version of `IsLeftPCIRing`. -/
def IsRightPCIRing (R : Type u) [Ring R] : Prop :=
  IsLeftPCIRing Rᵐᵒᵖ

/-- A ring is a **left V-ring** if every simple left `R`-module is injective. -/
def IsLeftVRing (R : Type u) [Ring R] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M], IsSimpleModule R M → Module.Injective R M

/-- A ring is a **right V-ring** if its opposite ring is a left V-ring. -/
def IsRightVRing (R : Type u) [Ring R] : Prop :=
  IsLeftVRing Rᵐᵒᵖ

/-- A domain is **right Ore** if any two non-zero elements have a non-zero common right
multiple: `a R ∩ b R ≠ 0`. For a ring that is not a domain this is not the general right Ore
condition, which is stated for regular elements; it is only used here together with `IsDomain`. -/
def IsRightOre (R : Type u) [Ring R] : Prop :=
  ∀ a b : R, a ≠ 0 → b ≠ 0 → ∃ x y : R, a * x = b * y ∧ a * x ≠ 0

/-- **Main Theorem** (Theorem 1.1 of the paper): a countable domain which is a left PCI ring and a
left V-ring but is not right Ore, not a right PCI ring and not a right V-ring. -/
theorem exists_isLeftPCIRing_not_isRightPCIRing :
    ∃ (R : Type) (_ : Ring R), IsDomain R ∧ Countable R ∧ IsLeftPCIRing R ∧ IsLeftVRing R ∧
      ¬ IsRightOre R ∧ ¬ IsRightPCIRing R ∧ ¬ IsRightVRing R := by
  sorry

/-- A left PCI ring need not be right PCI: the Main Theorem's example. Passing to the opposite
ring, this is Corollary 2.6 (1) of the paper, that a right PCI ring need not be left PCI. -/
theorem not_forall_isLeftPCIRing_imp_isRightPCIRing :
    ¬ ∀ (R : Type) [Ring R], IsLeftPCIRing R → IsRightPCIRing R := by
  sorry

/-- A left V-domain need not be a right V-domain (Corollary 2.6 (3)). -/
theorem not_forall_isLeftVRing_imp_isRightVRing :
    ¬ ∀ (R : Type) [Ring R], IsDomain R → IsLeftVRing R → IsRightVRing R := by
  sorry

end LeftPCI
```

This is `Challenge.lean` without its five `import Mathlib.…` lines and module docstring. The library
repeats the definitions verbatim in `LeftPCI/Counterexample/Defs.lean`, and Comparator checks
that the two copies agree.

**Fidelity.**

- **Right-handed notions.** They are formalized through the opposite ring `Rᵐᵒᵖ`, which is
  the standard Mathlib idiom: right `R`-modules are left `Rᵐᵒᵖ`-modules.
- **Proper cyclic modules.** A proper cyclic left module is a quotient `R ⧸ I` that is not
  isomorphic to `R`. Every cyclic module is such a quotient, and injectivity is preserved by
  isomorphisms, so this is the usual notion.
- **Universes.** `IsLeftVRing` quantifies over simple modules in the universe of `R`. The
  compared statements live in `Type`.
- **Base field.** The paper works over any countable commutative field `k`. The Lean
  development takes `k = ℚ`.
- **Proposition 2.2.** Formalized as in the paper: every proper cyclic left module `R/Rf` is
  divisible (`IsCFClosed`), hence injective by Baer's criterion over the principal left ideal
  domain `R`. The "left V" step (a maximal left ideal is non-zero, so `R/L` is a proper cyclic
  module) is `isLeftVRing_of_isLeftPCIRing`, stated for any ring that is not a division ring.
- **"Not right PCI" and "not right V".** Both come from the countability argument of
  Lemma 2.4, as in the paper; Cozzens–Faith 6.17 is not used. Lemma 2.4 is proved on the left
  and applied to `Rᵐᵒᵖ`.
- **Construction.** Construction 4.1 is formalized with `Z = ℕ`: the tasks `(f, g, e)` are
  coded by an injection into `ℕ`, and the generators `x^τ_{l,j}` are the symbols
  `⟨code τ, l, j⟩` under a pairing function. Unused symbols get `d = 0`, as in the paper.
- **Cohn's theory.** Theorem 3.1 (Cohn) is proved in this repository, not assumed: free
  algebras are firs, and a semifir has a universal field of fractions with the universal
  property of a localization. The general Ore extension `K[t; σ, δ]` is also built here,
  because Mathlib only has the case `δ = 0`.
- **Corollary 2.6.** Items (1) and (3) are compared theorems. Item (1) is stated for `R`
  itself (a left PCI ring need not be right PCI), which is the paper's statement about `Rᵒᵖ`
  read through the opposite ring, so both compared corollaries use the same ring. Items (2)
  and (4) are not stated separately in Lean. Item (2) is visible in the Main Theorem's
  statement (`R` is not right Ore, so `Rᵐᵒᵖ` is not left Ore). Item (4) is visible in the
  construction; the compared existential statement does not record that the witness is an
  Ore extension.

## Proof account

The following summarizes the paper; section numbers refer to it.

**Section 2: reduction to linear equations.** Let `R = K[t; σ, δ]` with coefficients on the
left and `t a = σ(a) t + δ(a)`. For a monic `f` of degree `n`, identify `R/Rf` with `Kⁿ`.
Left multiplication by `t` then becomes the pseudo-linear map `T_f(v) = σ(v) C_f + δ(v)`,
where `C_f` is the companion matrix of `f`, and left multiplication by `g` becomes `g(T_f)`
(Lemma 2.1). Suppose that `g(T_f)` is onto `Kⁿ` for all monic `f, g` of degree at least 1.
Then every proper cyclic left module `R/Rf` is divisible, hence injective by Baer's criterion
over the principal left ideal domain `R`; so `R` is left PCI, simple, and left V
(Proposition 2.2).

Now suppose `σ` is not onto and `c ∉ σ(K)`. A degree count shows that `tR ∩ ctR = 0`, so `R`
is not right Ore (Proposition 2.3). A cardinality argument in the spirit of Lawrence then shows
that when `R` is countable, no non-zero countable right module is injective: the right ideal
`⊕ᵢ bⁱaR` is free of countable rank, so an injective module `E` would satisfy `|E^ℕ| ≤ |E|`.
In particular no simple right module is injective, so `R` is neither right V nor right PCI
(Lemma 2.4). The Main Theorem thus reduces to Theorem 2.5: there is a countable `(K, σ, δ)`
with `σ` not onto over which every `g(T_f)` is onto.

**Section 3: free fields.** Let `𝓕(Y)` be the free field on a set `Y`: the universal field of
fractions of the free algebra `ℚ⟨Y⟩` (Theorem 3.1, Cohn). Two homomorphisms out of `𝓕(Y)`
that agree on `ℚ⟨Y⟩` are equal (Lemma 3.2). Choose an injective map `s : Y → Y` and an
arbitrary map `d : Y → 𝓕(Y)`. There are an endomorphism `σ` of `𝓕(Y)` and a `σ`-derivation
`δ` extending them (Proposition 3.5). To see this, send `y` to the matrix
`[[s(y), d(y)], [0, y]]`. This gives a homomorphism from `ℚ⟨Y⟩` to the upper triangular
`2 × 2` matrices over `𝓕(Y)`. It inverts every full matrix, so it extends to `𝓕(Y)`, and `σ`
and `δ` can be read off the matrix entries. If `y₀ ∉ s(Y)`, then `y₀ ∉ σ(𝓕(Y))`. The proof
uses the automorphism `y₀ ↦ y₀ + 1`, which fixes `σ(𝓕(Y))` but moves `y₀` (Lemma 3.6).

**Section 4: the construction.** Take `Y = {y₀, y₁, …} ⊔ Z` with `Z` countably infinite,
`K = 𝓕(Y)`, and `s` the shift `yᵢ ↦ yᵢ₊₁` on the first part and the identity on `Z`. A task
is a triple `(f, g, e)`: the coefficient lists of monic `f, g` of degrees `n, m ≥ 1` and a
right-hand side `e ∈ Kⁿ`. Tasks depend only on `K`, not on the `σ, δ` still to be chosen. For
every task reserve `nm` generators in `Z`, forming vectors `x₀, …, x_{m-1} ∈ Kⁿ`. These
generators are fixed by `σ`, so `T_f(x_j) = x_j C_f + δ(x_j)`, and prescribing `δ` on them is
the same as prescribing `T_f`. Choose `d` so that `T_f(x_j) = x_{j+1}` and
`T_f(x_{m-1}) = e − Σ_{j<m} g_j x_j`; then `g(T_f)(x₀) = e`. The prescriptions involve only
the coefficients of `f`, `g` and `e`, so all of them are imposed at once by Proposition 3.5,
and `y₀ ∉ σ(K)` by Lemma 3.6. There is no tower of fields (Construction 4.1, which proves
Theorem 2.5).

## Repository layout

- `Challenge.lean`: the statement surface (definitions and the three compared theorems with
  `sorry`). It imports only Mathlib.
- `Solution.lean`: imports the library. The compared theorems are proved in the imported
  environment.
- `LeftPCI.lean`: the library root, which imports every module below.
- `LeftPCI/FreeAlgebra/`: Cohn's theorem that a free algebra over a field is a fir, proved via
  the weak algorithm (`Words`, `WeakAlgorithm`, `Fir`). This is the first half of Theorem 3.1.
- `LeftPCI/FreeField/`: full matrices and honest maps (`Full`, `FullCalculus`); semifirs are
  Sylvester domains (`Sylvester`); the universal localization at full matrices
  (`UniversalLocalization`); the display model (`DisplayModel`); Cramer's rule (`Cramer`);
  the universal field of fractions (`UniversalField`, `Interface`). This is the second half
  of Theorem 3.1, with Lemmas 3.2 and 3.3 derived from it in `Interface`.
- `LeftPCI/OrePoly/`: the Ore extension `K[t; σ, δ]` (`Basic`), its degree theory (`Degree`),
  the left division algorithm and principal left ideals (`Division`), and the failure of the
  right Ore condition (`RightOre`).
- `LeftPCI/Counterexample/`, following the paper:
  - `Defs`: the definitions of the statement.
  - `Adjoin`: Section 2.1 (the modules `R/Rf`, `T_f` and Lemma 2.1).
  - `OreExtension`: Propositions 2.2 and 2.3.
  - `Countable`: Lemma 2.4.
  - `PCIToV`: the "left V" step of Proposition 2.2 (a PCI ring that is not a division ring is
    a V-ring).
  - `FreeFieldExt`: Section 3.
  - `Direct`: Construction 4.1 and Theorem 2.5.
  - `Closure`: the Main Theorem and Corollary 2.6 (1), (3).
- `paper/`: the paper (LaTeX source and PDF).
- `comparator.json`: the `lake comparator` configuration naming the three compared theorems.
- `formalization.yaml`: structured metadata (provenance, sources, automation, fidelity,
  review) in the mathlib-initiative v0.4 format.
- `scripts/verify-comparator.sh`: runs the toolchain's `lake comparator` the way Palomar does.
- `scripts/validate-formalization.rb`: checks the metadata file.
- `test/`: tests for the metadata check.
- `.github/workflows/ci.yml`: CI (build, metadata, licence and Comparator). The layout
  comes from the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate).

## Verification

The following needs Linux, Git, Ruby, Python 3 and `bwrap` (bubblewrap), and several GiB of
disk space for Mathlib:

```sh
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

CI runs the same checks. This repository is prepared for submission to Palomar through the
[submission form](https://submit.palomar-registry.org/), using the full 40-character commit
SHA. The responsible maintainer submits it as a separate step.

## Licence

This repository snapshot, including the paper, is licensed under the Apache License 2.0 (see
`LICENSE`). Cited papers and books, Mathlib and other dependencies retain their own licences.
