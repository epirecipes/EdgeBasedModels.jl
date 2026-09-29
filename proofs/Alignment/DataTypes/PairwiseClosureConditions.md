# DataTypes — group `PairwiseClosureConditions`

Blind-safe vocabulary for shadow authors: imports, data types and **opaque signatures plus
docstrings** of the definitions the claims mention. No theorem statements, proofs,
definition bodies or instance bodies. Claim texts: `Alignment/claims_blind.yaml`.

## (a) Imports and namespaces

```lean
import EBCMCategory.PairwiseClosureConditions   -- imports Mathlib.Tactic only
open scoped BigOperators
```

* Declarations live in `namespace PairwiseClosureConditions`.
* The module declares the section variables
  `variable {α : Type} [Fintype α] [DecidableEq α]`; `α` is the finite set of node states `A`
  indexing the closed triples `[ASI]_A`. Write shadows in a section with the same `variable`
  line (the instance arguments are part of the definitions' signatures).
* All numbers are rationals (`ℚ`). Sums are `Finset.sum` over `Finset.univ`, written `∑ a, f a`.

## (b) Data types

No structures or inductive types. Weights are plain functions `p : α → ℚ`; the base term
(`B = (n - 1)[SI]` in the text) is a plain rational `base : ℚ`.

## (c) Operations under test (opaque signatures + docstrings)

| signature | docstring |
|---|---|
| `tripleTerm (base : ℚ) (p : α → ℚ) (a : α) : ℚ` | The triple contribution associated to state `a` under a normalized closure. |
| `convexMix (φ x y : ℚ) : ℚ` | Convex mixing between an unclustered and clustered weight. This is the algebraic shape used by Barnard-style improved closures. |
| `keelingFactor (φ corr : ℚ) : ℚ` | Keeling-style multiplicative clustering factor. |
| `barnardWeights (φ : ℚ) (p_uc p_c : α → ℚ) (a : α) : ℚ` | Barnard-style mixed weights: a convex combination of two normalized families of weights. |
| `keelingWeights (φ : ℚ) (p corr : α → ℚ) (a : α) : ℚ` | Keeling-style reweighted probabilities: the baseline weight `p a` is multiplied by a correlation correction. |

(The implicit arguments `{α : Type} [Fintype α] [DecidableEq α]` precede each signature that
mentions `α`.)

Vocabulary used in the claim texts:

* "normalized weights": `∑ a, p a = 1`; "nonnegative weights": `∀ a, 0 ≤ p a`.
* "total triple mass": `∑ a, tripleTerm base p a`; "triple count/term": `tripleTerm base p a`.
* "safe" closure (text's usage): total-mass conservation and pointwise nonnegativity of the
  triple terms together.
* The mixing parameter `φ` is the clustering weight; "convex" means `0 ≤ φ ∧ φ ≤ 1`.

## (d) Mathlib notions

* `Finset.sum`, `Finset.univ`, `Fintype`, `Finset.mul_sum`, `Finset.sum_add_distrib`,
  `Finset.single_le_sum` (for reference only; checkers must stay structural).
* Order and field structure of `ℚ` (`≤`, `<`, `*`, `-`).
* Existence statements (`∃ α p base, …`) for non-implication claims need a concrete finite type,
  e.g. `Fin 2` or `Bool`.
