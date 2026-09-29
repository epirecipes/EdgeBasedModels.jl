# DataTypes — group GaloisPair (blind-safe)

Opaque vocabulary for claims in group `GaloisPair`. No definition bodies or theorem
statements. Docstrings are quoted verbatim.

## (a) Imports

```lean
import EBCMCategory.GaloisPair   -- also brings CoarseGrain and EpiCategory
```

## (b) Shared data types

From `DataTypes/EpiCategory.md`: `EpiModel` (fields `dim : ℕ`, `R0 : ℚ`) with its
`Preorder` instance (refinement, `≤`); `PGFData`; `SIRParams`.

## (c) Operations under test (opaque signatures)

| name | signature | docstring |
|---|---|---|
| `coarseGrain` | `EpiModel → EpiModel` | The coarse-graining map F on abstract models. Projects any model to a 3-dimensional node model, preserving R₀. |
| `poissonLift` | `EpiModel → EpiModel` | The Poisson lift G: Node → Edge. Embeds a node model into the canonical 4D edge model with Poisson degree distribution. |
| `nodeModel` | `SIRParams → ℚ → EpiModel` | A node-based SIR model: 3 state variables (S, I, R). |
| `edgeModel` | `SIRParams → PGFData → EpiModel` | An edge-based SIR model: 4 state variables (θ, φ_I, R + algebraic φ_S). |
| `PGFData.poisson` | `(κ : ℚ) → 0 < κ → PGFData` | The Poisson PGF with mean κ. Key property: ψ''(1) = κ². |

In the claims, F = `coarseGrain`, G = `poissonLift`; `F ∘ G` is `coarseGrain ∘ poissonLift`.

## (d) Mathlib notions

* `Monotone`, `Function.comp` (`∘`), `id`, `funext` (function equality vs pointwise).
* `GaloisConnection l u` (Mathlib: `∀ a b, l a ≤ b ↔ a ≤ u b`), `GaloisInsertion`,
  `Function.LeftInverse` / `Function.RightInverse`.
* `CategoryTheory.Adjunction` (unit/counit) if "counit" / "adjunction-like" is read literally.
