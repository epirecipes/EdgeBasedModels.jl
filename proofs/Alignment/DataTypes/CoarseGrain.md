# DataTypes — group CoarseGrain (blind-safe)

Opaque vocabulary for claims in group `CoarseGrain`. No definition bodies, instance
bodies or theorem statements. Docstrings are quoted verbatim.

## (a) Imports

```lean
import EBCMCategory.CoarseGrain   -- also brings EBCMCategory.EpiCategory
```

## (b) Shared data types

All data types of `DataTypes/EpiCategory.md` are available: `PGFData` (fields `mean`,
`secondFactorial`, `mean_pos`, `secondFactorial_nonneg`), `SIRParams`, `EpiModel`
(fields `dim : ℕ`, `R0 : ℚ`) with its `Preorder` instance (refinement, written `≤`).

## (c) Operations under test (opaque signatures)

| name | signature | docstring |
|---|---|---|
| `coarseGrain` | `EpiModel → EpiModel` | The coarse-graining map F on abstract models. Projects any model to a 3-dimensional node model, preserving R₀. |
| `PGFData.excessDegree` | `PGFData → ℚ` | The excess degree ratio: ψ''(1)/ψ'(1). |
| `PGFData.variance` | `PGFData → ℚ` | Degree variance: Var(k) = ψ''(1) + ψ'(1) - (ψ'(1))². |
| `PGFData.dispersionIndex` | `PGFData → ℚ` | Index of dispersion: σ²/κ. Equals 1 iff Poisson. |
| `PGFData.poisson` | `(κ : ℚ) → 0 < κ → PGFData` | The Poisson PGF with mean κ. Key property: ψ''(1) = κ². |

Module header text: "The **coarse-graining** map sends an edge-based model to its
node-based projection by evaluating the PGF at the edge-transmission-failure probability:
S = ψ(θ), R = R, I = 1 - S - R". The module title calls it "The forgetful functor
F: Edge → Node". In the notation of the claims, F = `coarseGrain`, κ = `ψ.mean`,
σ² = `ψ.variance`.

## (d) Mathlib notions

* `Monotone` (for "F is monotone"), `Function.Injective` (for "not injective").
* `CategoryTheory.Functor` / thin categories (`Preorder.smallCategory`) if "functor" is
  read literally.
* ℚ field arithmetic (`field_simp`-style identities are fine in shadows; checkers are
  structural).
