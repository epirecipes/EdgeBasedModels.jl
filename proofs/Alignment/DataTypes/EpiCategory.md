# DataTypes — group EpiCategory (blind-safe)

Vocabulary a shadow author may use for claims in group `EpiCategory`.
Signatures are opaque: definition bodies, instance bodies and theorem statements
are deliberately omitted. Docstrings are quoted verbatim (they are intent text).

## (a) Imports

```lean
import EBCMCategory.EpiCategory   -- brings Mathlib.Tactic
```

All names below live at the root namespace unless a namespace is shown.
Dot notation works: `ψ.excessDegree`, `p.transmissibility`, `m.dim`.

## (b) Shared data types

### `structure PGFData`

> Abstract probability generating function data.
> A PGF ψ of a degree distribution is characterised by:
> * `mean` = ψ'(1): the mean degree κ
> * `secondFactorial` = ψ''(1): the second factorial moment
> * `mean_pos`: the mean degree is positive

| field | type |
|---|---|
| `mean` | `ℚ` |
| `secondFactorial` | `ℚ` |
| `mean_pos` | `0 < mean` |
| `secondFactorial_nonneg` | `0 ≤ secondFactorial` |

Note: the record stores only these two numbers; it contains no function ψ.

### `structure SIRParams`

> Transmission and recovery parameters for an SIR model.

| field | type | comment |
|---|---|---|
| `β` | `ℚ` | transmission rate |
| `γ` | `ℚ` | recovery rate |
| `β_pos` | `0 < β` | |
| `γ_pos` | `0 < γ` | |

### `structure EpiModel`

> An epidemic model, characterised abstractly by its state-space dimension
> (a proxy for information content) and R₀ (a shared observable).

| field | type |
|---|---|
| `dim` | `ℕ` |
| `R0` | `ℚ` |

Instances (bodies omitted): `instance : LE EpiModel`, `instance : Preorder EpiModel`.
Module header text: "Both are formalised as preorders under a "refinement" relation:
M₁ ≤ M₂ iff M₂ carries at least as much structural information as M₁."
Write refinement as `m₁ ≤ m₂`.

## (c) Operations under test (opaque signatures)

| name | signature | docstring |
|---|---|---|
| `PGFData.excessDegree` | `PGFData → ℚ` | The excess degree ratio: ψ''(1)/ψ'(1). |
| `PGFData.variance` | `PGFData → ℚ` | Degree variance: Var(k) = ψ''(1) + ψ'(1) - (ψ'(1))². |
| `PGFData.poisson` | `(κ : ℚ) → (hκ : 0 < κ) → PGFData` | The Poisson PGF with mean κ. Key property: ψ''(1) = κ². |
| `PGFData.dispersionIndex` | `PGFData → ℚ` | Index of dispersion: σ²/κ. Equals 1 iff Poisson. |
| `SIRParams.transmissibility` | `SIRParams → ℚ` | Transmissibility across a single edge: T = β/(β+γ). |
| `nodeModel` | `(p : SIRParams) → (κ : ℚ) → EpiModel` | A node-based SIR model: 3 state variables (S, I, R). |
| `edgeModel` | `(p : SIRParams) → (ψ : PGFData) → EpiModel` | An edge-based SIR model: 4 state variables (θ, φ_I, R + algebraic φ_S). |

## (d) Mathlib notions a faithful formalisation might need

* ℚ field arithmetic (`/`, `^`), `Preorder`, `LE.le`.
* For genuine PGFs (if the text is read literally): `PMF ℕ` or `ℕ → ℝ` weights with
  `HasSum`/`tsum`, `Polynomial.eval` / `PowerSeries`, `deriv`, `iteratedDeriv 2`,
  `Real.exp` (Poisson PGF `exp (κ (z - 1))`), `ProbabilityTheory.variance`.
* `CategoryTheory.Category`, `CategoryTheory.Functor` (the header speaks of categories
  **Node** and **Edge**); a preorder is a thin category via `Preorder.smallCategory`.
