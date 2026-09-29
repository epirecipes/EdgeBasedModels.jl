# DataTypes — group Hierarchy (blind-safe)

Opaque vocabulary for claims in group `Hierarchy`. No definition bodies or theorem
statements. Docstrings are quoted verbatim.

## (a) Imports

```lean
import EBCMCategory.Hierarchy   -- also brings CoarseGrain, EpiCategory, Mathlib.Tactic
```

## (b) Shared data types

### `inductive ModelLevel`

> Levels in the modelling hierarchy.

Constructors: `fullStochastic`, `pairApproximation`, `edgeBased`, `meanField`
(deriving `DecidableEq`, `Repr`). Written `.meanField` etc. / `ModelLevel.meanField`.

Also available (see `DataTypes/EpiCategory.md`): `PGFData` (fields `mean`,
`secondFactorial`, `mean_pos`, `secondFactorial_nonneg`), `SIRParams`, `EpiModel`.

## (c) Operations under test (opaque signatures)

| name | signature | docstring |
|---|---|---|
| `levelDim` | `(level : ModelLevel) → (N : ℕ) → ℕ` | State-space dimension at each level for an N-node SIR network model. |
| `PGFData.poisson` | `(κ : ℚ) → 0 < κ → PGFData` | The Poisson PGF with mean κ. Key property: ψ''(1) = κ². |
| `PGFData.excessDegree` | `PGFData → ℚ` | The excess degree ratio: ψ''(1)/ψ'(1). |
| `PGFData.variance` | `PGFData → ℚ` | Degree variance: Var(k) = ψ''(1) + ψ'(1) - (ψ'(1))². |
| `SIRParams.transmissibility` | `SIRParams → ℚ` | Transmissibility across a single edge: T = β/(β+γ). |
| `nodeModel` | `SIRParams → ℚ → EpiModel` | A node-based SIR model: 3 state variables (S, I, R). |
| `edgeModel` | `SIRParams → PGFData → EpiModel` | An edge-based SIR model: 4 state variables (θ, φ_I, R + algebraic φ_S). |
| `poissonLift` | `EpiModel → EpiModel` (in `EBCMCategory.GaloisPair`, not imported by Hierarchy) | The Poisson lift G: Node → Edge. Embeds a node model into the canonical 4D edge model with Poisson degree distribution. |
| `coarseGrain` | `EpiModel → EpiModel` | The coarse-graining map F on abstract models. Projects any model to a 3-dimensional node model, preserving R₀. |

"Number of variables" of a level = `levelDim level N`. "Poisson" for a `ψ : PGFData`
can be expressed as `ψ = PGFData.poisson ψ.mean ψ.mean_pos` (or via the moment
fields); "excess degree = mean" as `ψ.excessDegree = ψ.mean`.

## (d) Mathlib notions

* `Nat` order and `^`, `∀ N, 1 ≤ N → …`.
* Uniqueness: `∃!`, or `∀ ψ, P ψ → ψ = …`.
* "Parameterised by": `Function.Bijective`, `Equiv`, `Set.range`.
* For genuine PGFs (literal reading): `PMF ℕ`, `HasSum`, `deriv`, `Real.exp`.
