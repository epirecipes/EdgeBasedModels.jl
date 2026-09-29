# DataTypes — group DynamicLimits (blind-safe)

Opaque vocabulary for claims in group `DynamicLimits`. No definition bodies or theorem
statements. Docstrings are quoted verbatim.

## (a) Imports

```lean
import EBCMCategory.DynamicLimits   -- also brings CoarseGrain, EpiCategory, Mathlib.Tactic
```

## (b) Shared data types

### `structure DynamicEBCM`

> A dynamic EBCM: the standard edge model augmented with a dormant-edge
> variable φ_D for tracking edge rewiring dynamics.
>
> The dynamic SIR EBCM has **5 ODE variables**: θ, φ_I, R, φ_D, (φ_S algebraic).
> Compare with the static EBCM's 4 variables.

| field | type |
|---|---|
| `disease` | `SIRParams` |
| `pgf` | `PGFData` |

Note: there are no rewiring-rate fields (η₁, η₂) and no ODE right-hand side.

From `DataTypes/EpiCategory.md`: `SIRParams` (β, γ, positivity), `PGFData` (mean,
secondFactorial, …), `EpiModel` (`dim : ℕ`, `R0 : ℚ`, `Preorder` = refinement).

## (c) Operations under test (opaque signatures)

| name | signature | docstring |
|---|---|---|
| `DynamicEBCM.dim` | `DynamicEBCM → ℕ` | The state-space dimension of a dynamic EBCM: always 5. (θ, φ_S, φ_I, R, plus the new φ_D for dormant edge stubs.) |
| `DynamicEBCM.R0` | `DynamicEBCM → ℚ` | R₀ for a dynamic EBCM. **Key result**: R₀ does NOT depend on the rewiring rate. It depends only on transmissibility and the excess degree ratio, because rewiring preserves the degree distribution. |
| `DynamicEBCM.toEpiModel` | `DynamicEBCM → EpiModel` | Project a dynamic EBCM to an abstract EpiModel. |
| `DynamicEBCM.staticLimit` | `DynamicEBCM → EpiModel` | The **static limit** (η₁, η₂ → 0): rewiring terms vanish, φ_D decouples from the system, and we recover the standard 4-variable EBCM. The R₀ is preserved. |
| `DynamicEBCM.fastRewiringLimit` | `DynamicEBCM → EpiModel` | The **fast-rewiring limit** (η₁, η₂ → ∞): the network reshuffles so fast that at each instant it looks like a fresh configuration model draw. Edge correlations are destroyed, and only mean-degree information survives. The system collapses to a 3D mean-field model. Crucially, R₀ now uses the **mean degree** κ rather than the excess degree ψ''(1)/ψ'(1), because the fast-rewiring limit destroys the degree-heterogeneity amplification effect. |
| `coarseGrain` | `EpiModel → EpiModel` | The coarse-graining map F on abstract models. Projects any model to a 3-dimensional node model, preserving R₀. |
| `edgeModel` | `SIRParams → PGFData → EpiModel` | An edge-based SIR model: 4 state variables (θ, φ_I, R + algebraic φ_S). |
| `SIRParams.transmissibility` | `SIRParams → ℚ` | Transmissibility across a single edge: T = β/(β+γ). |
| `PGFData.excessDegree` | `PGFData → ℚ` | The excess degree ratio: ψ''(1)/ψ'(1). |
| `PGFData.poisson` | `(κ : ℚ) → 0 < κ → PGFData` | The Poisson PGF with mean κ. Key property: ψ''(1) = κ². |
| `levelDim` (module `EBCMCategory.Hierarchy`, not imported here) | `ModelLevel → ℕ → ℕ` | State-space dimension at each level for an N-node SIR network model. |

In the claims: "dynamic EBCM (dim …)" = `m.toEpiModel` / `m.dim`; "static EBCM" =
`m.staticLimit`; "fast-rewiring limit / mean-field" = `m.fastRewiringLimit`;
"EBCM R₀" = `m.R0`; F = `coarseGrain`; "refines"/"coarser" = `≤` on `EpiModel`.

## (d) Mathlib notions

* `Nat` order, `EpiModel` preorder `≤`.
* For limits read literally (η → 0, η → ∞): `Filter.Tendsto`, `nhds`, `Filter.atTop`,
  `nhdsWithin`; a rate parameter would have to be introduced by the shadow.
* "Independent of the rewiring rate": `∀ η₁ η₂, f η₁ = f η₂` (requires a rate argument).
