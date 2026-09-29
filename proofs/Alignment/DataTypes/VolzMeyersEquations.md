# DataTypes — group VolzMeyersEquations (blind-safe)

Opaque vocabulary for claims in group `VolzMeyersEquations`. No definition bodies or
theorem statements. Docstrings and field comments are quoted verbatim.

## (a) Imports

```lean
import EBCMCategory.VolzMeyersEquations   -- also brings DynamicLimits, CoarseGrain, EpiCategory
```

## (b) Shared data types

### `structure VMState` — "State of the Volz–Meyers neighbour-exchange system."

| field | type | comment |
|---|---|---|
| `θ` | `ℚ` | probability a stub has not transmitted |
| `P₁` | `ℚ` | fraction of ego's stubs → infected |
| `P_S` | `ℚ` | fraction of ego's stubs → susceptible |
| `M₁` | `ℚ` | population fraction of stubs → infected |
| `I` | `ℚ` | infected population fraction |
| `R` | `ℚ` | recovered population fraction |

Anonymous-constructor order: `⟨θ, P₁, P_S, M₁, I, R⟩`.

### `structure VMParams` — "Parameters for the VM model."

| field | type | comment |
|---|---|---|
| `β` | `ℚ` | per-edge transmission rate |
| `γ` | `ℚ` | recovery rate |
| `ρ` | `ℚ` | edge swap rate (≥ 0) |
| `κ` | `ℚ` | mean degree (ψ'(1)) |
| `β_pos` | `0 < β` | |
| `γ_pos` | `0 < γ` | |
| `ρ_nonneg` | `0 ≤ ρ` | |

Anonymous-constructor order: `⟨β, γ, ρ, κ, β_pos, γ_pos, ρ_nonneg⟩`.
Note: no PGF ψ (function) is part of either structure; S is not a field.

## (c) Operations under test (opaque signatures)

| name | signature | docstring |
|---|---|---|
| `VMState.excessRatio` | `VMState → ℚ → ℚ` | The excess degree ratio θ·ψ''(θ)/ψ'(θ). For Poisson(κ): this equals κ·θ (since ψ''(θ)/ψ'(θ) = κ). |
| `VMState.edgeHazard` | `VMState → VMParams → ℚ` | The edge hazard: β·P₁ (per-stub force of infection). |
| `VMState.dθ` | `VMState → VMParams → ℚ` | dθ/dt = −β·P₁·θ |
| `VMState.incidence` | `VMState → VMParams → ℚ` | Incidence = β·P₁·θ·κ (for Poisson, ψ'(θ) = κ·ψ(θ)). |
| `VMState.dI` | `VMState → VMParams → ℚ` | d(pop_I)/dt = incidence − γ·pop_I |
| `VMState.dR` | `VMState → VMParams → ℚ` | d(pop_R)/dt = γ·pop_I |
| `VMState.P_R` | `VMState → ℚ` | P_R = 1 − P₁ − P_S (the fraction of ego stubs → recovered). This is derived, not tracked. |
| `staticParams` | `(β γ κ : ℚ) → 0 < β → 0 < γ → VMParams` | Static parameters: ρ = 0. |
| `vmInitialState` | `(sf : ℚ) → VMState` | Standard VM initial conditions with node-level seed fraction sf. |

Dot notation: `s.dθ p`, `s.incidence p`, `s.P_R`.

Module-header equation table (intent text, lines 21-30 of the module):

| Equation | ODE |
|---|---|
| θ̇ | = −β P₁ θ |
| Ṗ_S | = β P_S P₁ (1 − θ ψ''(θ)/ψ'(θ)) + ρ(ψ'(θ)/ψ'(1) − P_S) |
| Ṗ₁ | = β P₁ P_S θ ψ''(θ)/ψ'(θ) − P₁(1−P₁)β − P₁ γ + ρ(M₁ − P₁) |
| Ṁ₁ | = −γ M₁ + β P₁ (θ² ψ''(θ) + θ ψ'(θ))/ψ'(1) |
| pop_I | = β P₁ θ ψ'(θ) − γ pop_I |
| pop_R | = γ pop_I |

"Susceptible fraction: S = ψ(θ)". Only θ̇, pop_I, pop_R have operations above; there
are no operations for Ṗ_S, Ṗ₁, Ṁ₁ or S.

## (d) Mathlib notions

* ℚ order/arithmetic for sign conditions on rate expressions.
* For trajectory statements (literal reading): `HasDerivAt`, `deriv`, `Antitone`,
  `MonotoneOn`, `Real.exp` (Poisson S = exp(κ(θ−1))).
* For ρ → ∞ / ρ → 0 limits: `Filter.Tendsto`, `Filter.atTop`, `nhds`.
