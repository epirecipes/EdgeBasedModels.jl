# DataTypes — group Obstructions (blind-safe)

Opaque vocabulary for claims in group `Obstructions`. No definition bodies or theorem
statements. Docstrings and constructor comments are quoted verbatim.

## (a) Imports

```lean
import EBCMCategory.Obstructions   -- brings Mathlib.Tactic only
```

Root namespace for the classification part; namespace `MarginalisationObstruction` for
the Theorem T2 part (`open MarginalisationObstruction`).

## (b) Shared data types

### `inductive NetworkType` — "Classification of network structure."

| constructor | comment |
|---|---|
| `configurationModel` | tree-like (standard EBCM is exact) |
| `clusteredTriangles` | clustering via triangles (triangle EBCM is exact) |
| `degreeCorrelated` | degree-degree correlations (multi-type EBCM works) |
| `multiplexStaticDyn` | static+dynamic layers (multiplex EBCM works) |

### `inductive TransitionType`

> Classification of disease dynamics.
> Non-Markovian dynamics are NOT an absolute obstruction — they change
> the EBCM from an ODE to a PDE (age-structured von Foerster equation).
> The Erlang approximation recovers an ODE system with more variables.

| constructor | comment |
|---|---|
| `markovian` | exponential waiting times → ODE EBCM |
| `erlangStaged` | n-stage Erlang approximation → ODE EBCM (more vars) |
| `generalNonMarkov` | general τ(a), q(a) → PDE EBCM (exact, infinite-dim) |

Note: `erlangStaged` carries no stage count n.

### `inductive InitCondType` — "Classification of initial conditions."

| constructor | comment |
|---|---|
| `uniform` | i.i.d. infection with probability ε |
| `localised` | spatially correlated initial outbreak |

### `inductive SystemType` — "The type of mathematical system required."

| constructor | comment |
|---|---|
| `ode` | finite-dimensional ODE system |
| `pde` | age-structured PDE (von Foerster + integral equations) |
| `impossible` | no EBCM variant works |

All four derive `DecidableEq, Repr`.

### Theorem-T2 surrogate (namespace `MarginalisationObstruction`)

* `inductive Idx4 | a | b` — "Index type for the order-4 surrogate (a = C₄ SISI, b = C₄ SSSS)."
* `inductive Idx3 | c` — "Index type for the order-3 surrogate (c = P₃ SIS)."
* `abbrev U4 := Idx4 → ℚ` — "Order-4 state vector."
* `abbrev U3 := Idx3 → ℚ` — "Order-3 state vector."

## (c) Operations under test (opaque signatures)

| name | signature | docstring |
|---|---|---|
| `standardEbcmValid` | `NetworkType → TransitionType → InitCondType → Prop` | The **standard** EBCM (4 ODE variables) is valid iff: configuration model + Markovian + uniform initials. |
| `ebcmExists` | `NetworkType → TransitionType → InitCondType → Prop` | An EBCM variant exists (as ODE or PDE) for any network type and any transition type, provided initials are uniform. |
| `systemRequired` | `TransitionType → InitCondType → SystemType` | What type of system is needed? |
| `extensionDim` | `NetworkType → TransitionType → ℕ` | The ODE state-space dimension for each network × transition combination. Returns 0 for PDE systems (infinite-dimensional). |
| `MarginalisationObstruction.M_witness` | `U4 → U3` | The marginalisation `M : U4 → U3`, here `M(u)(c) = u(a) + u(b)`. |
| `MarginalisationObstruction.F4_Kirkwood` | `U4 → U4` | The Kirkwood-closed order-4 RHS at the witness configuration. The bilinear `(a·b, b)` form is the characteristic shape of a pair-Kirkwood closure applied to a 5-vertex moment that decomposes as a product of a "pair" entry (`a`) and a "single" entry (`b`). |
| `MarginalisationObstruction.F3_Kirkwood` | `U3 → U3` | The Kirkwood-closed order-3 RHS at the witness configuration. The quadratic-rational `c²/4` form is the analogous order-3 Kirkwood closure applied to the collapsed variable. |

"The standard EBCM" = the configuration-model / Markovian / uniform case; "an EBCM
variant exists" = `ebcmExists …`; "ODE / PDE / impossible" = values of `systemRequired`;
"number of (ODE) variables" = `extensionDim`.

Related theorem-free vocabulary from other modules (for header claims that cite T1):
`EBCMCategory.Marginalisation.IsFlow`, `ContinuousLinearMap` — see `DataTypes/Docs.md`.

## (d) Mathlib notions

* `Ne`, `¬`, `∀`/`∃` over the finite enums, `Nat` arithmetic (`3 * x - 1` is truncated
  subtraction on ℕ).
* Function equality on `Idx3 → ℚ` (`funext`, `congrFun`), `ℚ` arithmetic.
* For "cannot hold along trajectories": `HasDerivAt`, flows `V → ℝ → V`.
