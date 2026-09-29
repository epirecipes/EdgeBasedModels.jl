# DataTypes — group `InvariantRegion`

Blind-safe vocabulary for shadow authors: imports, data types (fields + docstrings) and
**opaque signatures plus docstrings** of the definitions the claims mention. No theorem
statements, proofs, definition bodies or instance bodies. Claim texts:
`Alignment/claims_blind.yaml`.

## (a) Imports and namespaces

```lean
import EBCMCategory.InvariantRegion   -- imports EBCMCategory.EpiCategory, Mathlib.Tactic
open scoped BigOperators
```

* Declarations live in `namespace InvariantRegion`.
* All state variables and parameters are **rationals** (`ℚ`).

## (b) Structures

```lean
/-- A probability generating function (PGF) for a degree distribution with
    at most `n` possible degrees.  The coefficients `pᵢ` satisfy:
    - pᵢ ≥ 0   (probabilities are nonneg)
    - Σ pᵢ = 1  (they sum to 1)

    The PGF is evaluated as ψ(x) = Σᵢ pᵢ xⁱ. -/
structure PolyPGF (n : ℕ) where
  coeffs : Fin n → ℚ
  nonneg : ∀ i, 0 ≤ coeffs i
  sum_one : ∑ i : Fin n, coeffs i = 1
```

```lean
/-- SIR transmission and recovery rates. -/
structure EBCMParams where
  β : ℚ
  γ : ℚ
  β_pos : 0 < β
  γ_pos : 0 < γ
```

```lean
/-- The invariant region for the single-type SIR EBCM. -/
structure EBCMRegion where
  θ   : ℚ
  φ_I : ℚ
  φ_R : ℚ
  R   : ℚ
  hθ_lo : 0 ≤ θ
  hθ_hi : θ ≤ 1
  hφ_I  : 0 ≤ φ_I
  hφ_R  : 0 ≤ φ_R
  hR    : 0 ≤ R
```

## (c) Operations under test (opaque signatures + docstrings)

| signature | docstring |
|---|---|
| `PolyPGF.eval {n : ℕ} (ψ : PolyPGF n) (x : ℚ) : ℚ` | Evaluate ψ at x. |

That is the only definition. In particular the module has **no** Lean definition of:

* the EBCM vector field (dθ/dt, dφ_I/dt, dφ_R/dt, dR/dt), of ψ′ (the derivative of a
  `PolyPGF`), of the observables S = ψ(θ) and I = 1 − S − R, or of the seed factor ρ;
* ODE solutions, trajectories, or (positive/forward) invariance of a region.

Claims about these must be stated with explicit expressions built from `PolyPGF.eval`,
`EBCMParams` fields and free variables, or from Mathlib primitives (see (d)). The vector field
is described only in prose, by the module header (claim `InvariantRegion.header.model` in
claims_blind.yaml).

## (d) Mathlib notions a faithful formalisation may need

* Polynomials: `Polynomial ℚ`/`Polynomial ℝ`, `Polynomial.eval`, `Polynomial.derivative`
  (for ψ′), or `∑ i : Fin n, …` sums with `(i : ℕ)` exponents matching `PolyPGF.eval`.
* Calculus / ODE (over `ℝ`; cast rationals with `(q : ℝ)`): `HasDerivAt`, `HasDerivWithinAt`,
  `deriv`, `Set.Ici 0`, `MonotoneOn`, `AntitoneOn` (and the mean-value consequences
  `monotoneOn_of_deriv_nonneg`, `antitoneOn_of_deriv_nonpos`); solutions as `x : ℝ → ℝ` with
  `∀ t ≥ 0, HasDerivAt x (f (x t)) t`.
* Positive invariance: `∀ t ≥ 0, sol t ∈ K` for a set `K` (e.g. `Set.Icc 0 1`), given
  `sol 0 ∈ K`. Nagumo's theorem is not in Mathlib.
* Limits (θ → 0⁺): `Filter.Tendsto`, `nhdsWithin 0 (Set.Ioi 0)`, `ContinuousWithinAt`.
