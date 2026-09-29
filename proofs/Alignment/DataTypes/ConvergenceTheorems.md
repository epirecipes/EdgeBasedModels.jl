# DataTypes — group `ConvergenceTheorems`

Blind-safe vocabulary for shadow authors. It lists imports, data types (with their fields)
and the definitions that the group's claims talk about, as **opaque signatures plus
docstrings**. It contains no theorem statements, proofs, definition bodies or instance bodies.
Claim texts are in `Alignment/claims_blind.yaml` (group `ConvergenceTheorems`).

## (a) Imports and namespaces

```lean
import EBCMCategory.ConvergenceTheorems   -- transitively imports EBCMCategory.EpiCategory, Mathlib.Tactic
```

* Every declaration below is in the **root namespace**. The module body is a
  `noncomputable section` with `open Real`.
* All quantities are real numbers (`ℝ`). No probability generating function is represented
  as a function: degree distributions appear only through the moment record `PGFMoments`.

## (b) Structures and classes

(The classes `TreeNetwork`, `PairClosureError` and the structure `FinalSizeCLTData` were deleted
with the axioms that used them; the tree-exactness and CLT results are cited, not formalised.)

```lean
/-- Data for the Poisson-network EBCM: Poisson(κ) degree distribution
with per-edge transmission rate β̃ and recovery rate γ̃. -/
structure PoissonEBCMData where
  kappa : ℝ          -- Poisson mean degree
  beta_tilde : ℝ     -- per-edge transmission rate
  gamma_tilde : ℝ    -- recovery rate
  kappa_pos : 0 < kappa
  beta_tilde_pos : 0 < beta_tilde
  gamma_tilde_pos : 0 < gamma_tilde
```

```lean
/-- PGF moment data over ℝ with mean, second factorial moment, and variance. -/
structure PGFMoments where
  mean : ℝ                -- ⟨k⟩ = ψ'(1)
  secondFactorial : ℝ     -- ⟨k(k-1)⟩ = ψ''(1)
  variance : ℝ            -- Var(k)
  mean_pos : 0 < mean
  secondFactorial_nonneg : 0 ≤ secondFactorial
  variance_nonneg : 0 ≤ variance
  /-- The consistency relation: ⟨k²⟩ = ⟨k(k-1)⟩ + ⟨k⟩ and Var = ⟨k²⟩ - ⟨k⟩²,
  so Var = ⟨k(k-1)⟩ + ⟨k⟩ - ⟨k⟩². -/
  variance_eq : variance = secondFactorial + mean - mean ^ 2
```

## (c) Operations under test (opaque signatures + docstrings)

| signature | docstring |
|---|---|
| `effective_beta (d : PoissonEBCMData) : ℝ` | **Result 105a.** Effective mass-action transmission rate: β = κ β̃. |
| `effective_gamma (d : PoissonEBCMData) : ℝ` | **Result 105b.** Effective mass-action recovery rate: γ = γ̃ + β̃. |
| `PGFMoments.excessDegree (m : PGFMoments) : ℝ` | The excess degree ratio ψ''(1)/ψ'(1). |
| `PGFMoments.secondMoment (m : PGFMoments) : ℝ` | Second moment ⟨k²⟩ = ⟨k(k-1)⟩ + ⟨k⟩. |
| `R0_heterogeneous (T : ℝ) (m : PGFMoments) : ℝ` | R₀ for a heterogeneous network with transmissibility T. |
| `R0_homogeneous (T : ℝ) (k : ℝ) : ℝ` | R₀ for a homogeneous (regular) network where every node has degree k. |
| `poissonMoments (kappa : ℝ) (hk : 0 < kappa) : PGFMoments` | Poisson PGF moments over ℝ. |
| `finalSizeMap (T : ℝ) (g_at_theta : ℝ) : ℝ` | The final-size fixed-point function: f(θ) = 1 - T + T · g(θ) where g(θ) = ψ'(θ)/ψ'(1). At θ=1, g(1) = 1 (normalization). |
| `criticalTransmissibility (m : PGFMoments) (_hsf : 0 < m.secondFactorial) : ℝ` | The critical transmissibility: T_c = ψ'(1)/ψ''(1) = 1/excessDegree. |

Notes on the signatures:

* `finalSizeMap` takes the **value** `g(θ)` as its second argument (a real number), not a
  function `g`.
* `criticalTransmissibility` takes a proof of `0 < m.secondFactorial` as an explicit argument.
* There is **no** Lean definition of the Poisson EBCM ODE, of `S`, `I`, θ(t), of a pair
  closure, of a tree network, or of the random final size `Z_n`. Claims about those must be
  stated from Mathlib primitives (see (d)).

## (d) Mathlib notions a faithful formalisation may need

* Calculus: `Real.exp`, `deriv`, `iteratedDeriv`, `HasDerivAt` (and `HasDerivAt.exp`,
  `HasDerivAt.comp`, `HasDerivAt.const_mul` for the chain rule), `derivWithin`.
* PGFs as functions: `ψ : ℝ → ℝ`, e.g. `fun x => Real.exp (κ * (x - 1))`; series
  `∑' k, p k * x ^ k` (`tsum`) or finite `Finset.sum` for a degree distribution `p : ℕ → ℝ`.
* ODE trajectories: functions `ℝ → ℝ` with `∀ t, HasDerivAt θ (f (θ t)) t`.
* Fixed points / stability: `Function.IsFixedPt`, `|·|` (`abs`), `Filter.Tendsto` of iterates
  `f^[n]`.
* Limits and probability (Results 106, 111): `Filter.Tendsto`, `Filter.atTop`,
  `MeasureTheory.Measure`, `ProbabilityTheory` (a.s. statements via `∀ᵐ ω ∂P, …`),
  `ProbabilityTheory.gaussianReal` for N(0, σ²); convergence in distribution may need a
  hand-written predicate on laws (`MeasureTheory.Measure.map`) if no library notion fits.
* Orders/fields on `ℝ`: `div`, `inv`, `≤`, `<`, `↔`.
