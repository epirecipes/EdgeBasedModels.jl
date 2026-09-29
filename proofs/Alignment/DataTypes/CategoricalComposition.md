# DataTypes — group `CategoricalComposition`

Blind-safe vocabulary for shadow authors: imports, data types (fields + docstrings) and
**opaque signatures plus docstrings** of the definitions the claims mention. No statements of
theorems or axioms, and no proofs, definition bodies or instance bodies. Claim texts:
`Alignment/claims_blind.yaml`.

## (a) Imports and namespaces

```lean
import EBCMCategory.CategoricalComposition   -- imports EBCMCategory.EpiCategory, Mathlib.Tactic
```

* Every declaration below is in the **root namespace** (module body: `noncomputable section`,
  `open Real`).
* The module does **not** import any `Mathlib.CategoryTheory` file and defines no category,
  functor, natural transformation, limit/colimit or monoidal structure. A shadow that needs
  such notions must import them itself (see (d)).
* Numbers are `ℝ` except where stated (`ℕ` for dimensions; a few claims about clustering are
  phrased over `ℚ` in the text's own terms).

## (b) Structures

```lean
/-- An EBCM layer: a (Graph, Disease) pair with its derived quantities. -/
structure EBCMLayer where
  mean : ℝ               -- ψ'(1) = ⟨k⟩
  secondFactorial : ℝ    -- ψ''(1) = ⟨k(k-1)⟩
  T : ℝ                  -- edge transmissibility
  dim : ℕ                -- ODE dimension
  mean_pos : 0 < mean
  sf_nonneg : 0 ≤ secondFactorial
  T_pos : 0 < T
  T_le_one : T ≤ 1

/-- Data for a multiplex product of two EBCM layers. -/
structure MultiplexProduct where
  layer1 : EBCMLayer
  layer2 : EBCMLayer

/-- Data for a 2-type stratified model with mixing matrix. -/
structure StratifiedData where
  layer1 : EBCMLayer     -- type 1 EBCM
  layer2 : EBCMLayer     -- type 2 EBCM
  p1 : ℝ                 -- proportion of type 1
  p2 : ℝ                 -- proportion of type 2
  m11 : ℝ                -- mixing M₁₁
  m12 : ℝ                -- mixing M₁₂
  m21 : ℝ                -- mixing M₂₁
  m22 : ℝ                -- mixing M₂₂
  p1_pos : 0 < p1
  p2_pos : 0 < p2
  p_sum : p1 + p2 = 1
  m_nonneg : 0 ≤ m11 ∧ 0 ≤ m12 ∧ 0 ≤ m21 ∧ 0 ≤ m22

/-- Data for the stages natural transformation. -/
structure StagesNatTransData where
  beta : ℝ       -- per-edge transmission rate
  gamma : ℝ      -- recovery rate (base)
  n : ℕ          -- number of Erlang stages
  beta_pos : 0 < beta
  gamma_pos : 0 < gamma
  n_pos : 0 < n

/-- Data for the pullback construction: a mixing matrix parameterized
by assortativity r ∈ [0,1], where r=0 gives neutral (terminal) mixing. -/
structure MixingPullbackData where
  k1 : ℝ               -- degree of type 1
  k2 : ℝ               -- degree of type 2
  p1 : ℝ               -- fraction with degree k1
  p2 : ℝ               -- fraction with degree k2
  r : ℝ                -- assortativity parameter
  k1_pos : 0 < k1
  k2_pos : 0 < k2
  p1_pos : 0 < p1
  p2_pos : 0 < p2
  p_sum : p1 + p2 = 1
  r_nonneg : 0 ≤ r
  r_le_one : r ≤ 1
```

## (c) Operations under test (opaque signatures + docstrings)

| signature | docstring |
|---|---|
| `EBCMLayer.excessDegree (l : EBCMLayer) : ℝ` | Excess degree for a layer: ψ''(1)/ψ'(1). |
| `EBCMLayer.R0 (l : EBCMLayer) : ℝ` | R₀ for a single EBCM layer. |
| `MultiplexProduct.dim (p : MultiplexProduct) : ℕ` | **Result 96b.** The product dimension is the sum of individual dimensions. |
| `MultiplexProduct.R0_sum (p : MultiplexProduct) : ℝ` | **Result 96c.** Product R₀ for independent multiplex layers adds the per-layer contributions, matching the compact implementation in `src/multiplex.jl`. |
| `compactMultiplexDim (nLayers : ℕ) : ℕ` | The compact two-layer multiplex implementation has one θ-equation per layer plus one shared recovery equation. |
| `StratifiedData.S_total (S1 S2 : ℝ) (d : StratifiedData) : ℝ` | **Result 97a.** Overall susceptible fraction is the population-weighted sum: S(t) = p₁·S₁(t) + p₂·S₂(t). This is the defining property of the coproduct injection. |
| `StagesNatTransData.T_exp (d : StagesNatTransData) : ℝ` | Transmissibility for the exponential model: T_exp = β/(β+γ). |
| `StagesNatTransData.T_erlang (d : StagesNatTransData) : ℝ` | Transmissibility for the n-stage Erlang model: T_n = 1 - (nγ/(β+nγ))^n. |
| `MixingPullbackData.meanDeg (d : MixingPullbackData) : ℝ` | Mean degree. |
| `MixingPullbackData.q1 (d : MixingPullbackData) : ℝ` | Excess degree probabilities. |
| `MixingPullbackData.q2 (d : MixingPullbackData) : ℝ` | (no docstring; companion of `q1` for type 2) |

Usage notes:

* `StratifiedData.S_total` takes the two layer susceptible fractions **before** the data
  record; with dot notation write `d.S_total S1 S2`.
* There is **no** Lean definition of: a PGF as a function, θ(t), S(t) of a layer, the
  multiplex or clustered ODE systems, a clustering coefficient, a clustered R₀, a mixing
  matrix `C`/`Q` (entries are not packaged as a `Matrix`), eigenvalues, Erlang distributions
  or expectations. Claims involving these must be stated from Mathlib primitives.

## (d) Mathlib notions a faithful formalisation may need

* Category theory: `CategoryTheory.Category`, `CategoryTheory.Functor` (`map_id`, `map_comp`),
  `CategoryTheory.NatTrans` (naturality squares), `CategoryTheory.Functor.const`,
  `CategoryTheory.Limits.IsTerminal`, `CategoryTheory.Limits.prod`/`coprod`,
  `CategoryTheory.Limits.pullback`, `CategoryTheory.MonoidalCategory` (`pentagon`, `triangle`),
  and `Preorder`-as-category (`CategoryTheory.Preorder`/thin categories).
* Linear algebra: `Matrix (Fin 2) (Fin 2) ℝ`, `Matrix.det`, `Matrix.rank`,
  `Module.End.HasEigenvalue`, `spectralRadius`, `Matrix.toLin'`.
* Probability: `ProbabilityTheory.gammaMeasure`/`gammaPDFReal` (Erlang = gamma with integer
  shape), `MeasureTheory.integral` for expectations, `ProbabilityTheory.expMeasure`.
* PGFs/ODEs as functions: `ψ : ℝ → ℝ`, `deriv`, `HasDerivAt`; final-size fixed points via
  `Function.IsFixedPt`.
* Order/field facts on `ℝ` and `ℕ`.
