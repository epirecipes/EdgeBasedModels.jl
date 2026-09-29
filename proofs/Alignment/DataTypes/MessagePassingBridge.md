# DataTypes — MessagePassingBridge

Blind-safe vocabulary for shadow authors of group `MessagePassingBridge` (SA-PASS). This file lists the Lean
imports, the shared data types (structures/inductives with their fields) and the operations under
test as **opaque signatures with their docstrings only**. It deliberately contains no theorem
statements, no proofs, no definition bodies and no instance bodies. Where a docstring spells out a
formula, that formula is the author's *intent text*, not a guarantee about the body.

Number types: all quantities are rationals (`ℚ`); dimensions are natural numbers.

## (a) Imports

```lean
import EBCMCategory.MessagePassingBridge
import Mathlib.Tactic
-- MessagePassingBridge imports EBCMCategory.EpiCategory, EBCMCategory.CoarseGrain,
-- EBCMCategory.SurvivalBridge (VolzState/volzToDSA etc.: see DataTypes/SurvivalBridge.md)
```

## (b) Shared data types

### `PGFData` (from `EBCMCategory.EpiCategory`)

```lean
structure PGFData where
  mean : ℚ
  secondFactorial : ℚ
  mean_pos : 0 < mean
  secondFactorial_nonneg : 0 ≤ secondFactorial
```
Docstring: "Abstract probability generating function data. A PGF ψ of a degree distribution is
characterised by: `mean` = ψ'(1): the mean degree κ; `secondFactorial` = ψ''(1): the second
factorial moment; `mean_pos`: the mean degree is positive."

Note: a `PGFData` is only a pair of numbers; it does not contain the PGF ψ as a function, so
statements about ψ(u) for u ≠ 1 cannot be expressed through it.

### `SIRParams` (from `EBCMCategory.EpiCategory`)

```lean
structure SIRParams where
  β : ℚ   -- transmission rate
  γ : ℚ   -- recovery rate
  β_pos : 0 < β
  γ_pos : 0 < γ
```
Docstring: "Transmission and recovery parameters for an SIR model."

### `EpiModel` (from `EBCMCategory.EpiCategory`)

```lean
structure EpiModel where
  dim : ℕ
  R0 : ℚ
```
Docstring: "An epidemic model, characterised abstractly by its state-space dimension (a proxy for
information content) and R₀ (a shared observable)." (`EpiModel` also carries `LE`/`Preorder`
instances; their bodies are withheld and not needed for this group.)

### `ModelFamily`

```lean
inductive ModelFamily where
  | messagePassing     -- Karrer & Newman: exact on CM, any τ(a), q(a)
  | ebcmPDE            -- Non-Markovian EBCM: von Foerster PDE
  | ebcmODE            -- Markovian EBCM: Volz's 3-variable ODE
  | dsa                -- Dynamic survival analysis
  | pairwise           -- Pairwise model with moment closure
  | massAction         -- Classical SIR (fully mixed / Poisson network)
  deriving DecidableEq, Repr
```
Docstring: "The six model families in the epidemic-on-network hierarchy. Ordered from most general
(MP) to most specialized (massAction)."

### `Assumption`

```lean
inductive Assumption where
  | configModel        -- Configuration model network
  | markovTransmission -- τ(a) = β·exp(-βa)
  | markovRecovery     -- q(a) = γ·exp(-γa)
  | poissonType        -- Degree distribution is PT (κ = const)
  | poissonDegree      -- Degree distribution is Poisson
  deriving DecidableEq, Repr
```
Docstring: "What assumptions are needed for each model to be exact (in the N → ∞ limit on
configuration model networks)." No implication/ordering relation between assumptions is defined.

### `EpiProcess`

```lean
structure EpiProcess where
  ζ : ℚ      -- transmission hazard
  ρ : ℚ      -- recovery hazard
  ξ_τ : ℚ    -- transmission survival
  ξ_q : ℚ    -- recovery survival
  ζ_pos : 0 < ζ
  ξ_τ_pos : 0 < ξ_τ
  ξ_q_pos : 0 < ξ_q
```
Docstring: "Transmission and recovery processes, abstracted to their algebraic essence at a single
age point a. * ζ = hazard rate for transmission: ζ(a) = τ(a)/ξ_τ(a) * ρ = hazard rate for recovery:
ρ(a) = q(a)/ξ_q(a) * ξ_τ = survival function for transmission: exp(-∫₀ᵃ ζ) * ξ_q = survival function
for recovery: exp(-∫₀ᵃ ρ) * τ = density for transmission: τ(a) = ζ(a)·ξ_τ(a) * f = combined:
τ(a)·ξ_q(a) (prob of transmitting at age a)"

### `MPState`, `EBCMState`

```lean
structure MPState where
  H₁ : ℚ         -- the message
  H₁_pos : 0 < H₁
  H₁_le_one : H₁ ≤ 1

structure EBCMState where
  Θ : ℚ
  Θ_pos : 0 < Θ
  Θ_le_one : Θ ≤ 1
```
Docstring of `MPState`: "The MP model state: the message H₁(t). H₁(t) = probability a neighbour has
NOT transmitted by time t." Docstring of `EBCMState`: "The EBCM state: the edge probability Θ(t) and
densities. Θ(t) = probability test node has not received transmission from a given neighbour by
time t. On CM networks as N → ∞, Θ(t) = H₁(t)."

## (c) Operations under test (opaque signatures + docstrings)

* `PGFData.excessDegree : PGFData → ℚ` — "The excess degree ratio: ψ''(1)/ψ'(1)."
* `PGFData.variance : PGFData → ℚ` — "Degree variance: Var(k) = ψ''(1) + ψ'(1) - (ψ'(1))²."
* `PGFData.dispersionIndex : PGFData → ℚ` — "Index of dispersion: σ²/κ. Equals 1 iff Poisson."
* `PGFData.poisson : (κ : ℚ) → 0 < κ → PGFData` — "The Poisson PGF with mean κ. Key property: ψ''(1) = κ²."
* `SIRParams.transmissibility : SIRParams → ℚ` — "Transmissibility across a single edge: T = β/(β+γ)."
* `nodeModel : SIRParams → ℚ → EpiModel` — "A node-based SIR model: 3 state variables (S, I, R)."
  (second argument: the mean degree κ)
* `edgeModel : SIRParams → PGFData → EpiModel` — "An edge-based SIR model: 4 state variables (θ, φ_I, R + algebraic φ_S)."

* `ModelFamily.requiredAssumptions : ModelFamily → List Assumption` — "The assumptions required for each model to be exact."
* `ModelFamily.effectiveDim : ModelFamily → ℕ` — "Effective dimension of each model family.
  * MP: one integro-differential equation per edge direction (∞ on CM) * EBCM PDE: von Foerster PDE
  (∞-dim function space) * EBCM ODE: 3 core + 2 output = 5 * DSA: 3 core + 2 output = 5 * Pairwise: 4
  variables ([S], [I], [SI], [SS]) + closure * Mass-action: 2 variables (S, I)"
* `EpiProcess.f_mp : EpiProcess → ℚ` — "The MP transmission kernel: f(a) = τ(a)·ξ_q(a) = ζ·ξ_τ·ξ_q"
* `EpiProcess.f_ebcm : EpiProcess → ℚ` — "The EBCM transmission kernel: f̂(a) = ζ(a)·exp(-∫(ζ+ρ))
  Since exp(-∫ζ) = ξ_τ and exp(-∫ρ) = ξ_q, we have f̂(a) = ζ·ξ_τ·ξ_q"
* `mpToEBCM : MPState → EBCMState` — "The bridge map: MP → EBCM via H₁ ↦ Θ."
* `ebcmToMP : EBCMState → MPState` — "The bridge map: EBCM → MP via Θ ↦ H₁."

## (d) Mathlib notions a faithful formalisation may need

* Arithmetic over `ℚ` (field operations, `^`, `<`, `≤`, `≠`), `Nat.cast`.
* PGFs as functions: `ψ : ℝ → ℝ` (or `ℚ → ℚ`), e.g. `ψ u = ∑' k, p k * u ^ k` (`tsum`) or a finite
  `Finset.sum`; `PMF ℕ`, `PMF.binomial`, `ProbabilityTheory.poissonPMF`/`poissonPMFReal`,
  `ProbabilityTheory.geometricPMFReal`.
* Derivatives: `deriv`, `iteratedDeriv 2`, `HasDerivAt`, `HasDerivWithinAt`, `DifferentiableAt`.
* `Real.exp`, `Real.log`, `Real.sqrt`.
* ODE trajectories: a function `x : ℝ → State` with `∀ t, HasDerivAt x (F (x t)) t`; `Monotone`, `Antitone`.
* Limits: `Filter.Tendsto`, `Filter.atTop`, `nhds`.

* `List.length`, `List.Subset` / `∈` on lists, `Finset` inclusion (for "requires at least as many
  assumptions" / "implies all weaker assumptions").
* `MeasureTheory.integral` over `Set.Ioi 0` (`∫ a in Set.Ioi 0, f a`) for ∫₀^∞ f(a) da.
* `Function.LeftInverse`, `Function.RightInverse`, `Equiv`.

## Notes for shadow authors

* The library has no MP/EBCM/DSA/pairwise/mass-action dynamics; claims about trajectories must be
  stated with Mathlib notions (functions of time, `HasDerivAt`) if they are to be stated at all.
