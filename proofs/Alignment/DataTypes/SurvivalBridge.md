# DataTypes — SurvivalBridge

Blind-safe vocabulary for shadow authors of group `SurvivalBridge` (SA-PASS). This file lists the Lean
imports, the shared data types (structures/inductives with their fields) and the operations under
test as **opaque signatures with their docstrings only**. It deliberately contains no theorem
statements, no proofs, no definition bodies and no instance bodies. Where a docstring spells out a
formula, that formula is the author's *intent text*, not a guarantee about the body.

Number types: all quantities are rationals (`ℚ`).

## (a) Imports

```lean
import EBCMCategory.SurvivalBridge
import Mathlib.Tactic
-- SurvivalBridge imports EBCMCategory.EpiCategory; some claims also refer to
-- EBCMCategory.ClosureTheorem (see DataTypes/ClosureTheorem.md): import EBCMCategory.ClosureTheorem
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

### `PTType`

```lean
inductive PTType where
  | poisson       -- κ = 1
  | binomial      -- κ = (n-1)/n < 1 for integer n ≥ 1
  | negBinomial   -- κ = (r+1)/r > 1 for real r > 0
  deriving DecidableEq, Repr
```
Docstring: "Classification of Poisson-type distributions." (Not referenced by any operation.)

### `VolzState`, `DSAState`

```lean
structure VolzState where
  θ : ℚ
  p_I : ℚ
  p_S : ℚ

structure DSAState where
  x_θ : ℚ
  x_SI : ℚ
  x_SS : ℚ
```
Docstring of `VolzState`: "The Volz model uses edge-probability variables (θ, p_I, p_S). The DSA
model uses survival-analysis variables (x_θ, x_{SI}, x_{SS}). They are related by:
x_{SI} = p_I · ψ'(θ), x_{SS} = p_S · ψ'(θ). This is invertible whenever ψ'(θ) > 0 (mean degree > 0)."
`DSAState` has no docstring.

## (c) Operations under test (opaque signatures + docstrings)

* `PGFData.excessDegree : PGFData → ℚ` — "The excess degree ratio: ψ''(1)/ψ'(1)."
* `PGFData.variance : PGFData → ℚ` — "Degree variance: Var(k) = ψ''(1) + ψ'(1) - (ψ'(1))²."
* `PGFData.dispersionIndex : PGFData → ℚ` — "Index of dispersion: σ²/κ. Equals 1 iff Poisson."
* `PGFData.poisson : (κ : ℚ) → 0 < κ → PGFData` — "The Poisson PGF with mean κ. Key property: ψ''(1) = κ²."
* `SIRParams.transmissibility : SIRParams → ℚ` — "Transmissibility across a single edge: T = β/(β+γ)."
* `nodeModel : SIRParams → ℚ → EpiModel` — "A node-based SIR model: 3 state variables (S, I, R)."
  (second argument: the mean degree κ)
* `edgeModel : SIRParams → PGFData → EpiModel` — "An edge-based SIR model: 4 state variables (θ, φ_I, R + algebraic φ_S)."

* `PGFData.closureKappa : PGFData → ℚ` — "The closure parameter κ for a PGF.
  κ = ψ''(1)·ψ(1) / (ψ'(1))² = secondFactorial / mean² (since ψ(1) = 1 for any proper PGF).
  This is the ratio of mean excess degree to mean degree. It is constant in θ iff the degree
  distribution is Poisson-type."
* `dsaToVolz : DSAState → (psi_prime : ℚ) → psi_prime ≠ 0 → VolzState` — "The variable change DSA → Volz: divide by ψ'(θ)."
* `volzToDSA : VolzState → ℚ → DSAState` — "The variable change Volz → DSA: multiply by ψ'(θ)."
  (the ℚ argument is the value ψ'(θ); it is not computed from the state)

## (d) Mathlib notions a faithful formalisation may need

* Arithmetic over `ℚ` (field operations, `^`, `<`, `≤`, `≠`), `Nat.cast`.
* PGFs as functions: `ψ : ℝ → ℝ` (or `ℚ → ℚ`), e.g. `ψ u = ∑' k, p k * u ^ k` (`tsum`) or a finite
  `Finset.sum`; `PMF ℕ`, `PMF.binomial`, `ProbabilityTheory.poissonPMF`/`poissonPMFReal`,
  `ProbabilityTheory.geometricPMFReal`.
* Derivatives: `deriv`, `iteratedDeriv 2`, `HasDerivAt`, `HasDerivWithinAt`, `DifferentiableAt`.
* `Real.exp`, `Real.log`, `Real.sqrt`.
* ODE trajectories: a function `x : ℝ → State` with `∀ t, HasDerivAt x (F (x t)) t`; `Monotone`, `Antitone`.
* Limits: `Filter.Tendsto`, `Filter.atTop`, `nhds`.

* `Function.LeftInverse`, `Function.RightInverse`, `Function.Bijective`, `Equiv` for "invertible"/"isomorphism".
* Category theory (if a claim needs it): `CategoryTheory.Category`, `CategoryTheory.Functor`,
  `CategoryTheory.NatTrans`, `CategoryTheory.NatIso`, `CategoryTheory.Limits.IsColimit`. The library
  defines no category of networks or of ODE systems.

## Notes for shadow authors

* Several claims mention a PGF evaluated away from u = 1, derivatives, ODE flows or survival
  equations. None of these exist as operations; write the intended statement with Mathlib notions
  (functions `ψ : ℝ → ℝ`, `deriv`, trajectories) or over the opaque operations above, whichever the
  text requires.
