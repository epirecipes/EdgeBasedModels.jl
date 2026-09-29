# DataTypes — ClosureTheorem

Blind-safe vocabulary for shadow authors of group `ClosureTheorem` (SA-PASS). This file lists the Lean
imports, the shared data types (structures/inductives with their fields) and the operations under
test as **opaque signatures with their docstrings only**. It deliberately contains no theorem
statements, no proofs, no definition bodies and no instance bodies. Where a docstring spells out a
formula, that formula is the author's *intent text*, not a guarantee about the body.

Number types: all quantities are rationals (`ℚ`); `n`, `m` are natural numbers cast to `ℚ`.

## (a) Imports

```lean
import EBCMCategory.ClosureTheorem
import Mathlib.Tactic
-- ClosureTheorem imports EBCMCategory.EpiCategory and EBCMCategory.SurvivalBridge
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

### `PGFEval`

```lean
structure PGFEval where
  ψ : ℚ
  ψ' : ℚ
  ψ'' : ℚ
  ψ_pos : 0 < ψ
  ψ'_pos : 0 < ψ'
```
Docstring: "A PGF evaluated at a point theta, carrying its first two derivatives." Constructed with
`PGFEval.mk ψ ψ' ψ'' hψ hψ'` or `⟨ψ, ψ', ψ'', hψ, hψ'⟩`. Nothing in the structure ties `ψ'`/`ψ''` to
derivatives of an actual function.

## (c) Operations under test (opaque signatures + docstrings)

* `PGFData.excessDegree : PGFData → ℚ` — "The excess degree ratio: ψ''(1)/ψ'(1)."
* `PGFData.variance : PGFData → ℚ` — "Degree variance: Var(k) = ψ''(1) + ψ'(1) - (ψ'(1))²."
* `PGFData.dispersionIndex : PGFData → ℚ` — "Index of dispersion: σ²/κ. Equals 1 iff Poisson."
* `PGFData.poisson : (κ : ℚ) → 0 < κ → PGFData` — "The Poisson PGF with mean κ. Key property: ψ''(1) = κ²."

* `PGFData.closureKappa : PGFData → ℚ` (from SurvivalBridge) — "The closure parameter κ for a PGF.
  κ = ψ''(1)·ψ(1) / (ψ'(1))² = secondFactorial / mean² (since ψ(1) = 1 for any proper PGF).
  This is the ratio of mean excess degree to mean degree. It is constant in θ iff the degree
  distribution is Poisson-type."
* `PGFEval.closureRatio : PGFEval → ℚ` — "The closure ratio kappa(theta) = psi'' psi / psi'^2."

Family PGFs referred to by the text (standard parametrisations, for shadow authors' convenience):
Poisson(λ): ψ(θ) = e^{λ(θ−1)}; Binomial(n, p): ψ(θ) = (1 − p + pθ)^n;
NegBin(r, c): ψ(θ) = (c / (1 − (1 − c)θ))^r; mixture ψ(θ) = 1/2 + θ²/2.

## (d) Mathlib notions a faithful formalisation may need

* Arithmetic over `ℚ` (field operations, `^`, `<`, `≤`, `≠`), `Nat.cast`.
* PGFs as functions: `ψ : ℝ → ℝ` (or `ℚ → ℚ`), e.g. `ψ u = ∑' k, p k * u ^ k` (`tsum`) or a finite
  `Finset.sum`; `PMF ℕ`, `PMF.binomial`, `ProbabilityTheory.poissonPMF`/`poissonPMFReal`,
  `ProbabilityTheory.geometricPMFReal`.
* Derivatives: `deriv`, `iteratedDeriv 2`, `HasDerivAt`, `HasDerivWithinAt`, `DifferentiableAt`.
* `Real.exp`, `Real.log`, `Real.sqrt`.
* ODE trajectories: a function `x : ℝ → State` with `∀ t, HasDerivAt x (F (x t)) t`; `Monotone`, `Antitone`.
* Limits: `Filter.Tendsto`, `Filter.atTop`, `nhds`.

* `lt_trichotomy`-style disjunctions `a < b ∨ a = b ∨ b < a` are logical glue.
