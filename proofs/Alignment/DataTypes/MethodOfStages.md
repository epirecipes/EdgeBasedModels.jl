# DataTypes — MethodOfStages

Blind-safe vocabulary for shadow authors of group `MethodOfStages` (SA-PASS). This file lists the Lean
imports, the shared data types (structures/inductives with their fields) and the operations under
test as **opaque signatures with their docstrings only**. It deliberately contains no theorem
statements, no proofs, no definition bodies and no instance bodies. Where a docstring spells out a
formula, that formula is the author's *intent text*, not a guarantee about the body.

Number types: all quantities are reals (`ℝ`); `n` is a natural number cast to `ℝ`. The module is `noncomputable` and opens `Real`.

## (a) Imports

```lean
import EBCMCategory.MethodOfStages
import Mathlib
```

## (b) Shared data types

Module context (header text): "Formalizes the Erlang sub-stage technique for replacing exponential
sojourn times with gamma-distributed ones. An Erlang(n, nγ) distribution is implemented as n
sequential sub-stages each with rate nγ."

### `ErlangParams`

```lean
structure ErlangParams where
  n : ℕ           -- number of sub-stages
  gamma : ℝ       -- overall rate
  n_pos : 0 < n
  gamma_pos : 0 < gamma
```
(no docstring)

## (c) Operations under test (opaque signatures + docstrings)

The module defines **no** operations: every quantity in the claims (Erlang mean, variance, CV,
transmissibility T_n, ODE dimension) appears only as an explicit real expression. There is no
Erlang/exponential distribution object in the library; a faithful formalisation must use Mathlib's
(section d).

## (d) Mathlib notions a faithful formalisation may need

* `ProbabilityTheory.gammaMeasure (a r : ℝ) : Measure ℝ`, `ProbabilityTheory.gammaPDFReal a r x`,
  `ProbabilityTheory.gammaPDF`, `ProbabilityTheory.exponentialPDFReal r x`, `ProbabilityTheory.exponentialPDF`
  (Erlang(n, λ) = Gamma with shape n and rate λ).
* `MeasureTheory.integral` (`∫ x, f x ∂μ`), `ProbabilityTheory.variance`, `MeasureTheory.Measure.dirac`.
* Weak convergence: `MeasureTheory.ProbabilityMeasure` with its topology and `Filter.Tendsto`.
* `Filter.Tendsto`, `Filter.atTop`, `nhds`, `Real.exp`, `Real.sqrt`, `Monotone`/`Antitone`/`StrictAnti`.
* `List.sum`, `List.map` (for stage counts).
