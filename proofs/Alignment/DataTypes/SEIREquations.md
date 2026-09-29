# DataTypes — SEIREquations

Blind-safe vocabulary for shadow authors of group `SEIREquations` (SA-PASS). This file lists the Lean
imports, the shared data types (structures/inductives with their fields) and the operations under
test as **opaque signatures with their docstrings only**. It deliberately contains no theorem
statements, no proofs, no definition bodies and no instance bodies. Where a docstring spells out a
formula, that formula is the author's *intent text*, not a guarantee about the body.

Number types: all quantities are rationals (`ℚ`).

## (a) Imports

```lean
import EBCMCategory.SEIREquations
import Mathlib.Tactic
```

## (b) Shared data types

### `SEIRState`

```lean
structure SEIRState where
  θ     : ℚ   -- prob stub hasn't transmitted
  φ_E   : ℚ   -- prob stub partner is in E
  φ_I   : ℚ   -- prob stub partner is in I (infectious)
  pop_E : ℚ   -- fraction of population in E
  pop_I : ℚ   -- fraction of population in I
  pop_R : ℚ   -- fraction of population in R
```
Docstring: "State of an SEIR EBCM." Anonymous-constructor order is `⟨θ, φ_E, φ_I, pop_E, pop_I, pop_R⟩`.
There is no susceptible-fraction field and no sign/range constraints on the fields.

### `SEIRParams`

```lean
structure SEIRParams where
  β : ℚ     -- per-edge transmission rate (I stage only)
  σ : ℚ     -- E → I progression rate
  γ : ℚ     -- I → R recovery rate
  β_pos : 0 < β
  σ_pos : 0 < σ
  γ_pos : 0 < γ
```
Docstring: "SEIR parameters."

Module context (header text): the SEIR model is S → E → I → R "where only the I stage has positive
transmission rate".

## (c) Operations under test (opaque signatures + docstrings)

* `SEIRState.edgeHazard : SEIRState → SEIRParams → ℚ` — "The edge hazard: only I contributes (E has
  zero transmission rate). **SEIR2**: E does NOT contribute to edge hazard."
* `SEIRState.dθ : SEIRState → SEIRParams → ℚ` — "dθ/dt = −β·φ_I (only infectious edges cause
  transmission). **SEIR4**: θ does not decrease from E-edges."
* `SEIRState.I_pop : SEIRState → ℚ` — "I_pop = pop_I only (NOT pop_E + pop_I). **SEIR1**: This is the
  key invariant that was violated in the bug."
* `SEIRState.I_pop_wrong : SEIRState → ℚ` — "The wrong definition that caused the bug: I_pop_wrong = pop_E + pop_I."
* `SEIRState.dE : SEIRState → SEIRParams → ℚ → ℚ` — "Population rates." (third argument: the incidence)
* `SEIRState.dI : SEIRState → SEIRParams → ℚ` — (no docstring; rate of change of pop_I)
* `SEIRState.dR : SEIRState → SEIRParams → ℚ` — (no docstring; rate of change of pop_R)

These are rate *functions* of a state; the module defines no trajectories, no susceptible fraction
S, no final size and no peak.

## (d) Mathlib notions a faithful formalisation may need

* Arithmetic over `ℚ` (field operations, `^`, `<`, `≤`, `≠`), `Nat.cast`.

* To speak about time evolution, peaks or final sizes one would need trajectories
  `x : ℝ → SEIRState`-like functions with `HasDerivAt`, `Filter.Tendsto … Filter.atTop`, `sSup`/`iSup`
  for a peak, and a comparison SIR system (none exist in the library).
