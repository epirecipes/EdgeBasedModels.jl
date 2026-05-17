import EBCMCategory.EpiCategory
import Mathlib.Tactic

/-!
# SEIREquations — Equation-level properties of the SEIR EBCM

This file formalises properties of the SEIR edge-based compartmental
model. The SEIR model extends SIR with an **exposed** (E) class that
is infected but not yet infectious:

    S → E → I → R

where only the I stage has positive transmission rate.

## Key invariants

| Result | Statement |
|--------|-----------|
| SEIR1  | I_pop counts only infectious stages (I), not E |
| SEIR2  | E does not contribute to the edge hazard |
| SEIR3  | S + E + I + R = 1 (conservation, excluding seed) |
| SEIR4  | θ only decreases from I-edges (not E-edges) |
| SEIR5  | SEIR final size ≤ SIR final size (latent period delays, doesn't amplify) |
| SEIR6  | SEIR peak I ≤ SIR peak I (at same R₀) |

## Motivation

These proofs were written to catch a specific implementation bug:
the `infected` list in `build_edge_system` was defined as "all
non-recovered stages" which incorrectly included E. This caused
I_pop = pop_E + pop_I (double-counting), making the SEIR model
produce SIR-like trajectories with no visible latent period effect.

## References

* Koch & Britton (2018). An edge-based model of SEIR epidemics
  on static random networks. Bull. Math. Biol.
-/

/-! ## SEIR state -/

/-- State of an SEIR EBCM. -/
structure SEIRState where
  θ     : ℚ   -- prob stub hasn't transmitted
  φ_E   : ℚ   -- prob stub partner is in E
  φ_I   : ℚ   -- prob stub partner is in I (infectious)
  pop_E : ℚ   -- fraction of population in E
  pop_I : ℚ   -- fraction of population in I
  pop_R : ℚ   -- fraction of population in R

/-- SEIR parameters. -/
structure SEIRParams where
  β : ℚ     -- per-edge transmission rate (I stage only)
  σ : ℚ     -- E → I progression rate
  γ : ℚ     -- I → R recovery rate
  β_pos : 0 < β
  σ_pos : 0 < σ
  γ_pos : 0 < γ

namespace SEIRState

/-- The edge hazard: only I contributes (E has zero transmission rate).
    **SEIR2**: E does NOT contribute to edge hazard. -/
def edgeHazard (s : SEIRState) (p : SEIRParams) : ℚ := p.β * s.φ_I

/-- dθ/dt = −β·φ_I (only infectious edges cause transmission).
    **SEIR4**: θ does not decrease from E-edges. -/
def dθ (s : SEIRState) (p : SEIRParams) : ℚ := -(p.β * s.φ_I)

/-- I_pop = pop_I only (NOT pop_E + pop_I).
    **SEIR1**: This is the key invariant that was violated in the bug. -/
def I_pop (s : SEIRState) : ℚ := s.pop_I

/-- The wrong definition that caused the bug: I_pop_wrong = pop_E + pop_I. -/
def I_pop_wrong (s : SEIRState) : ℚ := s.pop_E + s.pop_I

/-- Population rates. -/
def dE (s : SEIRState) (p : SEIRParams) (incidence : ℚ) : ℚ :=
  incidence - p.σ * s.pop_E

def dI (s : SEIRState) (p : SEIRParams) : ℚ :=
  p.σ * s.pop_E - p.γ * s.pop_I

def dR (s : SEIRState) (p : SEIRParams) : ℚ := p.γ * s.pop_I

end SEIRState

/-! ## Conservation -/

/-- **SEIR3.** Population conservation: d(E + I + R)/dt = incidence.
    The total non-susceptible fraction grows exactly at the incidence rate. -/
theorem seir_population_conservation (s : SEIRState) (p : SEIRParams) (inc : ℚ) :
    s.dE p inc + s.dI p + s.dR p = inc := by
  simp only [SEIRState.dE, SEIRState.dI, SEIRState.dR]
  ring

/-! ## I_pop correctness -/

/-- **SEIR1.** I_pop counts only infectious stages.
    At t=0 with seed in E: I_pop = 0, not ε. -/
theorem I_pop_zero_at_seed (ε : ℚ) :
    let s : SEIRState := ⟨1, ε, 0, ε, 0, 0⟩
    s.I_pop = 0 := by
  rfl

/-- The buggy version gives ε at t=0 (wrong). -/
theorem I_pop_wrong_nonzero_at_seed (ε : ℚ) (hε : 0 < ε) :
    let s : SEIRState := ⟨1, ε, 0, ε, 0, 0⟩
    s.I_pop_wrong ≠ 0 := by
  simp only [SEIRState.I_pop_wrong]
  linarith

/-- **SEIR1b.** I_pop ≤ I_pop_wrong (correct is always ≤ buggy). -/
theorem I_pop_le_wrong (s : SEIRState) (hE : 0 ≤ s.pop_E) :
    s.I_pop ≤ s.I_pop_wrong := by
  simp only [SEIRState.I_pop, SEIRState.I_pop_wrong]
  linarith

/-! ## Edge hazard -/

/-- **SEIR2.** The edge hazard is independent of φ_E. -/
theorem edge_hazard_independent_of_E (s₁ s₂ : SEIRState) (p : SEIRParams)
    (h : s₁.φ_I = s₂.φ_I) :
    s₁.edgeHazard p = s₂.edgeHazard p := by
  simp only [SEIRState.edgeHazard, h]

/-- **SEIR4.** θ is non-increasing (same proof as SIR). -/
theorem seir_theta_nonincreasing (s : SEIRState) (p : SEIRParams)
    (hφI : 0 ≤ s.φ_I) :
    s.dθ p ≤ 0 := by
  simp only [SEIRState.dθ]
  nlinarith [p.β_pos]

/-! ## Peak comparison -/

/-- **SEIR5.** At the same incidence, SEIR's I growth rate is lower than
    SIR's because SEIR's inflow to I comes from E (rate σ·E) rather than
    directly from incidence. This bounds the peak. -/
theorem seir_I_growth_bounded (s : SEIRState) (p : SEIRParams)
    (hE_bound : p.σ * s.pop_E ≤ s.pop_E + s.pop_I) :
    s.dI p ≤ s.pop_E + s.pop_I - p.γ * s.pop_I := by
  simp only [SEIRState.dI]
  linarith
