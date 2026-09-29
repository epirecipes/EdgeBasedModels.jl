import Alignment.Registry
import EBCMCategory.SEIREquations

/-!
# Blind shadow sets for group `SEIREquations`

Written blind: from the claim texts in `Alignment/claims_blind.yaml`, the vocabulary in
`Alignment/DataTypes/SEIREquations.md`, `Alignment/README.md` and `Example/ExampleShadows.lean`
only. No trusted theorem statements or definition bodies were consulted.

Vocabulary used (opaque, from DataTypes):
* `SEIRState` with fields `θ φ_E φ_I pop_E pop_I pop_R : ℚ` (constructor order as listed; no
  susceptible field, no sign constraints);
* `SEIRParams` with `β σ γ : ℚ` (β: per-edge transmission rate of the I stage, σ: E → I
  progression rate, γ: I → R recovery rate);
* rate functions of a state: `SEIRState.edgeHazard`, `SEIRState.dθ` (= dθ/dt),
  `SEIRState.dE s p inc` (third argument: the incidence), `SEIRState.dI`, `SEIRState.dR`,
  and the counts `SEIRState.I_pop`, `SEIRState.I_pop_wrong`.

General VOCAB-GAP (applies to every time-evolution statement below): the module has no
trajectories and no susceptible fraction `S`, and its quantities are rationals, so a real-time
trajectory of `SEIRState`s would be constant. Statements about how a quantity evolves in time
("θ is non-increasing", "S + E + I + R = 1", "d(E + I + R)/dt = …") are therefore stated at the
rate level, pointwise in the state, using the rate functions `dθ`, `dE`, `dI`, `dR`.

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace). Ids of that pass not formalised (remarks on proof status, on which notions the library
defines, or cited results needing models the vocabulary lacks): `seirIGrowthBounded-b`,
`table.SEIR5`, `table.SEIR6`.
-/

/-! ## `SEIREquations.table.SEIR1`

Text: "| SEIR1 | I_pop counts only infectious stages (I), not E |" -/
namespace Alignment.Shadows.SEIREquations.table_SEIR1

/-- Intended statement: for every state, `I_pop` is the infectious fraction `pop_I`, and in
particular it does not depend on the exposed fraction `pop_E`. -/
@[sa_reference "SEIREquations.table.SEIR1"]
def T : Prop :=
  (∀ s : SEIRState, s.I_pop = s.pop_I) ∧
    (∀ (s : SEIRState) (x : ℚ), ({ s with pop_E := x } : SEIRState).I_pop = s.I_pop)

/-- S1: "I_pop counts only infectious stages (I)": `I_pop = pop_I`. -/
@[sa_shadow "SEIREquations.table.SEIR1" 1]
def S1 : Prop := ∀ s : SEIRState, s.I_pop = s.pop_I

/-- S2: "not E": changing the E fraction leaves `I_pop` unchanged. -/
@[sa_shadow "SEIREquations.table.SEIR1" 2]
def S2 : Prop :=
  ∀ (s : SEIRState) (x : ℚ), ({ s with pop_E := x } : SEIRState).I_pop = s.I_pop

@[sa_ref_forward "SEIREquations.table.SEIR1" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "SEIREquations.table.SEIR1" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "SEIREquations.table.SEIR1"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SEIREquations.table_SEIR1

/-! ## `SEIREquations.table.SEIR2`

Text: "| SEIR2 | E does not contribute to the edge hazard |" -/
namespace Alignment.Shadows.SEIREquations.table_SEIR2

-- AMBIGUITY: "E does not contribute to the edge hazard" read as: the edge hazard does not
-- depend on φ_E (the probability that the stub's partner is in E), i.e. the E-partner edges
-- make no contribution. A reading "does not depend on the population fraction pop_E" was
-- rejected: the edge hazard is an edge-level quantity and E enters it only through φ_E.
/-- Intended statement: for every state and parameters, changing φ_E leaves the edge hazard
unchanged. -/
@[sa_reference "SEIREquations.table.SEIR2"]
def T : Prop :=
  ∀ (s : SEIRState) (p : SEIRParams) (x : ℚ),
    ({ s with φ_E := x } : SEIRState).edgeHazard p = s.edgeHazard p

/-- S1: the edge hazard is independent of φ_E. -/
@[sa_shadow "SEIREquations.table.SEIR2" 1]
def S1 : Prop :=
  ∀ (s : SEIRState) (p : SEIRParams) (x : ℚ),
    ({ s with φ_E := x } : SEIRState).edgeHazard p = s.edgeHazard p

@[sa_ref_forward "SEIREquations.table.SEIR2" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SEIREquations.table.SEIR2"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SEIREquations.table_SEIR2

/-! ## `SEIREquations.table.SEIR3`

Text: "| SEIR3 | S + E + I + R = 1 (conservation, excluding seed) |" -/
namespace Alignment.Shadows.SEIREquations.table_SEIR3

-- VOCAB-GAP: there is no susceptible fraction S, no trajectory and no initial condition in the
-- vocabulary, so "S + E + I + R = 1" cannot be stated as an identity along a solution. Its
-- differential content is stated instead: the susceptible fraction leaves at exactly the
-- incidence rate (dS/dt = −incidence, the definition of incidence), and the total rate
-- dS/dt + dE/dt + dI/dt + dR/dt vanishes. The normalisation "= 1" (an initial condition) is not
-- expressible.
-- AMBIGUITY: "excluding seed" is not formalised; at the rate level a seed (an initial
-- condition) plays no role.

/-- Rate of change of the (unrepresented) susceptible fraction: minus the incidence. -/
def dS (inc : ℚ) : ℚ := -inc

/-- Intended statement: for every state, parameters and incidence, the rates of S, E, I and R
sum to zero, so S + E + I + R is conserved. -/
@[sa_reference "SEIREquations.table.SEIR3"]
def T : Prop :=
  ∀ (s : SEIRState) (p : SEIRParams) (inc : ℚ),
    dS inc + s.dE p inc + s.dI p + s.dR p = 0

/-- S1: d(S + E + I + R)/dt = 0, with dS/dt = −incidence. -/
@[sa_shadow "SEIREquations.table.SEIR3" 1]
def S1 : Prop :=
  ∀ (s : SEIRState) (p : SEIRParams) (inc : ℚ),
    dS inc + s.dE p inc + s.dI p + s.dR p = 0

@[sa_ref_forward "SEIREquations.table.SEIR3" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SEIREquations.table.SEIR3"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SEIREquations.table_SEIR3

/-! ## `SEIREquations.table.SEIR4`

Text: "| SEIR4 | θ only decreases from I-edges (not E-edges) |" -/
namespace Alignment.Shadows.SEIREquations.table_SEIR4

-- AMBIGUITY: "θ only decreases from I-edges (not E-edges)": "only" read as attaching to
-- "from I-edges" (the parenthetical contrasts I-edges with E-edges): (S1) E-edges do not affect
-- the rate of change of θ, i.e. dθ/dt does not depend on φ_E; (S2) without I-edges (φ_I = 0)
-- θ does not decrease, i.e. dθ/dt ≥ 0. The reading "θ only decreases, i.e. never increases"
-- was rejected for this row (it is the separate claim SEIREquations.seirThetaNonincreasing).
-- VOCAB-GAP: no trajectories; "decreases" is stated through the rate dθ (= dθ/dt).

/-- Intended statement: dθ/dt is unaffected by E-edges, and θ does not decrease when there are
no I-edges. -/
@[sa_reference "SEIREquations.table.SEIR4"]
def T : Prop :=
  (∀ (s : SEIRState) (p : SEIRParams) (x : ℚ),
      ({ s with φ_E := x } : SEIRState).dθ p = s.dθ p) ∧
    (∀ (s : SEIRState) (p : SEIRParams), s.φ_I = 0 → 0 ≤ s.dθ p)

/-- S1: "not E-edges": dθ/dt is independent of φ_E. -/
@[sa_shadow "SEIREquations.table.SEIR4" 1]
def S1 : Prop :=
  ∀ (s : SEIRState) (p : SEIRParams) (x : ℚ),
    ({ s with φ_E := x } : SEIRState).dθ p = s.dθ p

/-- S2: "only from I-edges": with no I-edges (φ_I = 0), θ does not decrease. -/
@[sa_shadow "SEIREquations.table.SEIR4" 2]
def S2 : Prop := ∀ (s : SEIRState) (p : SEIRParams), s.φ_I = 0 → 0 ≤ s.dθ p

@[sa_ref_forward "SEIREquations.table.SEIR4" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "SEIREquations.table.SEIR4" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "SEIREquations.table.SEIR4"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SEIREquations.table_SEIR4

/-! ## `SEIREquations.edgeHazard`

Text: "The edge hazard: only I contributes (E has zero transmission rate). **SEIR2**: E does NOT
contribute to edge hazard." -/
namespace Alignment.Shadows.SEIREquations.edgeHazard

-- AMBIGUITY: "only I contributes (E has zero transmission rate)" read in two ways, both
-- required: (S2) the hazard is determined by the I-partner probability φ_I alone (only I
-- contributes); (S3) "the edge hazard" is the standard EBCM per-stub hazard, the sum over
-- partner stages of (stage transmission rate) × (probability the partner is in that stage),
-- with rate 0 for E and rate β for I (SEIRParams.β is the "per-edge transmission rate (I stage
-- only)"), i.e. β·φ_I.
-- AMBIGUITY: "E does NOT contribute to edge hazard" read as independence of φ_E (S1).

/-- Intended statement: the edge hazard is β·φ_I; in particular it is determined by φ_I and
independent of φ_E. -/
@[sa_reference "SEIREquations.edgeHazard"]
def T : Prop :=
  (∀ (s : SEIRState) (p : SEIRParams) (x : ℚ),
      ({ s with φ_E := x } : SEIRState).edgeHazard p = s.edgeHazard p) ∧
    (∀ (s s' : SEIRState) (p : SEIRParams), s.φ_I = s'.φ_I → s.edgeHazard p = s'.edgeHazard p) ∧
    (∀ (s : SEIRState) (p : SEIRParams), s.edgeHazard p = p.β * s.φ_I)

/-- S1: "E does NOT contribute": the edge hazard is independent of φ_E. -/
@[sa_shadow "SEIREquations.edgeHazard" 1]
def S1 : Prop :=
  ∀ (s : SEIRState) (p : SEIRParams) (x : ℚ),
    ({ s with φ_E := x } : SEIRState).edgeHazard p = s.edgeHazard p

/-- S2: "only I contributes": two states with the same φ_I have the same edge hazard. -/
@[sa_shadow "SEIREquations.edgeHazard" 2]
def S2 : Prop :=
  ∀ (s s' : SEIRState) (p : SEIRParams), s.φ_I = s'.φ_I → s.edgeHazard p = s'.edgeHazard p

/-- S3: the edge hazard is 0·φ_E + β·φ_I = β·φ_I. -/
@[sa_shadow "SEIREquations.edgeHazard" 3]
def S3 : Prop := ∀ (s : SEIRState) (p : SEIRParams), s.edgeHazard p = p.β * s.φ_I

@[sa_ref_forward "SEIREquations.edgeHazard" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "SEIREquations.edgeHazard" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "SEIREquations.edgeHazard" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2

@[sa_complete "SEIREquations.edgeHazard"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.SEIREquations.edgeHazard

/-! ## `SEIREquations.dTheta`

Text: "dθ/dt = −β·φ_I (only infectious edges cause transmission). **SEIR4**: θ does not decrease
from E-edges." -/
namespace Alignment.Shadows.SEIREquations.dTheta

-- AMBIGUITY: "θ does not decrease from E-edges" read as: the rate dθ/dt does not depend on φ_E
-- (E-edges make no contribution to the decrease of θ). The parenthetical "(only infectious
-- edges cause transmission)" is explanatory and is implied by the formula (S1).

/-- Intended statement: dθ/dt = −β·φ_I, and dθ/dt is independent of φ_E. -/
@[sa_reference "SEIREquations.dTheta"]
def T : Prop :=
  (∀ (s : SEIRState) (p : SEIRParams), s.dθ p = -p.β * s.φ_I) ∧
    (∀ (s : SEIRState) (p : SEIRParams) (x : ℚ),
      ({ s with φ_E := x } : SEIRState).dθ p = s.dθ p)

/-- S1: dθ/dt = −β·φ_I. -/
@[sa_shadow "SEIREquations.dTheta" 1]
def S1 : Prop := ∀ (s : SEIRState) (p : SEIRParams), s.dθ p = -p.β * s.φ_I

/-- S2: θ does not decrease from E-edges: dθ/dt is independent of φ_E. -/
@[sa_shadow "SEIREquations.dTheta" 2]
def S2 : Prop :=
  ∀ (s : SEIRState) (p : SEIRParams) (x : ℚ),
    ({ s with φ_E := x } : SEIRState).dθ p = s.dθ p

@[sa_ref_forward "SEIREquations.dTheta" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "SEIREquations.dTheta" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "SEIREquations.dTheta"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SEIREquations.dTheta

/-! ## `SEIREquations.seirPopulationConservation`

Text: "**SEIR3.** Population conservation: d(E + I + R)/dt = incidence. The total non-susceptible
fraction grows exactly at the incidence rate." -/
namespace Alignment.Shadows.SEIREquations.seirPopulationConservation

-- VOCAB-GAP: no trajectories; d(E + I + R)/dt is the sum of the rate functions dE + dI + dR at
-- a state, with the incidence passed as the third argument of dE (DataTypes).
-- The second sentence ("The total non-susceptible fraction grows exactly at the incidence
-- rate") restates the first (E + I + R is the non-susceptible fraction) and adds no shadow.

/-- Intended statement: for every state, parameters and incidence, dE + dI + dR = incidence. -/
@[sa_reference "SEIREquations.seirPopulationConservation"]
def T : Prop :=
  ∀ (s : SEIRState) (p : SEIRParams) (inc : ℚ), s.dE p inc + s.dI p + s.dR p = inc

/-- S1: d(E + I + R)/dt = incidence, for every incidence value. -/
@[sa_shadow "SEIREquations.seirPopulationConservation" 1]
def S1 : Prop :=
  ∀ (s : SEIRState) (p : SEIRParams) (inc : ℚ), s.dE p inc + s.dI p + s.dR p = inc

@[sa_ref_forward "SEIREquations.seirPopulationConservation" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SEIREquations.seirPopulationConservation"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SEIREquations.seirPopulationConservation

/-! ## `SEIREquations.iPopZeroAtSeed-a`

Text: "**SEIR1.** I_pop counts only infectious stages." -/
namespace Alignment.Shadows.SEIREquations.iPopZeroAtSeed_a

-- AMBIGUITY: "counts only infectious stages" read as: I_pop is exactly the fraction in the
-- infectious stage I (the only infectious stage of S → E → I → R), for every state.

/-- Intended statement: for every state, `I_pop = pop_I`. -/
@[sa_reference "SEIREquations.iPopZeroAtSeed-a"]
def T : Prop := ∀ s : SEIRState, s.I_pop = s.pop_I

/-- S1: `I_pop = pop_I` for every state. -/
@[sa_shadow "SEIREquations.iPopZeroAtSeed-a" 1]
def S1 : Prop := ∀ s : SEIRState, s.I_pop = s.pop_I

@[sa_ref_forward "SEIREquations.iPopZeroAtSeed-a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SEIREquations.iPopZeroAtSeed-a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SEIREquations.iPopZeroAtSeed_a

/-! ## `SEIREquations.iPopZeroAtSeed-b`

Text: "At t=0 with seed in E: I_pop = 0, not ε." -/
namespace Alignment.Shadows.SEIREquations.iPopZeroAtSeed_b

-- AMBIGUITY: "At t=0 with seed in E" read as the state ⟨θ, φ_E, φ_I, ε, 0, 0⟩: the seed
-- fraction ε > 0 is in E and nothing is yet in I or R (t = 0). The text does not fix the edge
-- variables θ, φ_E, φ_I at t = 0, so they are universally quantified. "seed" is read as a
-- positive fraction, 0 < ε (needed for "not ε" to say anything).
-- VOCAB-GAP: no trajectories or initial-condition operation; "at t=0" is represented by the
-- initial state above.

/-- Intended statement: for every seed size ε > 0 and all edge variables, the initial state with
the seed in E has I_pop = 0, and I_pop ≠ ε. -/
@[sa_reference "SEIREquations.iPopZeroAtSeed-b"]
def T : Prop :=
  ∀ (ε θ φE φI : ℚ), 0 < ε →
    SEIRState.I_pop ⟨θ, φE, φI, ε, 0, 0⟩ = 0 ∧ SEIRState.I_pop ⟨θ, φE, φI, ε, 0, 0⟩ ≠ ε

/-- S1: "I_pop = 0" at t = 0 with the seed in E. -/
@[sa_shadow "SEIREquations.iPopZeroAtSeed-b" 1]
def S1 : Prop :=
  ∀ (ε θ φE φI : ℚ), 0 < ε → SEIRState.I_pop ⟨θ, φE, φI, ε, 0, 0⟩ = 0

/-- S2: "not ε": at t = 0 with the seed in E, I_pop ≠ ε. -/
@[sa_shadow "SEIREquations.iPopZeroAtSeed-b" 2]
def S2 : Prop :=
  ∀ (ε θ φE φI : ℚ), 0 < ε → SEIRState.I_pop ⟨θ, φE, φI, ε, 0, 0⟩ ≠ ε

@[sa_ref_forward "SEIREquations.iPopZeroAtSeed-b" 1]
theorem ref_fwd1 : T → S1 := fun t ε θ φE φI h => (t ε θ φE φI h).1

@[sa_ref_forward "SEIREquations.iPopZeroAtSeed-b" 2]
theorem ref_fwd2 : T → S2 := fun t ε θ φE φI h => (t ε θ φE φI h).2

@[sa_complete "SEIREquations.iPopZeroAtSeed-b"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun ε θ φE φI h => ⟨s1 ε θ φE φI h, s2 ε θ φE φI h⟩

end Alignment.Shadows.SEIREquations.iPopZeroAtSeed_b

/-! ## `SEIREquations.iPopWrongNonzeroAtSeed`

Text: "The buggy version gives ε at t=0 (wrong)." -/
namespace Alignment.Shadows.SEIREquations.iPopWrongNonzeroAtSeed

-- AMBIGUITY: "The buggy version" read as `SEIRState.I_pop_wrong` (DataTypes: "The wrong
-- definition that caused the bug"); "at t=0" read, as in iPopZeroAtSeed-b, as the state
-- ⟨θ, φ_E, φ_I, ε, 0, 0⟩ with the seed ε > 0 in E and arbitrary edge variables.
-- AMBIGUITY: "(wrong)" read as: the value differs from the correct infectious count at t = 0,
-- which is 0 (nobody is infectious yet), i.e. I_pop_wrong ≠ 0 at the seed state (S2).
-- VOCAB-GAP: no trajectories or initial-condition operation (see iPopZeroAtSeed-b).

/-- Intended statement: at t = 0 with seed ε > 0 in E, `I_pop_wrong = ε`, which is nonzero. -/
@[sa_reference "SEIREquations.iPopWrongNonzeroAtSeed"]
def T : Prop :=
  ∀ (ε θ φE φI : ℚ), 0 < ε →
    SEIRState.I_pop_wrong ⟨θ, φE, φI, ε, 0, 0⟩ = ε ∧
      SEIRState.I_pop_wrong ⟨θ, φE, φI, ε, 0, 0⟩ ≠ 0

/-- S1: "gives ε at t=0". -/
@[sa_shadow "SEIREquations.iPopWrongNonzeroAtSeed" 1]
def S1 : Prop :=
  ∀ (ε θ φE φI : ℚ), 0 < ε → SEIRState.I_pop_wrong ⟨θ, φE, φI, ε, 0, 0⟩ = ε

/-- S2: "(wrong)": the buggy count at t = 0 is not the true count 0. -/
@[sa_shadow "SEIREquations.iPopWrongNonzeroAtSeed" 2]
def S2 : Prop :=
  ∀ (ε θ φE φI : ℚ), 0 < ε → SEIRState.I_pop_wrong ⟨θ, φE, φI, ε, 0, 0⟩ ≠ 0

@[sa_ref_forward "SEIREquations.iPopWrongNonzeroAtSeed" 1]
theorem ref_fwd1 : T → S1 := fun t ε θ φE φI h => (t ε θ φE φI h).1

@[sa_ref_forward "SEIREquations.iPopWrongNonzeroAtSeed" 2]
theorem ref_fwd2 : T → S2 := fun t ε θ φE φI h => (t ε θ φE φI h).2

@[sa_complete "SEIREquations.iPopWrongNonzeroAtSeed"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun ε θ φE φI h => ⟨s1 ε θ φE φI h, s2 ε θ φE φI h⟩

end Alignment.Shadows.SEIREquations.iPopWrongNonzeroAtSeed

/-! ## `SEIREquations.iPopLeWrong`

Text: "**SEIR1b.** I_pop ≤ I_pop_wrong (correct is always ≤ buggy)." -/
namespace Alignment.Shadows.SEIREquations.iPopLeWrong

-- AMBIGUITY: "always" read as: for every state whose exposed fraction pop_E is nonnegative
-- (pop_E is a "fraction of population"; SEIRState carries no sign constraint, and for a
-- negative E fraction a count that adds E would be smaller). Only this validity condition is
-- assumed; no other field is constrained.

/-- Intended statement: for every state with `0 ≤ pop_E`, `I_pop ≤ I_pop_wrong`. -/
@[sa_reference "SEIREquations.iPopLeWrong"]
def T : Prop := ∀ s : SEIRState, 0 ≤ s.pop_E → s.I_pop ≤ s.I_pop_wrong

/-- S1: the correct count is at most the buggy count, for every state with `0 ≤ pop_E`. -/
@[sa_shadow "SEIREquations.iPopLeWrong" 1]
def S1 : Prop := ∀ s : SEIRState, 0 ≤ s.pop_E → s.I_pop ≤ s.I_pop_wrong

@[sa_ref_forward "SEIREquations.iPopLeWrong" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SEIREquations.iPopLeWrong"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SEIREquations.iPopLeWrong

/-! ## `SEIREquations.edgeHazardIndependentOfE`

Text: "**SEIR2.** The edge hazard is independent of φ_E." -/
namespace Alignment.Shadows.SEIREquations.edgeHazardIndependentOfE

/-- Intended statement: for every state, parameters and value `x`, replacing φ_E by `x` leaves
the edge hazard unchanged. -/
@[sa_reference "SEIREquations.edgeHazardIndependentOfE"]
def T : Prop :=
  ∀ (s : SEIRState) (p : SEIRParams) (x : ℚ),
    ({ s with φ_E := x } : SEIRState).edgeHazard p = s.edgeHazard p

/-- S1: the edge hazard is independent of φ_E. -/
@[sa_shadow "SEIREquations.edgeHazardIndependentOfE" 1]
def S1 : Prop :=
  ∀ (s : SEIRState) (p : SEIRParams) (x : ℚ),
    ({ s with φ_E := x } : SEIRState).edgeHazard p = s.edgeHazard p

@[sa_ref_forward "SEIREquations.edgeHazardIndependentOfE" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SEIREquations.edgeHazardIndependentOfE"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SEIREquations.edgeHazardIndependentOfE

/-! ## `SEIREquations.seirThetaNonincreasing`

Text: "**SEIR4.** θ is non-increasing (same proof as SIR)." -/
namespace Alignment.Shadows.SEIREquations.seirThetaNonincreasing

-- VOCAB-GAP: no trajectories; "θ is non-increasing" is stated at the rate level as
-- dθ/dt ≤ 0 at every (valid) state.
-- AMBIGUITY: the text gives no domain; read as every state whose I-partner probability φ_I is
-- nonnegative (φ_I is a probability; SEIRState carries no sign constraint). No other field is
-- constrained. "(same proof as SIR)" is a remark about the proof and is not formalised.

/-- Intended statement: for all parameters and every state with `0 ≤ φ_I`, `dθ/dt ≤ 0`. -/
@[sa_reference "SEIREquations.seirThetaNonincreasing"]
def T : Prop := ∀ (s : SEIRState) (p : SEIRParams), 0 ≤ s.φ_I → s.dθ p ≤ 0

/-- S1: dθ/dt ≤ 0 whenever φ_I ≥ 0. -/
@[sa_shadow "SEIREquations.seirThetaNonincreasing" 1]
def S1 : Prop := ∀ (s : SEIRState) (p : SEIRParams), 0 ≤ s.φ_I → s.dθ p ≤ 0

@[sa_ref_forward "SEIREquations.seirThetaNonincreasing" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "SEIREquations.seirThetaNonincreasing"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.SEIREquations.seirThetaNonincreasing

noncomputable section

/-! ## `SEIREquations.seirIGrowthBounded-a` (re-authored blind)

Text: "**SEIR5 (auxiliary; not a peak bound).** If σ·pop_E ≤ pop_E + pop_I, then
dI/dt ≤ pop_E + pop_I − γ·pop_I. Since dI/dt = σ·pop_E − γ·pop_I, this only restates the
hypothesis; it does not compare SEIR with SIR, and σ·pop_E can exceed the SIR incidence."

S1: the implication; S2: dI/dt = σ·pop_E − γ·pop_I (`SEIRState.dI`). The remarks (restates the
hypothesis, no comparison with SIR) describe the statement; the SIR incidence is not defined in the
vocabulary and the last clause is not formalised. -/
namespace Alignment.Shadows.SEIREquations.seirIGrowthBounded_a

@[sa_reference "SEIREquations.seirIGrowthBounded-a"]
def T : Prop :=
  (∀ (s : SEIRState) (p : SEIRParams), p.σ * s.pop_E ≤ s.pop_E + s.pop_I →
      s.dI p ≤ s.pop_E + s.pop_I - p.γ * s.pop_I) ∧
  (∀ (s : SEIRState) (p : SEIRParams), s.dI p = p.σ * s.pop_E - p.γ * s.pop_I)

/-- S1: `σ·pop_E ≤ pop_E + pop_I → dI/dt ≤ pop_E + pop_I − γ·pop_I`. -/
@[sa_shadow "SEIREquations.seirIGrowthBounded-a" 1]
def S1 : Prop :=
  ∀ (s : SEIRState) (p : SEIRParams), p.σ * s.pop_E ≤ s.pop_E + s.pop_I →
    s.dI p ≤ s.pop_E + s.pop_I - p.γ * s.pop_I
/-- S2: `dI/dt = σ·pop_E − γ·pop_I`. -/
@[sa_shadow "SEIREquations.seirIGrowthBounded-a" 2]
def S2 : Prop := ∀ (s : SEIRState) (p : SEIRParams), s.dI p = p.σ * s.pop_E - p.γ * s.pop_I

@[sa_ref_forward "SEIREquations.seirIGrowthBounded-a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SEIREquations.seirIGrowthBounded-a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "SEIREquations.seirIGrowthBounded-a"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.SEIREquations.seirIGrowthBounded_a

end
