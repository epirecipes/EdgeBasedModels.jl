import Alignment.Registry
import EBCMCategory.VolzMeyersEquations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Blind shadow sets: group `VolzMeyersEquations`

Written blind: the author read only the claims' entries in `Alignment/claims_blind.yaml`,
`Alignment/DataTypes/VolzMeyersEquations.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean` and `SA-PASS_SKILL.md`. No trusted statement, definition
body or checker was read.

Vocabulary used (from DataTypes): `VMState` (ℚ fields `θ P₁ P_S M₁ I R`), `VMParams`
(`β γ ρ κ` with `0 < β`, `0 < γ`, `0 ≤ ρ`), and the opaque operations `VMState.dθ`,
`VMState.dI`, `VMState.dR`, `VMState.incidence`, `VMState.P_R`, `VMState.excessRatio`,
`staticParams`, `vmInitialState`.

Notions the DataTypes cannot express are written with Mathlib primitives and marked `VOCAB-GAP`:
real-valued trajectories (the state is a ℚ-valued point, so there is no time), the PGF ψ and its
derivatives (no ψ in `VMState`/`VMParams`), the susceptible fraction `S` (not a field), and the
`Ṗ₁`, `Ṗ_S` right-hand sides of the header equation table (no operations for them).

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace). Ids of that pass not formalised (remarks on proof status, on which notions the library
defines, or cited results needing models the vocabulary lacks): `header.equationLevel`.
-/

namespace Alignment.Shadows.VolzMeyersEquations

/-! ## Shared primitive notions (helpers; not operations under test) -/

/-- A degree distribution: `q k ≥ 0` is the probability of degree `k`, and the weights sum to 1.
-- VOCAB-GAP: DataTypes has no PGF; a PGF is represented by its degree distribution. -/
def IsDegreeDist (q : ℕ → ℝ) : Prop := (∀ k, 0 ≤ q k) ∧ HasSum q 1

/-- The PGF ψ(x) = Σₖ qₖ xᵏ of the degree distribution `q`. -/
noncomputable def psi (q : ℕ → ℝ) (x : ℝ) : ℝ := ∑' k : ℕ, q k * x ^ k

/-- ψ'(x) = Σₖ (k+1) q_{k+1} xᵏ (termwise derivative of the PGF; ψ'(1) is the mean degree). -/
noncomputable def psi1 (q : ℕ → ℝ) (x : ℝ) : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) * q (k + 1) * x ^ k

/-- ψ''(x) = Σₖ (k+2)(k+1) q_{k+2} xᵏ (second termwise derivative of the PGF). -/
noncomputable def psi2 (q : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * q (k + 2) * x ^ k

/-- The header-table θ-equation θ̇ = −β P₁ θ along real trajectories `θ, P₁ : ℝ → ℝ`.
-- VOCAB-GAP: no trajectory notion in DataTypes (`VMState.dθ` is a ℚ-valued rate at a point). -/
def ThetaODE (p : VMParams) (θ P₁ : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt θ (-(p.β : ℝ) * P₁ t * θ t) t

/-- Header-table right-hand side of Ṗ₁ with P₁ replaced by `x` and the other state fields from `s`:
β P₁ P_S θψ''(θ)/ψ'(θ) − P₁(1−P₁)β − P₁γ + ρ(M₁ − P₁), where θψ''(θ)/ψ'(θ) is the operation
`VMState.excessRatio` (docstring "The excess degree ratio θ·ψ''(θ)/ψ'(θ)").
-- VOCAB-GAP: no operation for Ṗ₁.
-- AMBIGUITY: the ℚ argument of `excessRatio` is undocumented; taken to be κ (Poisson case). -/
noncomputable def rateP1 (s : VMState) (p : VMParams) (x : ℝ) : ℝ :=
  (p.β : ℝ) * x * (s.P_S : ℝ) * (s.excessRatio p.κ : ℝ) - x * (1 - x) * (p.β : ℝ)
    - x * (p.γ : ℝ) + (p.ρ : ℝ) * ((s.M₁ : ℝ) - x)

/-- Header-table right-hand side of Ṗ_S with P_S replaced by `x`, for the PGF of `q`:
β P_S P₁ (1 − θψ''(θ)/ψ'(θ)) + ρ(ψ'(θ)/ψ'(1) − P_S).
-- VOCAB-GAP: no operation for Ṗ_S and no ψ in the data types. -/
noncomputable def ratePS (q : ℕ → ℝ) (s : VMState) (p : VMParams) (x : ℝ) : ℝ :=
  (p.β : ℝ) * x * (s.P₁ : ℝ) * (1 - (s.θ : ℝ) * psi2 q s.θ / psi1 q s.θ)
    + (p.ρ : ℝ) * (psi1 q s.θ / psi1 q 1 - x)

end Alignment.Shadows.VolzMeyersEquations

/-! ## VM1 -/

namespace Alignment.Shadows.VolzMeyersEquations.table_VM1

open Alignment.Shadows.VolzMeyersEquations

/-! ### `VolzMeyersEquations.table.VM1`
Blind text: "| VM1 | θ is non-increasing (dθ/dt ≤ 0) |"

-- AMBIGUITY: the row states no hypotheses; unconditionally dθ/dt ≤ 0 fails for P₁ < 0, so the
-- conditions "β > 0, P₁ ≥ 0, θ ≥ 0" are taken from the **VM1.** docstring this row indexes
-- (β > 0 is the `VMParams.β_pos` invariant).
-- AMBIGUITY: "θ is non-increasing (dθ/dt ≤ 0)" read as (S1) the rate `VMState.dθ` is ≤ 0 at
-- every admissible state, and (S2) literally: θ(t) is antitone along every trajectory of
-- θ̇ = −β P₁ θ with P₁(t) ≥ 0, θ(t) ≥ 0. Both are required.
-- VOCAB-GAP: S2 uses real trajectories (`ThetaODE`), not expressible with `VMState`. -/

@[sa_reference "VolzMeyersEquations.table.VM1"]
def T : Prop :=
  (∀ (s : VMState) (p : VMParams), 0 ≤ s.P₁ → 0 ≤ s.θ → s.dθ p ≤ 0) ∧
  (∀ (p : VMParams) (θ P₁ : ℝ → ℝ),
    ThetaODE p θ P₁ → (∀ t, 0 ≤ P₁ t) → (∀ t, 0 ≤ θ t) → Antitone θ)

/-- S1: dθ/dt ≤ 0 at every state with P₁ ≥ 0, θ ≥ 0 (any parameters, so β > 0). -/
@[sa_shadow "VolzMeyersEquations.table.VM1" 1]
def S1 : Prop := ∀ (s : VMState) (p : VMParams), 0 ≤ s.P₁ → 0 ≤ s.θ → s.dθ p ≤ 0

/-- S2: θ is non-increasing in time along solutions of θ̇ = −β P₁ θ with P₁ ≥ 0, θ ≥ 0. -/
@[sa_shadow "VolzMeyersEquations.table.VM1" 2]
def S2 : Prop :=
  ∀ (p : VMParams) (θ P₁ : ℝ → ℝ),
    ThetaODE p θ P₁ → (∀ t, 0 ≤ P₁ t) → (∀ t, 0 ≤ θ t) → Antitone θ

@[sa_ref_forward "VolzMeyersEquations.table.VM1" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "VolzMeyersEquations.table.VM1" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "VolzMeyersEquations.table.VM1"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.VolzMeyersEquations.table_VM1

namespace Alignment.Shadows.VolzMeyersEquations.thetaNonincreasing

open Alignment.Shadows.VolzMeyersEquations

/-! ### `VolzMeyersEquations.thetaNonincreasing`
Blind text: "**VM1.** θ is non-increasing: dθ/dt ≤ 0 whenever β > 0, P₁ ≥ 0, θ ≥ 0."

-- AMBIGUITY: "θ is non-increasing: dθ/dt ≤ 0 whenever …" read as (S1) the pointwise rate
-- condition spelled out after the colon, and (S2) the headline literally (θ(t) antitone along
-- trajectories satisfying the same conditions at every time). Both are required.
-- VOCAB-GAP: S2 uses real trajectories (`ThetaODE`). -/

@[sa_reference "VolzMeyersEquations.thetaNonincreasing"]
def T : Prop :=
  (∀ (s : VMState) (p : VMParams), 0 ≤ s.P₁ → 0 ≤ s.θ → s.dθ p ≤ 0) ∧
  (∀ (p : VMParams) (θ P₁ : ℝ → ℝ),
    ThetaODE p θ P₁ → (∀ t, 0 ≤ P₁ t) → (∀ t, 0 ≤ θ t) → Antitone θ)

/-- S1: dθ/dt ≤ 0 whenever β > 0 (from `VMParams`), P₁ ≥ 0, θ ≥ 0. -/
@[sa_shadow "VolzMeyersEquations.thetaNonincreasing" 1]
def S1 : Prop := ∀ (s : VMState) (p : VMParams), 0 ≤ s.P₁ → 0 ≤ s.θ → s.dθ p ≤ 0

/-- S2: θ(t) is non-increasing along solutions of θ̇ = −β P₁ θ with P₁(t) ≥ 0, θ(t) ≥ 0. -/
@[sa_shadow "VolzMeyersEquations.thetaNonincreasing" 2]
def S2 : Prop :=
  ∀ (p : VMParams) (θ P₁ : ℝ → ℝ),
    ThetaODE p θ P₁ → (∀ t, 0 ≤ P₁ t) → (∀ t, 0 ≤ θ t) → Antitone θ

@[sa_ref_forward "VolzMeyersEquations.thetaNonincreasing" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "VolzMeyersEquations.thetaNonincreasing" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "VolzMeyersEquations.thetaNonincreasing"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.VolzMeyersEquations.thetaNonincreasing

/-! ## VM2 -/

namespace Alignment.Shadows.VolzMeyersEquations.table_VM2

/-! ### `VolzMeyersEquations.table.VM2`
Blind text: "| VM2 | Edge partition: P₁ + P_S + P_R = 1 (where P_R = 1-P₁-P_S) |"

The "(where P_R = 1-P₁-P_S)" clause defines the symbol P_R; it is the docstring of the operation
`VMState.P_R`, so P_R is that operation (its definition is a bridge matter, not a shadow).
No hypotheses are stated: every state. -/

@[sa_reference "VolzMeyersEquations.table.VM2"]
def T : Prop := ∀ s : VMState, s.P₁ + s.P_S + s.P_R = 1

/-- S1: for every state, P₁ + P_S + P_R = 1. -/
@[sa_shadow "VolzMeyersEquations.table.VM2" 1]
def S1 : Prop := ∀ s : VMState, s.P₁ + s.P_S + s.P_R = 1

@[sa_ref_forward "VolzMeyersEquations.table.VM2" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "VolzMeyersEquations.table.VM2"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.VolzMeyersEquations.table_VM2

namespace Alignment.Shadows.VolzMeyersEquations.edgePartition

/-! ### `VolzMeyersEquations.edgePartition`
Blind text: "**VM2.** Edge partition: P₁ + P_S + P_R = 1 (by definition of P_R)."

"(by definition of P_R)" is the justification; P_R is the operation `VMState.P_R`. -/

@[sa_reference "VolzMeyersEquations.edgePartition"]
def T : Prop := ∀ s : VMState, s.P₁ + s.P_S + s.P_R = 1

/-- S1: for every state, P₁ + P_S + P_R = 1. -/
@[sa_shadow "VolzMeyersEquations.edgePartition" 1]
def S1 : Prop := ∀ s : VMState, s.P₁ + s.P_S + s.P_R = 1

@[sa_ref_forward "VolzMeyersEquations.edgePartition" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "VolzMeyersEquations.edgePartition"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.VolzMeyersEquations.edgePartition

/-! ## VM3 -/

namespace Alignment.Shadows.VolzMeyersEquations.table_VM3

/-! ### `VolzMeyersEquations.table.VM3`
Blind text: "| VM3 | Population conservation: d(pop_I + pop_R)/dt = incidence |"

d(pop_I + pop_R)/dt is the sum of the rate operations `VMState.dI` (d(pop_I)/dt) and
`VMState.dR` (d(pop_R)/dt); "incidence" is the operation `VMState.incidence`. No hypotheses:
every state and parameter set. A trajectory version would only add linearity of the time
derivative (it does not involve the operations), so it is not a separate shadow. -/

@[sa_reference "VolzMeyersEquations.table.VM3"]
def T : Prop := ∀ (s : VMState) (p : VMParams), s.dI p + s.dR p = s.incidence p

/-- S1: d(pop_I)/dt + d(pop_R)/dt equals the incidence, at every state. -/
@[sa_shadow "VolzMeyersEquations.table.VM3" 1]
def S1 : Prop := ∀ (s : VMState) (p : VMParams), s.dI p + s.dR p = s.incidence p

@[sa_ref_forward "VolzMeyersEquations.table.VM3" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "VolzMeyersEquations.table.VM3"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.VolzMeyersEquations.table_VM3

namespace Alignment.Shadows.VolzMeyersEquations.populationInflux_a

/-! ### `VolzMeyersEquations.populationInflux-a`
Blind text: "**VM3.** Population dynamics: d(I + R)/dt = incidence."

I, R are the population fractions `VMState.I`, `VMState.R`; their rates are `VMState.dI`,
`VMState.dR`. -/

@[sa_reference "VolzMeyersEquations.populationInflux-a"]
def T : Prop := ∀ (s : VMState) (p : VMParams), s.dI p + s.dR p = s.incidence p

/-- S1: dI/dt + dR/dt equals the incidence, at every state. -/
@[sa_shadow "VolzMeyersEquations.populationInflux-a" 1]
def S1 : Prop := ∀ (s : VMState) (p : VMParams), s.dI p + s.dR p = s.incidence p

@[sa_ref_forward "VolzMeyersEquations.populationInflux-a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "VolzMeyersEquations.populationInflux-a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.VolzMeyersEquations.populationInflux_a

/-! ## VM4 -/

namespace Alignment.Shadows.VolzMeyersEquations.table_VM4

open Alignment.Shadows.VolzMeyersEquations

/-! ### `VolzMeyersEquations.table.VM4`
Blind text: "| VM4 | S is non-increasing (follows from VM1 and PGF monotonicity) |"

S = ψ(θ) (module header: "Susceptible fraction: S = ψ(θ)").
-- AMBIGUITY: the row names no specific distribution and appeals to "PGF monotonicity", so ψ is
-- read as an arbitrary PGF (degree distribution `q`), not only Poisson.
-- AMBIGUITY: "S is non-increasing" read as (S1) the induced rate dS/dt = ψ'(θ)·dθ/dt ≤ 0 at
-- every admissible state (P₁ ≥ 0 and θ ∈ [0,1], θ being a probability; VM1 conditions), and
-- (S2) literally: t ↦ ψ(θ(t)) is antitone along trajectories of θ̇ = −β P₁ θ with P₁ ≥ 0,
-- θ ∈ [0,1]. Both are required.
-- The clause "follows from VM1 and PGF monotonicity" is a justification, not formalised.
-- VOCAB-GAP: no ψ or S in DataTypes; no trajectories. -/

@[sa_reference "VolzMeyersEquations.table.VM4"]
def T : Prop :=
  (∀ q : ℕ → ℝ, IsDegreeDist q → ∀ (s : VMState) (p : VMParams),
    0 ≤ s.P₁ → 0 ≤ s.θ → s.θ ≤ 1 → psi1 q s.θ * (s.dθ p : ℝ) ≤ 0) ∧
  (∀ q : ℕ → ℝ, IsDegreeDist q → ∀ (p : VMParams) (θ P₁ : ℝ → ℝ),
    ThetaODE p θ P₁ → (∀ t, 0 ≤ P₁ t) → (∀ t, 0 ≤ θ t) → (∀ t, θ t ≤ 1) →
      Antitone (fun t => psi q (θ t)))

/-- S1: for every PGF, dS/dt = ψ'(θ)·dθ/dt ≤ 0 at states with P₁ ≥ 0, 0 ≤ θ ≤ 1. -/
@[sa_shadow "VolzMeyersEquations.table.VM4" 1]
def S1 : Prop :=
  ∀ q : ℕ → ℝ, IsDegreeDist q → ∀ (s : VMState) (p : VMParams),
    0 ≤ s.P₁ → 0 ≤ s.θ → s.θ ≤ 1 → psi1 q s.θ * (s.dθ p : ℝ) ≤ 0

/-- S2: for every PGF, S(t) = ψ(θ(t)) is non-increasing along θ̇ = −β P₁ θ (P₁ ≥ 0, θ ∈ [0,1]). -/
@[sa_shadow "VolzMeyersEquations.table.VM4" 2]
def S2 : Prop :=
  ∀ q : ℕ → ℝ, IsDegreeDist q → ∀ (p : VMParams) (θ P₁ : ℝ → ℝ),
    ThetaODE p θ P₁ → (∀ t, 0 ≤ P₁ t) → (∀ t, 0 ≤ θ t) → (∀ t, θ t ≤ 1) →
      Antitone (fun t => psi q (θ t))

@[sa_ref_forward "VolzMeyersEquations.table.VM4" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "VolzMeyersEquations.table.VM4" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "VolzMeyersEquations.table.VM4"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.VolzMeyersEquations.table_VM4

namespace Alignment.Shadows.VolzMeyersEquations.sNonincreasing_a

open Alignment.Shadows.VolzMeyersEquations

/-! ### `VolzMeyersEquations.sNonincreasing-a`
Blind text: "**VM4.** S is non-increasing (for Poisson PGF, S = exp(κ(θ-1))). Since θ is
non-increasing (VM1) and exp is monotone, S is non-increasing."

S = exp(κ(θ−1)) with κ the mean degree `VMParams.κ`.
-- AMBIGUITY: no sign condition on κ is stated; "Poisson PGF" with mean κ (and the next sentence,
-- "when κ > 0") gives κ > 0. The VM1 conditions (P₁ ≥ 0, θ ≥ 0) are the premise "θ is
-- non-increasing (VM1)".
-- AMBIGUITY: "S is non-increasing" read as (S1) literally: t ↦ exp(κ(θ(t)−1)) is antitone along
-- trajectories of θ̇ = −β P₁ θ with P₁ ≥ 0, θ ≥ 0; and (S2) the rate reading: the induced rate
-- dS/dt = (d/dθ exp(κ(θ−1)))·dθ/dt is ≤ 0 at every such state. Both are required.
-- VOCAB-GAP: S and exp are not expressible over the ℚ-valued `VMState`; real casts are used. -/

@[sa_reference "VolzMeyersEquations.sNonincreasing-a"]
def T : Prop :=
  (∀ p : VMParams, 0 < p.κ → ∀ θ P₁ : ℝ → ℝ,
    ThetaODE p θ P₁ → (∀ t, 0 ≤ P₁ t) → (∀ t, 0 ≤ θ t) →
      Antitone (fun t => Real.exp ((p.κ : ℝ) * (θ t - 1)))) ∧
  (∀ (s : VMState) (p : VMParams), 0 < p.κ → 0 ≤ s.P₁ → 0 ≤ s.θ →
    deriv (fun x : ℝ => Real.exp ((p.κ : ℝ) * (x - 1))) (s.θ : ℝ) * (s.dθ p : ℝ) ≤ 0)

/-- S1: for Poisson (κ > 0), S(t) = exp(κ(θ(t)−1)) is non-increasing along VM θ-trajectories. -/
@[sa_shadow "VolzMeyersEquations.sNonincreasing-a" 1]
def S1 : Prop :=
  ∀ p : VMParams, 0 < p.κ → ∀ θ P₁ : ℝ → ℝ,
    ThetaODE p θ P₁ → (∀ t, 0 ≤ P₁ t) → (∀ t, 0 ≤ θ t) →
      Antitone (fun t => Real.exp ((p.κ : ℝ) * (θ t - 1)))

/-- S2: for Poisson (κ > 0), the rate of S = exp(κ(θ−1)) induced by dθ/dt is ≤ 0 at states with
P₁ ≥ 0, θ ≥ 0. -/
@[sa_shadow "VolzMeyersEquations.sNonincreasing-a" 2]
def S2 : Prop :=
  ∀ (s : VMState) (p : VMParams), 0 < p.κ → 0 ≤ s.P₁ → 0 ≤ s.θ →
    deriv (fun x : ℝ => Real.exp ((p.κ : ℝ) * (x - 1))) (s.θ : ℝ) * (s.dθ p : ℝ) ≤ 0

@[sa_ref_forward "VolzMeyersEquations.sNonincreasing-a" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "VolzMeyersEquations.sNonincreasing-a" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "VolzMeyersEquations.sNonincreasing-a"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.VolzMeyersEquations.sNonincreasing_a

/-! ## VM5 -/

namespace Alignment.Shadows.VolzMeyersEquations.table_VM5

/-! ### `VolzMeyersEquations.table.VM5`
Blind text: "| VM5 | Static limit (ρ=0): θ̇ = −β P₁ θ reduces to static EBCM |"

The static limit is the operation `staticParams` ("Static parameters: ρ = 0").
-- AMBIGUITY: "θ̇ = −β P₁ θ reduces to static EBCM" read as: at ρ = 0 the VM θ-rate is the
-- static-network (Volz) EBCM θ-equation θ̇ = −β p_I θ, with P₁ in the role of p_I.
-- VOCAB-GAP: DataTypes has no static-EBCM θ-equation; it is written in primitive terms. -/

@[sa_reference "VolzMeyersEquations.table.VM5"]
def T : Prop :=
  ∀ (s : VMState) (β γ κ : ℚ) (hβ : 0 < β) (hγ : 0 < γ),
    s.dθ (staticParams β γ κ hβ hγ) = -β * s.P₁ * s.θ

/-- S1: with static parameters (ρ = 0), dθ/dt = −β P₁ θ at every state. -/
@[sa_shadow "VolzMeyersEquations.table.VM5" 1]
def S1 : Prop :=
  ∀ (s : VMState) (β γ κ : ℚ) (hβ : 0 < β) (hγ : 0 < γ),
    s.dθ (staticParams β γ κ hβ hγ) = -β * s.P₁ * s.θ

@[sa_ref_forward "VolzMeyersEquations.table.VM5" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "VolzMeyersEquations.table.VM5"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.VolzMeyersEquations.table_VM5

namespace Alignment.Shadows.VolzMeyersEquations.staticThetaEq_a

/-! ### `VolzMeyersEquations.staticThetaEq-a`
Blind text: "**VM5.** In the static limit, the θ equation dθ/dt = −β P₁ θ is independent of ρ"

The predicate is "is independent of ρ"; "dθ/dt = −β P₁ θ" names the equation (the docstring of
`VMState.dθ`), so it is not a separate requirement.
-- AMBIGUITY: read as (S1) changing only ρ does not change dθ/dt, and (S2) "in the static
-- limit": dθ/dt at any parameters equals dθ/dt at the static parameters (`staticParams`, ρ = 0)
-- with the same β, γ, κ. Both are required. -/

@[sa_reference "VolzMeyersEquations.staticThetaEq-a"]
def T : Prop :=
  (∀ (s : VMState) (β γ κ ρ₁ ρ₂ : ℚ) (hβ : 0 < β) (hγ : 0 < γ) (h₁ : 0 ≤ ρ₁) (h₂ : 0 ≤ ρ₂),
    s.dθ (VMParams.mk β γ ρ₁ κ hβ hγ h₁) = s.dθ (VMParams.mk β γ ρ₂ κ hβ hγ h₂)) ∧
  (∀ (s : VMState) (p : VMParams),
    s.dθ p = s.dθ (staticParams p.β p.γ p.κ p.β_pos p.γ_pos))

/-- S1: dθ/dt is the same for any two swap rates ρ₁, ρ₂ (other parameters fixed). -/
@[sa_shadow "VolzMeyersEquations.staticThetaEq-a" 1]
def S1 : Prop :=
  ∀ (s : VMState) (β γ κ ρ₁ ρ₂ : ℚ) (hβ : 0 < β) (hγ : 0 < γ) (h₁ : 0 ≤ ρ₁) (h₂ : 0 ≤ ρ₂),
    s.dθ (VMParams.mk β γ ρ₁ κ hβ hγ h₁) = s.dθ (VMParams.mk β γ ρ₂ κ hβ hγ h₂)

/-- S2: dθ/dt at any parameters equals dθ/dt in the static limit (ρ = 0, same β, γ, κ). -/
@[sa_shadow "VolzMeyersEquations.staticThetaEq-a" 2]
def S2 : Prop :=
  ∀ (s : VMState) (p : VMParams),
    s.dθ p = s.dθ (staticParams p.β p.γ p.κ p.β_pos p.γ_pos)

@[sa_ref_forward "VolzMeyersEquations.staticThetaEq-a" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "VolzMeyersEquations.staticThetaEq-a" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "VolzMeyersEquations.staticThetaEq-a"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.VolzMeyersEquations.staticThetaEq_a

namespace Alignment.Shadows.VolzMeyersEquations.fastMixingP1Equilibrium_a

open Alignment.Shadows.VolzMeyersEquations

/-! ### `VolzMeyersEquations.fastMixingP1Equilibrium-a`
Blind text: "**VM6.** In the fast-mixing limit, P₁ → M₁"

-- AMBIGUITY: "fast-mixing limit" is ρ → ∞; "P₁ → M₁" read as quasi-equilibrium convergence of
-- the header-table P₁-equation (as in table.VM6 S1). A trajectory (singular-perturbation) reading
-- is not formalised.
-- VOCAB-GAP: no operation for Ṗ₁ (`rateP1` is built from the header table and `excessRatio`). -/

@[sa_reference "VolzMeyersEquations.fastMixingP1Equilibrium-a"]
def T : Prop :=
  ∀ (s : VMState) (β γ κ : ℚ) (hβ : 0 < β) (hγ : 0 < γ) (ε : ℝ), 0 < ε →
    ∃ R : ℚ, ∀ (ρ : ℚ) (hρ : 0 ≤ ρ), R < ρ → ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      rateP1 s (VMParams.mk β γ ρ κ hβ hγ hρ) x = 0 → |x - (s.M₁ : ℝ)| < ε

/-- S1: as ρ → ∞, admissible equilibria of the P₁-equation converge to M₁. -/
@[sa_shadow "VolzMeyersEquations.fastMixingP1Equilibrium-a" 1]
def S1 : Prop :=
  ∀ (s : VMState) (β γ κ : ℚ) (hβ : 0 < β) (hγ : 0 < γ) (ε : ℝ), 0 < ε →
    ∃ R : ℚ, ∀ (ρ : ℚ) (hρ : 0 ≤ ρ), R < ρ → ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      rateP1 s (VMParams.mk β γ ρ κ hβ hγ hρ) x = 0 → |x - (s.M₁ : ℝ)| < ε

@[sa_ref_forward "VolzMeyersEquations.fastMixingP1Equilibrium-a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "VolzMeyersEquations.fastMixingP1Equilibrium-a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.VolzMeyersEquations.fastMixingP1Equilibrium_a

/-! ## VM7 (initial conditions) -/

namespace Alignment.Shadows.VolzMeyersEquations.icEdgePartition

/-! ### `VolzMeyersEquations.icEdgePartition`
Blind text: "**VM7.** IC consistency: the edge partition holds at t=0."

"The edge partition" is VM2's "P₁ + P_S + P_R = 1"; the state at t = 0 is
`vmInitialState sf` ("Standard VM initial conditions with node-level seed fraction sf").
-- AMBIGUITY: no restriction on sf is stated: every seed fraction sf. "Partition" is taken in
-- VM2's sense (the sum), not as additionally requiring each part to be nonnegative. -/

@[sa_reference "VolzMeyersEquations.icEdgePartition"]
def T : Prop :=
  ∀ sf : ℚ, (vmInitialState sf).P₁ + (vmInitialState sf).P_S + (vmInitialState sf).P_R = 1

/-- S1: the standard initial state satisfies P₁ + P_S + P_R = 1 for every seed fraction. -/
@[sa_shadow "VolzMeyersEquations.icEdgePartition" 1]
def S1 : Prop :=
  ∀ sf : ℚ, (vmInitialState sf).P₁ + (vmInitialState sf).P_S + (vmInitialState sf).P_R = 1

@[sa_ref_forward "VolzMeyersEquations.icEdgePartition" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "VolzMeyersEquations.icEdgePartition"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.VolzMeyersEquations.icEdgePartition

namespace Alignment.Shadows.VolzMeyersEquations.icPopulation

/-! ### `VolzMeyersEquations.icPopulation`
Blind text: "**VM7b.** IC consistency: I(0) + R(0) = sf."

I(0), R(0) are the fields `I`, `R` of `vmInitialState sf`; every seed fraction sf. -/

@[sa_reference "VolzMeyersEquations.icPopulation"]
def T : Prop := ∀ sf : ℚ, (vmInitialState sf).I + (vmInitialState sf).R = sf

/-- S1: the standard initial state has I + R equal to the seed fraction. -/
@[sa_shadow "VolzMeyersEquations.icPopulation" 1]
def S1 : Prop := ∀ sf : ℚ, (vmInitialState sf).I + (vmInitialState sf).R = sf

@[sa_ref_forward "VolzMeyersEquations.icPopulation" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "VolzMeyersEquations.icPopulation"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.VolzMeyersEquations.icPopulation

namespace Alignment.Shadows.VolzMeyersEquations.icTheta

/-! ### `VolzMeyersEquations.icTheta`
Blind text: "**VM7c.** IC consistency: θ(0) = 1 (no transmission at t=0)."

θ(0) is the field `θ` of `vmInitialState sf`; every seed fraction sf. The parenthesis is the
interpretation of θ = 1. -/

@[sa_reference "VolzMeyersEquations.icTheta"]
def T : Prop := ∀ sf : ℚ, (vmInitialState sf).θ = 1

/-- S1: the standard initial state has θ = 1. -/
@[sa_shadow "VolzMeyersEquations.icTheta" 1]
def S1 : Prop := ∀ sf : ℚ, (vmInitialState sf).θ = 1

@[sa_ref_forward "VolzMeyersEquations.icTheta" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "VolzMeyersEquations.icTheta"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.VolzMeyersEquations.icTheta

namespace Alignment.Shadows.VolzMeyersEquations.massActionIncidence_b

/-! ### `VolzMeyersEquations.massActionIncidence-b`
Blind text: "We verify that the incidence = β·P₁·θ·κ = β·I·S when κ=1 and P₁=I, θ=S."

"the incidence" is the operation `VMState.incidence`, whose docstring is "Incidence = β·P₁·θ·κ";
the middle term of the chain is that definition (a bridge matter), and the claim is
incidence = β·I·S under κ = 1, P₁ = I, with S := θ.
-- AMBIGUITY: "θ=S" read as naming S (S := θ) rather than as a constraint on an independent S. -/

@[sa_reference "VolzMeyersEquations.massActionIncidence-b"]
def T : Prop :=
  ∀ (s : VMState) (p : VMParams), p.κ = 1 → s.P₁ = s.I → s.incidence p = p.β * s.I * s.θ

/-- S1: with κ = 1 and P₁ = I, the incidence equals β·I·S (S = θ). -/
@[sa_shadow "VolzMeyersEquations.massActionIncidence-b" 1]
def S1 : Prop :=
  ∀ (s : VMState) (p : VMParams), p.κ = 1 → s.P₁ = s.I → s.incidence p = p.β * s.I * s.θ

@[sa_ref_forward "VolzMeyersEquations.massActionIncidence-b" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "VolzMeyersEquations.massActionIncidence-b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.VolzMeyersEquations.massActionIncidence_b

noncomputable section

/-! ## `VolzMeyersEquations.fastMixingP1Equilibrium-b` (blind)

Text: "and P_S → ψ'(θ)/ψ'(1)."

In the fast-mixing limit ρ → ∞ (context: Result on the fast-mixing equilibrium). The P_S equation of
the module table is `Ṗ_S = β P_S P₁ (1 − θψ″(θ)/ψ′(θ)) + ρ(ψ′(θ)/ψ′(1) − P_S)`. For fixed θ and P₁
write `a = θψ″(θ)/ψ′(θ)` and `c = ψ′(θ)/ψ′(1)`; the fast equilibrium `P_S(ρ)` (zero of the P_S
right-hand side) tends to `c` as ρ → ∞. -/
namespace Alignment.Shadows.VolzMeyersEquations.fastMixingP1Equilibrium_b

open Filter Topology

@[sa_reference "VolzMeyersEquations.fastMixingP1Equilibrium-b"]
def T : Prop :=
  ∀ (p : VMParams) (s : VMState) (a c : ℝ) (P : ℝ → ℝ),
    (∀ ρ : ℝ, 0 < ρ → (p.β : ℝ) * P ρ * s.P₁ * (1 - a) + ρ * (c - P ρ) = 0) →
    Tendsto P atTop (𝓝 c)

/-- S1: the fast equilibrium of P_S tends to ψ′(θ)/ψ′(1) as ρ → ∞. -/
@[sa_shadow "VolzMeyersEquations.fastMixingP1Equilibrium-b" 1]
def S1 : Prop :=
  ∀ (p : VMParams) (s : VMState) (a c : ℝ) (P : ℝ → ℝ),
    (∀ ρ : ℝ, 0 < ρ → (p.β : ℝ) * P ρ * s.P₁ * (1 - a) + ρ * (c - P ρ) = 0) →
    Tendsto P atTop (𝓝 c)

@[sa_ref_forward "VolzMeyersEquations.fastMixingP1Equilibrium-b" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t
@[sa_complete "VolzMeyersEquations.fastMixingP1Equilibrium-b"] theorem complete (s1 : S1) : T :=
  s1

end Alignment.Shadows.VolzMeyersEquations.fastMixingP1Equilibrium_b

/-! ## `VolzMeyersEquations.fastMixingP1Equilibrium-d` (re-authored blind)

Text: "Motivated by: the swap terms ρ(M₁ − P₁) and ρ(ψ'(θ)/ψ'(1) − P_S) drive P₁ and P_S to their
population-level values at rate ρ. The Lean statement is only that the swap term ρ(M₁ − P₁) vanishes
when P₁ = M₁; no limit ρ → ∞ is formalised."

"Drive ... at rate ρ": under the swap term alone (`Ṗ = ρ(target − P)`, target fixed) the
deviation from the target decays as `e^{−ρt}` (S1 for P₁ → M₁, S2 for P_S → ψ′(θ)/ψ′(1)). The rest
describes the Lean statement. -/
namespace Alignment.Shadows.VolzMeyersEquations.fastMixingP1Equilibrium_d

@[sa_reference "VolzMeyersEquations.fastMixingP1Equilibrium-d"]
def T : Prop :=
  (∀ (p : VMParams) (s : VMState) (P : ℝ → ℝ),
      (∀ t, HasDerivAt P ((p.ρ : ℝ) * ((s.M₁ : ℝ) - P t)) t) →
      ∀ t, P t - s.M₁ = (P 0 - s.M₁) * Real.exp (-(p.ρ : ℝ) * t)) ∧
  (∀ (p : VMParams) (c : ℝ) (P : ℝ → ℝ), (∀ t, HasDerivAt P ((p.ρ : ℝ) * (c - P t)) t) →
      ∀ t, P t - c = (P 0 - c) * Real.exp (-(p.ρ : ℝ) * t))

/-- S1: the swap term drives P₁ to M₁ at rate ρ. -/
@[sa_shadow "VolzMeyersEquations.fastMixingP1Equilibrium-d" 1]
def S1 : Prop :=
  ∀ (p : VMParams) (s : VMState) (P : ℝ → ℝ),
    (∀ t, HasDerivAt P ((p.ρ : ℝ) * ((s.M₁ : ℝ) - P t)) t) →
    ∀ t, P t - s.M₁ = (P 0 - s.M₁) * Real.exp (-(p.ρ : ℝ) * t)
/-- S2: the swap term drives P_S to ψ′(θ)/ψ′(1) at rate ρ. -/
@[sa_shadow "VolzMeyersEquations.fastMixingP1Equilibrium-d" 2]
def S2 : Prop :=
  ∀ (p : VMParams) (c : ℝ) (P : ℝ → ℝ), (∀ t, HasDerivAt P ((p.ρ : ℝ) * (c - P t)) t) →
    ∀ t, P t - c = (P 0 - c) * Real.exp (-(p.ρ : ℝ) * t)

@[sa_ref_forward "VolzMeyersEquations.fastMixingP1Equilibrium-d" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "VolzMeyersEquations.fastMixingP1Equilibrium-d" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "VolzMeyersEquations.fastMixingP1Equilibrium-d"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.VolzMeyersEquations.fastMixingP1Equilibrium_d

/-! ## `VolzMeyersEquations.header.popIEquation` (blind)

Text: "| pop_I | = β P₁ θ ψ'(θ) − γ pop_I | [...] The Lean incidence β·P₁·θ·κ. The Volz–Meyers
incidence is β·P₁·θ·ψ'(θ); for Poisson, ψ'(θ) = κ·ψ(θ), so it is β·P₁·θ·κ·ψ(θ). This definition
drops the factor ψ(θ) and agrees with the model only while ψ(θ) = 1, i.e. at θ = 1."

S1: `d pop_I/dt = incidence − γ pop_I` (`VMState.dI`); S2: the Lean incidence is `β P₁ θ κ`
(`VMState.incidence`); S3: for Poisson ψ(θ) = e^{κ(θ−1)}, it equals the model incidence
`β P₁ θ κ ψ(θ)` iff θ = 1 (when β P₁ θ κ ≠ 0, κ > 0). -/
namespace Alignment.Shadows.VolzMeyersEquations.header_popIEquation

@[sa_reference "VolzMeyersEquations.header.popIEquation"]
def T : Prop :=
  (∀ (s : VMState) (p : VMParams), s.dI p = s.incidence p - p.γ * s.I) ∧
  (∀ (s : VMState) (p : VMParams), s.incidence p = p.β * s.P₁ * s.θ * p.κ) ∧
  (∀ (s : VMState) (p : VMParams), 0 < p.κ → s.P₁ ≠ 0 → s.θ ≠ 0 →
      (((s.incidence p : ℚ) : ℝ) =
          (p.β : ℝ) * s.P₁ * s.θ * p.κ * Real.exp ((p.κ : ℝ) * ((s.θ : ℝ) - 1)) ↔ s.θ = 1))

/-- S1: `d pop_I/dt = incidence − γ pop_I`. -/
@[sa_shadow "VolzMeyersEquations.header.popIEquation" 1]
def S1 : Prop := ∀ (s : VMState) (p : VMParams), s.dI p = s.incidence p - p.γ * s.I
/-- S2: the Lean incidence is `β P₁ θ κ`. -/
@[sa_shadow "VolzMeyersEquations.header.popIEquation" 2]
def S2 : Prop := ∀ (s : VMState) (p : VMParams), s.incidence p = p.β * s.P₁ * s.θ * p.κ
/-- S3: it agrees with the Poisson model incidence exactly at θ = 1. -/
@[sa_shadow "VolzMeyersEquations.header.popIEquation" 3]
def S3 : Prop :=
  ∀ (s : VMState) (p : VMParams), 0 < p.κ → s.P₁ ≠ 0 → s.θ ≠ 0 →
    (((s.incidence p : ℚ) : ℝ) =
        (p.β : ℝ) * s.P₁ * s.θ * p.κ * Real.exp ((p.κ : ℝ) * ((s.θ : ℝ) - 1)) ↔ s.θ = 1)

@[sa_ref_forward "VolzMeyersEquations.header.popIEquation" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "VolzMeyersEquations.header.popIEquation" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "VolzMeyersEquations.header.popIEquation" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2
@[sa_complete "VolzMeyersEquations.header.popIEquation"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.VolzMeyersEquations.header_popIEquation

/-! ## `VolzMeyersEquations.massActionIncidence-a` (re-authored blind)

Text: "**VM8.** For a homogeneous network with ψ(x) = x (every node has degree 1, κ=1), the VM model
reduces to the standard SIR in the fast-mixing limit ρ → ∞. At ρ = 0 it describes isolated pairs,
not mass action. In the fast-mixing limit: S = θ, P₁ = I, and the equations become
dS/dt = −β·I·S, dI/dt = β·I·S − γ·I, dR/dt = γ·I."

With S = ψ(θ) = θ and P₁ = I, the module's rates (`dθ`, `dI`, `dR`, κ = 1) are the SIR rates
(split into its three equations). S4: for ψ(x) = x the population stub
fraction M₁ has the same rate as I when M₁ = I (`Ṁ₁ = −γM₁ + βP₁θ`), which is why P₁ = M₁ becomes
P₁ = I. The ρ = 0 remark (isolated pairs) is qualitative and not formalised. -/
namespace Alignment.Shadows.VolzMeyersEquations.massActionIncidence_a

@[sa_reference "VolzMeyersEquations.massActionIncidence-a"]
def T : Prop :=
  (∀ (s : VMState) (p : VMParams), s.P₁ = s.I → s.dθ p = -p.β * s.I * s.θ) ∧
  (∀ (s : VMState) (p : VMParams), p.κ = 1 → s.P₁ = s.I →
      s.dI p = p.β * s.I * s.θ - p.γ * s.I) ∧
  (∀ (s : VMState) (p : VMParams), s.dR p = p.γ * s.I) ∧
  (∀ (s : VMState) (p : VMParams), p.κ = 1 → s.M₁ = s.I →
      -p.γ * s.M₁ + p.β * s.P₁ * s.θ = s.dI p)

/-- S1: dS/dt = −β I S (S = θ, P₁ = I). -/
@[sa_shadow "VolzMeyersEquations.massActionIncidence-a" 1]
def S1 : Prop := ∀ (s : VMState) (p : VMParams), s.P₁ = s.I → s.dθ p = -p.β * s.I * s.θ
/-- S2: dI/dt = β I S − γ I. -/
@[sa_shadow "VolzMeyersEquations.massActionIncidence-a" 2]
def S2 : Prop :=
  ∀ (s : VMState) (p : VMParams), p.κ = 1 → s.P₁ = s.I → s.dI p = p.β * s.I * s.θ - p.γ * s.I
/-- S3: dR/dt = γ I. -/
@[sa_shadow "VolzMeyersEquations.massActionIncidence-a" 3]
def S3 : Prop := ∀ (s : VMState) (p : VMParams), s.dR p = p.γ * s.I
/-- S4: for ψ(x) = x, M₁ follows the same rate as I. -/
@[sa_shadow "VolzMeyersEquations.massActionIncidence-a" 4]
def S4 : Prop :=
  ∀ (s : VMState) (p : VMParams), p.κ = 1 → s.M₁ = s.I → -p.γ * s.M₁ + p.β * s.P₁ * s.θ = s.dI p

@[sa_ref_forward "VolzMeyersEquations.massActionIncidence-a" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "VolzMeyersEquations.massActionIncidence-a" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "VolzMeyersEquations.massActionIncidence-a" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "VolzMeyersEquations.massActionIncidence-a" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2
@[sa_complete "VolzMeyersEquations.massActionIncidence-a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.VolzMeyersEquations.massActionIncidence_a

/-! ## `VolzMeyersEquations.populationInflux-b` (blind)

Text: "This is the influx of newly infected from the susceptible pool, with the Lean incidence
(which drops the factor ψ(θ); see `VMState.incidence`)."

S1: the Lean incidence is κ times the stub-level outflow `−θ̇` (the influx with the factor ψ(θ)
dropped); S2: for Poisson ψ(θ) = e^{κ(θ−1)}, the influx `−d/dt ψ(θ)` from the susceptible pool is
ψ(θ) times the Lean incidence. -/
namespace Alignment.Shadows.VolzMeyersEquations.populationInflux_b

@[sa_reference "VolzMeyersEquations.populationInflux-b"]
def T : Prop :=
  (∀ (s : VMState) (p : VMParams), s.incidence p = -(p.κ * s.dθ p)) ∧
  (∀ (p : VMParams) (θ P₁ : ℝ → ℝ) (t : ℝ),
      HasDerivAt θ (-(p.β : ℝ) * P₁ t * θ t) t →
      HasDerivAt (fun r => Real.exp ((p.κ : ℝ) * (θ r - 1)))
        (-(Real.exp ((p.κ : ℝ) * (θ t - 1)) * ((p.β : ℝ) * P₁ t * θ t * p.κ))) t)

/-- S1: the Lean incidence is `−κ θ̇`. -/
@[sa_shadow "VolzMeyersEquations.populationInflux-b" 1]
def S1 : Prop := ∀ (s : VMState) (p : VMParams), s.incidence p = -(p.κ * s.dθ p)
/-- S2: the true influx is ψ(θ) times the Lean incidence (Poisson). -/
@[sa_shadow "VolzMeyersEquations.populationInflux-b" 2]
def S2 : Prop :=
  ∀ (p : VMParams) (θ P₁ : ℝ → ℝ) (t : ℝ),
    HasDerivAt θ (-(p.β : ℝ) * P₁ t * θ t) t →
    HasDerivAt (fun r => Real.exp ((p.κ : ℝ) * (θ r - 1)))
      (-(Real.exp ((p.κ : ℝ) * (θ t - 1)) * ((p.β : ℝ) * P₁ t * θ t * p.κ))) t

@[sa_ref_forward "VolzMeyersEquations.populationInflux-b" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "VolzMeyersEquations.populationInflux-b" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "VolzMeyersEquations.populationInflux-b"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.VolzMeyersEquations.populationInflux_b

/-! ## `VolzMeyersEquations.sNonincreasing-b` (re-authored blind)

Text: "Motivated by: dS/dt = κ·S·dθ/dt ≤ 0 when κ > 0. The Lean statement is only κ·dθ/dt ≤ 0 (the
factor S ≥ 0 is omitted); nothing is proved about S along solutions."

S1: for Poisson S = e^{κ(θ−1)}, dS/dt = κ·S·dθ/dt along θ̇ = −βP₁θ; S2: κ·S·dθ/dt ≤ 0 for κ > 0,
S ≥ 0, P₁ ≥ 0, θ ≥ 0 (with `VMState.dθ`). The rest describes the Lean statement. -/
namespace Alignment.Shadows.VolzMeyersEquations.sNonincreasing_b

@[sa_reference "VolzMeyersEquations.sNonincreasing-b"]
def T : Prop :=
  (∀ (p : VMParams) (θ P₁ : ℝ → ℝ) (t : ℝ), HasDerivAt θ (-(p.β : ℝ) * P₁ t * θ t) t →
      HasDerivAt (fun r => Real.exp ((p.κ : ℝ) * (θ r - 1)))
        ((p.κ : ℝ) * Real.exp ((p.κ : ℝ) * (θ t - 1)) * (-(p.β : ℝ) * P₁ t * θ t)) t) ∧
  (∀ (s : VMState) (p : VMParams) (S : ℚ), 0 < p.κ → 0 ≤ S → 0 ≤ s.P₁ → 0 ≤ s.θ →
      p.κ * S * s.dθ p ≤ 0)

/-- S1: dS/dt = κ S dθ/dt for Poisson S = e^{κ(θ−1)}. -/
@[sa_shadow "VolzMeyersEquations.sNonincreasing-b" 1]
def S1 : Prop :=
  ∀ (p : VMParams) (θ P₁ : ℝ → ℝ) (t : ℝ), HasDerivAt θ (-(p.β : ℝ) * P₁ t * θ t) t →
    HasDerivAt (fun r => Real.exp ((p.κ : ℝ) * (θ r - 1)))
      ((p.κ : ℝ) * Real.exp ((p.κ : ℝ) * (θ t - 1)) * (-(p.β : ℝ) * P₁ t * θ t)) t
/-- S2: κ S dθ/dt ≤ 0. -/
@[sa_shadow "VolzMeyersEquations.sNonincreasing-b" 2]
def S2 : Prop :=
  ∀ (s : VMState) (p : VMParams) (S : ℚ), 0 < p.κ → 0 ≤ S → 0 ≤ s.P₁ → 0 ≤ s.θ →
    p.κ * S * s.dθ p ≤ 0

@[sa_ref_forward "VolzMeyersEquations.sNonincreasing-b" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "VolzMeyersEquations.sNonincreasing-b" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "VolzMeyersEquations.sNonincreasing-b"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.VolzMeyersEquations.sNonincreasing_b

/-! ## `VolzMeyersEquations.table.VM6` (re-authored blind)

Text: "| VM6 | Swap term ρ(M₁ − P₁) vanishes at P₁ = M₁ (fast-mixing motivation) |" -/
namespace Alignment.Shadows.VolzMeyersEquations.table_VM6

@[sa_reference "VolzMeyersEquations.table.VM6"]
def T : Prop := ∀ (s : VMState) (p : VMParams), s.P₁ = s.M₁ → p.ρ * (s.M₁ - s.P₁) = 0

/-- S1: the swap term vanishes at P₁ = M₁. -/
@[sa_shadow "VolzMeyersEquations.table.VM6" 1]
def S1 : Prop := ∀ (s : VMState) (p : VMParams), s.P₁ = s.M₁ → p.ρ * (s.M₁ - s.P₁) = 0

@[sa_ref_forward "VolzMeyersEquations.table.VM6" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "VolzMeyersEquations.table.VM6"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.VolzMeyersEquations.table_VM6

/-! ## `VolzMeyersEquations.table.VM7` (blind)

Text: "| VM7 | IC bookkeeping: with S(0) = ψ(1) = 1, S(0) + pop_I(0) + pop_R(0) = 1 + sf |"

The initial state is `vmInitialState sf`; S(0) = ψ(θ(0)) = ψ(1) requires θ(0) = 1 (S1). -/
namespace Alignment.Shadows.VolzMeyersEquations.table_VM7

@[sa_reference "VolzMeyersEquations.table.VM7"]
def T : Prop :=
  (∀ sf : ℚ, (vmInitialState sf).θ = 1) ∧
  (∀ sf : ℚ, 1 + (vmInitialState sf).I + (vmInitialState sf).R = 1 + sf)

/-- S1: θ(0) = 1, so S(0) = ψ(1) = 1. -/
@[sa_shadow "VolzMeyersEquations.table.VM7" 1]
def S1 : Prop := ∀ sf : ℚ, (vmInitialState sf).θ = 1
/-- S2: S(0) + pop_I(0) + pop_R(0) = 1 + sf. -/
@[sa_shadow "VolzMeyersEquations.table.VM7" 2]
def S2 : Prop := ∀ sf : ℚ, 1 + (vmInitialState sf).I + (vmInitialState sf).R = 1 + sf

@[sa_ref_forward "VolzMeyersEquations.table.VM7" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "VolzMeyersEquations.table.VM7" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "VolzMeyersEquations.table.VM7"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.VolzMeyersEquations.table_VM7

/-! ## `VolzMeyersEquations.table.VM8` (re-authored blind)

Text: "| VM8 | Mass-action recovery for ψ(x)=x (k=1) in the fast-mixing limit |"

With S = θ and (fast mixing) P₁ = I, the rates are the mass-action SIR rates. -/
namespace Alignment.Shadows.VolzMeyersEquations.table_VM8

@[sa_reference "VolzMeyersEquations.table.VM8"]
def T : Prop :=
  (∀ (s : VMState) (p : VMParams), s.P₁ = s.I → s.dθ p = -p.β * s.I * s.θ) ∧
  (∀ (s : VMState) (p : VMParams), p.κ = 1 → s.P₁ = s.I →
      s.dI p = p.β * s.I * s.θ - p.γ * s.I) ∧
  (∀ (s : VMState) (p : VMParams), s.dR p = p.γ * s.I)

/-- S1: dS/dt = −β I S. -/
@[sa_shadow "VolzMeyersEquations.table.VM8" 1]
def S1 : Prop := ∀ (s : VMState) (p : VMParams), s.P₁ = s.I → s.dθ p = -p.β * s.I * s.θ
/-- S2: dI/dt = β I S − γ I. -/
@[sa_shadow "VolzMeyersEquations.table.VM8" 2]
def S2 : Prop :=
  ∀ (s : VMState) (p : VMParams), p.κ = 1 → s.P₁ = s.I → s.dI p = p.β * s.I * s.θ - p.γ * s.I
/-- S3: dR/dt = γ I. -/
@[sa_shadow "VolzMeyersEquations.table.VM8" 3]
def S3 : Prop := ∀ (s : VMState) (p : VMParams), s.dR p = p.γ * s.I

@[sa_ref_forward "VolzMeyersEquations.table.VM8" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "VolzMeyersEquations.table.VM8" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "VolzMeyersEquations.table.VM8" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "VolzMeyersEquations.table.VM8"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.VolzMeyersEquations.table_VM8

end
