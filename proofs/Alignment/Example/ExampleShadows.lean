import Alignment.Registry
import EBCMCategory.EpiCategory
import EBCMCategory.MarginalisationDynamicalGap

/-!
# Worked example: blind shadow sets (template for `Alignment/Shadows/<Group>.lean`)

A shadow author reads only the claim's entry in `claims_blind.yaml`, the group's
`Alignment/DataTypes/<Group>.md`, `Alignment/README.md`, this file and the cited source passage.
They never read theorem statements, definition bodies or checker files.

For each claim write the intended statement `T` (`@[sa_reference]`), atomic shadows
`S₁ … Sₙ` (`@[sa_shadow]`), and the completeness certificates `T → Sᵢ` (`@[sa_ref_forward]`)
and `S₁ → … → Sₙ → T` (`@[sa_complete]`). Certificates may use any tactic; they are only
required to be sorry-free. State notions in primitive terms (fields of the data types, the
opaque "operations under test" listed in `DataTypes/<Group>.md`), never through a theorem.

These example claims are registered under `EXAMPLE.*` ids (group `Example`) and excluded from
normal reports; `bash scripts/sa_pass.sh --self-test` requires both to reach SA-PASS = 1.
Because the same person wrote these shadows and the checkers, they are *weak* passes and
illustrate the mechanics only.
-/

namespace Alignment.Example.PoissonVariance

/-! ### `EXAMPLE.poissonVariance`

Blind text: "**Result 2.** For Poisson, the variance equals the mean (equidispersion)."

Data types used: `PGFData` with fields `mean` (= ψ'(1)) and `secondFactorial` (= ψ''(1)), and the
operation under test `PGFData.poisson κ hκ` ("the Poisson PGF with mean κ"). The degree
variance of a degree distribution with PGF ψ is ψ''(1) + ψ'(1) − ψ'(1)², written below in
primitive terms. -/

/-- Degree variance of the distribution with PGF data `ψ`, in primitive terms:
Var(k) = ψ''(1) + ψ'(1)·(1 − ψ'(1)). -/
def degVar (ψ : PGFData) : ℚ := ψ.secondFactorial + ψ.mean * (1 - ψ.mean)

-- AMBIGUITY: "the variance equals the mean" -- "the mean" may be read as the parameter κ of
-- the Poisson distribution or as the mean ψ'(1) of the PGF; both readings are required (S1, S2).

/-- Intended statement: for every mean κ > 0, the Poisson degree distribution with mean κ has
degree variance equal to κ and equal to its PGF mean ψ'(1). -/
@[sa_reference "EXAMPLE.poissonVariance"]
def T : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ),
    degVar (PGFData.poisson κ hκ) = κ ∧
      degVar (PGFData.poisson κ hκ) = (PGFData.poisson κ hκ).mean

/-- S1: the variance equals the mean parameter κ. -/
@[sa_shadow "EXAMPLE.poissonVariance" 1]
def S1 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ), degVar (PGFData.poisson κ hκ) = κ

/-- S2: the variance equals the PGF mean ψ'(1). -/
@[sa_shadow "EXAMPLE.poissonVariance" 2]
def S2 : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ), degVar (PGFData.poisson κ hκ) = (PGFData.poisson κ hκ).mean

@[sa_ref_forward "EXAMPLE.poissonVariance" 1]
theorem ref_fwd1 : T → S1 := fun t κ hκ => (t κ hκ).1

@[sa_ref_forward "EXAMPLE.poissonVariance" 2]
theorem ref_fwd2 : T → S2 := fun t κ hκ => (t κ hκ).2

@[sa_complete "EXAMPLE.poissonVariance"]
theorem complete (s1 : S1) (s2 : S2) : T := fun κ hκ => ⟨s1 κ hκ, s2 κ hκ⟩

end Alignment.Example.PoissonVariance

namespace Alignment.Example.Transmissibility

/-! ### `EXAMPLE.transmissibilityRange`

Blind text: "Transmissibility is positive." [...] "Transmissibility is less than 1."

Data types used: `SIRParams` with fields `β`, `γ` (rates) and the invariants `0 < β`, `0 < γ`;
the text's transmissibility across a single edge is T = β/(β+γ) (written in primitive terms). -/

/-- Intended statement: for all SIR parameters, 0 < β/(β+γ) < 1. -/
@[sa_reference "EXAMPLE.transmissibilityRange"]
def T : Prop := ∀ p : SIRParams, 0 < p.β / (p.β + p.γ) ∧ p.β / (p.β + p.γ) < 1

/-- S1: transmissibility is positive. -/
@[sa_shadow "EXAMPLE.transmissibilityRange" 1]
def S1 : Prop := ∀ p : SIRParams, 0 < p.β / (p.β + p.γ)

/-- S2: transmissibility is less than one. -/
@[sa_shadow "EXAMPLE.transmissibilityRange" 2]
def S2 : Prop := ∀ p : SIRParams, p.β / (p.β + p.γ) < 1

@[sa_ref_forward "EXAMPLE.transmissibilityRange" 1]
theorem ref_fwd1 : T → S1 := fun t p => (t p).1

@[sa_ref_forward "EXAMPLE.transmissibilityRange" 2]
theorem ref_fwd2 : T → S2 := fun t p => (t p).2

@[sa_complete "EXAMPLE.transmissibilityRange"]
theorem complete (s1 : S1) (s2 : S2) : T := fun p => ⟨s1 p, s2 p⟩

end Alignment.Example.Transmissibility

namespace Alignment.Example.TrajectoryGap

open EBCMCategory.Marginalisation

/-! ### `EXAMPLE.trajectoryGapZero` (universe-polymorphic statement)

Blind text: "The trajectory gap vanishes at `t = 0`."

Data types used: normed real vector spaces `V₄`, `V₃`, a continuous linear map `M : V₄ →L[ℝ] V₃`,
vector fields `F₄`, `F₃` with flows `φ₄`, `φ₃` (operation under test `IsFlow F φ`: `φ v 0 = v`
and `t ↦ φ v t` solves `F`); the trajectory gap at time `t` is `M (φ₄ u t) − φ₃ (M u) t`.
The spaces live in arbitrary universes, so the shadows are universe polymorphic. -/

universe u v

/-- Intended statement: for flows of any two vector fields, the gap at time 0 is zero. -/
@[sa_reference "EXAMPLE.trajectoryGapZero"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ w : V₄, M (φ₄ w 0) - φ₃ (M w) 0 = 0

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "EXAMPLE.trajectoryGapZero" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ w : V₄, M (φ₄ w 0) - φ₃ (M w) 0 = 0

@[sa_ref_forward "EXAMPLE.trajectoryGapZero" 1]
theorem ref_fwd1 : T.{u, v} → S1.{u, v} := fun t => t

@[sa_complete "EXAMPLE.trajectoryGapZero"]
theorem complete (s1 : S1.{u, v}) : T.{u, v} := s1

end Alignment.Example.TrajectoryGap
