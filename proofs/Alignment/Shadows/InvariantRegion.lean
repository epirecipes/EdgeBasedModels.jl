import Alignment.Registry
import EBCMCategory.InvariantRegion
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Blind shadow sets for group `InvariantRegion`

Written blind: the author read only `Alignment/README.md`, `SA-PASS_SKILL.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/InvariantRegion.md` and the
`claims_blind.yaml` entries of this group (id, group, source, text).

Vocabulary (DataTypes): `PolyPGF n` (a PGF ψ(x) = Σᵢ pᵢ xⁱ with nonnegative coefficients
summing to 1), `PolyPGF.eval` (evaluate ψ at x), `EBCMParams` (β, γ > 0) and `EBCMRegion`
("the invariant region": θ ∈ [0, 1], φ_I ≥ 0, φ_R ≥ 0, R ≥ 0). Everything is over `ℚ`.

VOCAB-GAP (module-wide): the DataTypes provide no Lean notion of ψ′, of the EBCM vector
field, of the observables S = ψ(θ) and I = 1 − S − R, of ODE solutions or of invariance.
Following the DataTypes guidance these are written below as explicit expressions, taken from
the module header's prose description of the model (claim `InvariantRegion.header.model`):

* dθ/dt   = −β φ_I
* dφ_I/dt = (β φ_I / θ)(ψ′(θ)/ψ′(1)) − (β + γ) φ_I
* dφ_R/dt = γ φ_I
* dR/dt   = γ (1 − ψ(θ) − R)
* S = ψ(θ), I = 1 − S − R, hence (chain rule) dI/dt = −ψ′(θ)·dθ/dt − dR/dt.

Division is Lean's total division on `ℚ` (x / 0 = 0). Trajectory statements (only in
`R123b`) are stated for real-valued functions of time with `HasDerivAt`.

Re-authored blind (second pass, from the current claim texts only): the blocks after
`end Alignment.Shadows.InvariantRegion` (namespace `Shared2` and the claims `R117a`,
`R120b.guard`, `R123a`, `R123c`, `header.faceConditions`, `header.invariance.*`, `header.model`,
`header.thetaFace.b/c`, `phiIDotFactors.b`, `phiIDotCorrect*`, `phiILeTheta`). The current model
text gives the correct φ_I field β φ_I ψ″(θ)/ψ′(1) − (β + γ) φ_I; those blocks use it (and the
1/θ form only where the text speaks of it). Not formalised in that pass: `R123g` and
`header.nagumoConditional` (remarks that Nagumo's theorem is not formalised and no invariance
theorem is stated).
-/

open scoped BigOperators
open InvariantRegion

namespace Alignment.Shadows.InvariantRegion

/-! ## Shared primitive notions (alignment helpers, not claims) -/

/-- VOCAB-GAP: ψ′(x), the derivative of the PGF ψ(x) = Σᵢ pᵢ xⁱ, written as the formal
derivative Σᵢ i·pᵢ·x^(i−1) (the `i = 0` term is 0 because of the factor `i`). -/
def pgfDeriv {n : ℕ} (ψ : PolyPGF n) (x : ℚ) : ℚ :=
  ∑ i : Fin n, ((i : ℕ) : ℚ) * ψ.coeffs i * x ^ ((i : ℕ) - 1)

/-- VOCAB-GAP: the φ_I component of the EBCM vector field (module header):
dφ_I/dt = (β φ_I / θ)(ψ′(θ)/ψ′(1)) − (β + γ) φ_I. -/
def phiIDot (p : EBCMParams) {n : ℕ} (ψ : PolyPGF n) (θ φI : ℚ) : ℚ :=
  (p.β * φI / θ) * (pgfDeriv ψ θ / pgfDeriv ψ 1) - (p.β + p.γ) * φI

/-- VOCAB-GAP: the R component of the EBCM vector field (module header):
dR/dt = γ (1 − ψ(θ) − R). -/
def RDot (p : EBCMParams) {n : ℕ} (ψ : PolyPGF n) (θ R : ℚ) : ℚ :=
  p.γ * (1 - ψ.eval θ - R)

/-- VOCAB-GAP: the population-level drift dI/dt of the observable I = 1 − ψ(θ) − R along
the EBCM vector field, by the chain rule: dI/dt = −ψ′(θ)·(dθ/dt) − dR/dt with
dθ/dt = −β φ_I and dR/dt = γ (1 − ψ(θ) − R). -/
def IDot (p : EBCMParams) {n : ℕ} (ψ : PolyPGF n) (θ φI R : ℚ) : ℚ :=
  -(pgfDeriv ψ θ * (-p.β * φI)) - RDot p ψ θ R

/-! ## `InvariantRegion.pgfEvalOne`

Text: "ψ(1) = 1: the PGF evaluated at 1 gives total probability mass." -/
namespace pgfEvalOne

-- AMBIGUITY: "gives total probability mass" read as an additional assertion that ψ(1) equals
-- the total probability mass Σᵢ pᵢ (S2), besides ψ(1) = 1 (S1).

/-- Intended statement: for every PGF ψ, ψ(1) = 1 and ψ(1) = Σᵢ pᵢ. -/
@[sa_reference "InvariantRegion.pgfEvalOne"]
def T : Prop :=
  ∀ (n : ℕ) (ψ : PolyPGF n), ψ.eval 1 = 1 ∧ ψ.eval 1 = ∑ i : Fin n, ψ.coeffs i

/-- S1: ψ(1) = 1 for every PGF. -/
@[sa_shadow "InvariantRegion.pgfEvalOne" 1]
def S1 : Prop := ∀ (n : ℕ) (ψ : PolyPGF n), ψ.eval 1 = 1

/-- S2: ψ(1) is the total probability mass Σᵢ pᵢ. -/
@[sa_shadow "InvariantRegion.pgfEvalOne" 2]
def S2 : Prop := ∀ (n : ℕ) (ψ : PolyPGF n), ψ.eval 1 = ∑ i : Fin n, ψ.coeffs i

@[sa_ref_forward "InvariantRegion.pgfEvalOne" 1]
theorem ref_fwd1 : T → S1 := fun t n ψ => (t n ψ).1
@[sa_ref_forward "InvariantRegion.pgfEvalOne" 2]
theorem ref_fwd2 : T → S2 := fun t n ψ => (t n ψ).2

@[sa_complete "InvariantRegion.pgfEvalOne"]
theorem complete (s1 : S1) (s2 : S2) : T := fun n ψ => ⟨s1 n ψ, s2 n ψ⟩

end pgfEvalOne

/-! ## `InvariantRegion.R113`

Text: "**Result 113.** ψ(x) ≥ 0 for all x ∈ [0, 1]." -/
namespace R113

/-- Intended statement: every PGF is nonnegative on [0, 1]. -/
@[sa_reference "InvariantRegion.R113"]
def T : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (x : ℚ), 0 ≤ x → x ≤ 1 → 0 ≤ ψ.eval x

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "InvariantRegion.R113" 1]
def S1 : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (x : ℚ), 0 ≤ x → x ≤ 1 → 0 ≤ ψ.eval x

@[sa_ref_forward "InvariantRegion.R113" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "InvariantRegion.R113"]
theorem complete (s1 : S1) : T := s1

end R113

/-! ## `InvariantRegion.R114`

Text: "**Result 114.** ψ(x) ≤ 1 for all x ∈ [0, 1]." -/
namespace R114

/-- Intended statement: every PGF is at most 1 on [0, 1]. -/
@[sa_reference "InvariantRegion.R114"]
def T : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (x : ℚ), 0 ≤ x → x ≤ 1 → ψ.eval x ≤ 1

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "InvariantRegion.R114" 1]
def S1 : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (x : ℚ), 0 ≤ x → x ≤ 1 → ψ.eval x ≤ 1

@[sa_ref_forward "InvariantRegion.R114" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "InvariantRegion.R114"]
theorem complete (s1 : S1) : T := s1

end R114

/-! ## `InvariantRegion.R115`

Text: "**Result 115.** S = ψ(θ) ∈ [0, 1] whenever θ ∈ [0, 1]." -/
namespace R115

/-- Intended statement: for every PGF ψ and θ ∈ [0, 1], 0 ≤ ψ(θ) ≤ 1. -/
@[sa_reference "InvariantRegion.R115"]
def T : Prop :=
  ∀ (n : ℕ) (ψ : PolyPGF n) (θ : ℚ), 0 ≤ θ → θ ≤ 1 → 0 ≤ ψ.eval θ ∧ ψ.eval θ ≤ 1

/-- S1: lower bound S ≥ 0. -/
@[sa_shadow "InvariantRegion.R115" 1]
def S1 : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (θ : ℚ), 0 ≤ θ → θ ≤ 1 → 0 ≤ ψ.eval θ

/-- S2: upper bound S ≤ 1. -/
@[sa_shadow "InvariantRegion.R115" 2]
def S2 : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (θ : ℚ), 0 ≤ θ → θ ≤ 1 → ψ.eval θ ≤ 1

@[sa_ref_forward "InvariantRegion.R115" 1]
theorem ref_fwd1 : T → S1 := fun t n ψ θ h0 h1 => (t n ψ θ h0 h1).1
@[sa_ref_forward "InvariantRegion.R115" 2]
theorem ref_fwd2 : T → S2 := fun t n ψ θ h0 h1 => (t n ψ θ h0 h1).2

@[sa_complete "InvariantRegion.R115"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun n ψ θ h0 h1 => ⟨s1 n ψ θ h0 h1, s2 n ψ θ h0 h1⟩

end R115

/-! ## `InvariantRegion.R116a`

Text: "**Result 116.** dθ/dt = −β φ_I ≤ 0 when φ_I ≥ 0." -/
namespace R116a

-- The equation dθ/dt = −β φ_I is the model's definition (no Lean definition exists), so the
-- checkable content is the sign statement −β φ_I ≤ 0 for φ_I ≥ 0, β the transmission rate.

/-- Intended statement: for all SIR rates and φ_I ≥ 0, −β φ_I ≤ 0. -/
@[sa_reference "InvariantRegion.R116a"]
def T : Prop := ∀ (p : EBCMParams) (φI : ℚ), 0 ≤ φI → -p.β * φI ≤ 0

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "InvariantRegion.R116a" 1]
def S1 : Prop := ∀ (p : EBCMParams) (φI : ℚ), 0 ≤ φI → -p.β * φI ≤ 0

@[sa_ref_forward "InvariantRegion.R116a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "InvariantRegion.R116a"]
theorem complete (s1 : S1) : T := s1

end R116a

/-! ## `InvariantRegion.phiIDotFactors.a`

Text: "More general: when φ_I ≥ 0, the φ_I-derivative factors as φ_I × (something), [...]
Concretely, for θ > 0 the derivative has the form φ_I * f(θ) for some f;" -/
namespace phiIDotFactors_a

-- AMBIGUITY: "has the form φ_I * f(θ) for some f" read with one f (depending on the fixed
-- rates and PGF, and on θ only, not on φ_I) serving for all θ > 0 and φ_I ≥ 0. The weaker
-- pointwise reading (for each θ, φ_I some factor c with dφ_I/dt = φ_I * c) is implied and
-- not listed separately.

/-- Intended statement: for fixed rates and PGF there is f : ℚ → ℚ with
dφ_I/dt = φ_I * f(θ) for all θ > 0 and φ_I ≥ 0. -/
@[sa_reference "InvariantRegion.phiIDotFactors.a"]
def T : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), ∃ f : ℚ → ℚ,
    ∀ θ φI : ℚ, 0 < θ → 0 ≤ φI → phiIDot p ψ θ φI = φI * f θ

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "InvariantRegion.phiIDotFactors.a" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), ∃ f : ℚ → ℚ,
    ∀ θ φI : ℚ, 0 < θ → 0 ≤ φI → phiIDot p ψ θ φI = φI * f θ

@[sa_ref_forward "InvariantRegion.phiIDotFactors.a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "InvariantRegion.phiIDotFactors.a"]
theorem complete (s1 : S1) : T := s1

end phiIDotFactors_a

/-! ## `InvariantRegion.R118a`

Text: "**Result 118.** dφ_R/dt = γ φ_I ≥ 0 when φ_I ≥ 0." -/
namespace R118a

-- dφ_R/dt = γ φ_I is the model's definition; the checkable content is the sign statement.

/-- Intended statement: for all SIR rates and φ_I ≥ 0, γ φ_I ≥ 0. -/
@[sa_reference "InvariantRegion.R118a"]
def T : Prop := ∀ (p : EBCMParams) (φI : ℚ), 0 ≤ φI → 0 ≤ p.γ * φI

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "InvariantRegion.R118a" 1]
def S1 : Prop := ∀ (p : EBCMParams) (φI : ℚ), 0 ≤ φI → 0 ≤ p.γ * φI

@[sa_ref_forward "InvariantRegion.R118a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "InvariantRegion.R118a"]
theorem complete (s1 : S1) : T := s1

end R118a

/-! ## `InvariantRegion.R119a`

Text: "**Result 119.** dR/dt = γ I ≥ 0 when I ≥ 0." -/
namespace R119a

-- AMBIGUITY: "I" read as the EBCM observable I = 1 − ψ(θ) − R (module header), and dR/dt as
-- the model's γ (1 − ψ(θ) − R) = γ I. A reading with I an arbitrary rational is logically
-- equivalent (θ, R range over ℚ) and not listed separately.

/-- Intended statement: whenever I = 1 − ψ(θ) − R ≥ 0, dR/dt = γ I ≥ 0. -/
@[sa_reference "InvariantRegion.R119a"]
def T : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ R : ℚ),
    0 ≤ 1 - ψ.eval θ - R → 0 ≤ RDot p ψ θ R

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "InvariantRegion.R119a" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ R : ℚ),
    0 ≤ 1 - ψ.eval θ - R → 0 ≤ RDot p ψ θ R

@[sa_ref_forward "InvariantRegion.R119a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "InvariantRegion.R119a"]
theorem complete (s1 : S1) : T := s1

end R119a

/-! ## `InvariantRegion.R120`

Text: "**Result 120.** S + I + R = 1 holds as an *algebraic identity* because the EBCM
defines I := 1 − S − R. No ODE solution theory is required." -/
namespace R120

-- "No ODE solution theory is required" is a meta-statement about the proof; its checkable
-- trace is that the identity holds pointwise for every state (θ, R), with no trajectory.
-- S = ψ(θ) and I := 1 − S − R as in the module header.

/-- Intended statement: for every PGF and every state, ψ(θ) + (1 − ψ(θ) − R) + R = 1. -/
@[sa_reference "InvariantRegion.R120"]
def T : Prop :=
  ∀ (n : ℕ) (ψ : PolyPGF n) (θ R : ℚ), ψ.eval θ + (1 - ψ.eval θ - R) + R = 1

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "InvariantRegion.R120" 1]
def S1 : Prop :=
  ∀ (n : ℕ) (ψ : PolyPGF n) (θ R : ℚ), ψ.eval θ + (1 - ψ.eval θ - R) + R = 1

@[sa_ref_forward "InvariantRegion.R120" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "InvariantRegion.R120"]
theorem complete (s1 : S1) : T := s1

end R120

/-! ## `InvariantRegion.R120b`

Text: "**Result 120b.** Under the explicit seed convention used by the Julia builders, θ(0)=1
and the susceptible observable is `(1-ρ)ψ(θ)`. Since every PGF satisfies ψ(1)=1, the initial
observable values are S(0)=1−ρ, I(0)=ρ, R(0)=0 and therefore conserve total population." -/
namespace R120b

-- Convention (hypotheses, not claims): θ(0) = 1, S(0) = (1 − ρ)ψ(θ(0)) = (1 − ρ)ψ(1), R(0) = 0.
-- "Since every PGF satisfies ψ(1)=1" is the justification (claim pgfEvalOne), not listed.
-- AMBIGUITY: "I(0)=ρ": either the seeded initial value (then the claim is S(0) + ρ + 0 = 1,
-- S2), or the observable I = 1 − S − R evaluated at t = 0 (then I(0) = ρ is itself a claim,
-- S3). Both included. The seed fraction ρ is unrestricted (the text states no range).

/-- Intended statement: for every PGF ψ and seed ρ, S(0) = (1 − ρ)ψ(1) equals 1 − ρ, the
initial values S(0), I(0) = ρ, R(0) = 0 sum to 1, and the observable I(0) = 1 − S(0) − R(0)
equals ρ. -/
@[sa_reference "InvariantRegion.R120b"]
def T : Prop :=
  ∀ (n : ℕ) (ψ : PolyPGF n) (ρ : ℚ),
    (1 - ρ) * ψ.eval 1 = 1 - ρ ∧
    (1 - ρ) * ψ.eval 1 + ρ + 0 = 1 ∧
    1 - (1 - ρ) * ψ.eval 1 - 0 = ρ

/-- S1: S(0) = (1 − ρ)ψ(1) = 1 − ρ. -/
@[sa_shadow "InvariantRegion.R120b" 1]
def S1 : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (ρ : ℚ), (1 - ρ) * ψ.eval 1 = 1 - ρ

/-- S2: conservation, S(0) + I(0) + R(0) = 1 with I(0) = ρ and R(0) = 0. -/
@[sa_shadow "InvariantRegion.R120b" 2]
def S2 : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (ρ : ℚ), (1 - ρ) * ψ.eval 1 + ρ + 0 = 1

/-- S3: the observable I(0) = 1 − S(0) − R(0) equals ρ. -/
@[sa_shadow "InvariantRegion.R120b" 3]
def S3 : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (ρ : ℚ), 1 - (1 - ρ) * ψ.eval 1 - 0 = ρ

@[sa_ref_forward "InvariantRegion.R120b" 1]
theorem ref_fwd1 : T → S1 := fun t n ψ ρ => (t n ψ ρ).1
@[sa_ref_forward "InvariantRegion.R120b" 2]
theorem ref_fwd2 : T → S2 := fun t n ψ ρ => (t n ψ ρ).2.1
@[sa_ref_forward "InvariantRegion.R120b" 3]
theorem ref_fwd3 : T → S3 := fun t n ψ ρ => (t n ψ ρ).2.2

@[sa_complete "InvariantRegion.R120b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T :=
  fun n ψ ρ => ⟨s1 n ψ ρ, s2 n ψ ρ, s3 n ψ ρ⟩

end R120b

/-! ## `InvariantRegion.missingSeedFactorOvercounts`

Text: "If the seed factor is omitted from `S(0)` while `I(0)=ρ`, the total is `1+ρ`; for any
nonzero seed this is not a conserved population." -/
namespace missingSeedFactorOvercounts

-- With θ(0) = 1, the seed factor (1 − ρ) omitted gives S(0) = ψ(1); I(0) = ρ.
-- AMBIGUITY: R(0) is not mentioned; "the total" is read as S(0) + I(0) + R(0) with R(0) = 0
-- (R120b's convention).
-- AMBIGUITY: "this is not a conserved population" read as: the total differs from the
-- population 1.

/-- Intended statement: without the seed factor the total S(0) + I(0) + R(0) is 1 + ρ, and
for ρ ≠ 0 it is not 1. -/
@[sa_reference "InvariantRegion.missingSeedFactorOvercounts"]
def T : Prop :=
  ∀ (n : ℕ) (ψ : PolyPGF n) (ρ : ℚ),
    ψ.eval 1 + ρ + 0 = 1 + ρ ∧ (ρ ≠ 0 → ψ.eval 1 + ρ + 0 ≠ 1)

/-- S1: the total is 1 + ρ. -/
@[sa_shadow "InvariantRegion.missingSeedFactorOvercounts" 1]
def S1 : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (ρ : ℚ), ψ.eval 1 + ρ + 0 = 1 + ρ

/-- S2: for a nonzero seed the total is not the conserved population 1. -/
@[sa_shadow "InvariantRegion.missingSeedFactorOvercounts" 2]
def S2 : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (ρ : ℚ), ρ ≠ 0 → ψ.eval 1 + ρ + 0 ≠ 1

@[sa_ref_forward "InvariantRegion.missingSeedFactorOvercounts" 1]
theorem ref_fwd1 : T → S1 := fun t n ψ ρ => (t n ψ ρ).1
@[sa_ref_forward "InvariantRegion.missingSeedFactorOvercounts" 2]
theorem ref_fwd2 : T → S2 := fun t n ψ ρ => (t n ψ ρ).2

@[sa_complete "InvariantRegion.missingSeedFactorOvercounts"]
theorem complete (s1 : S1) (s2 : S2) : T := fun n ψ ρ => ⟨s1 n ψ ρ, s2 n ψ ρ⟩

end missingSeedFactorOvercounts

/-! ## `InvariantRegion.R121`

Text: "**Result 121.** I ≥ 0 is equivalent to S + R ≤ 1." -/
namespace R121

-- S = ψ(θ), I = 1 − S − R (module header). No restriction on θ, R is stated.

/-- Intended statement: 1 − ψ(θ) − R ≥ 0 ↔ ψ(θ) + R ≤ 1. -/
@[sa_reference "InvariantRegion.R121"]
def T : Prop :=
  ∀ (n : ℕ) (ψ : PolyPGF n) (θ R : ℚ), 0 ≤ 1 - ψ.eval θ - R ↔ ψ.eval θ + R ≤ 1

/-- S1: I ≥ 0 implies S + R ≤ 1. -/
@[sa_shadow "InvariantRegion.R121" 1]
def S1 : Prop :=
  ∀ (n : ℕ) (ψ : PolyPGF n) (θ R : ℚ), 0 ≤ 1 - ψ.eval θ - R → ψ.eval θ + R ≤ 1

/-- S2: S + R ≤ 1 implies I ≥ 0. -/
@[sa_shadow "InvariantRegion.R121" 2]
def S2 : Prop :=
  ∀ (n : ℕ) (ψ : PolyPGF n) (θ R : ℚ), ψ.eval θ + R ≤ 1 → 0 ≤ 1 - ψ.eval θ - R

@[sa_ref_forward "InvariantRegion.R121" 1]
theorem ref_fwd1 : T → S1 := fun t n ψ θ R => (t n ψ θ R).mp
@[sa_ref_forward "InvariantRegion.R121" 2]
theorem ref_fwd2 : T → S2 := fun t n ψ θ R => (t n ψ θ R).mpr

@[sa_complete "InvariantRegion.R121"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun n ψ θ R => ⟨s1 n ψ θ R, s2 n ψ θ R⟩

end R121

/-! ## `InvariantRegion.R122a`

Text: "**Result 122.** At the boundary face {I = 0}, the population-level drift is
dI/dt = β φ_I ψ′(θ) ≥ 0 whenever φ_I ≥ 0 and ψ′(θ) ≥ 0." -/
namespace R122a

-- "population-level drift dI/dt" = `IDot` (chain rule along the EBCM vector field).
-- Face {I = 0}: 1 − ψ(θ) − R = 0. No other restriction on θ, R is stated.

/-- Intended statement: on {I = 0}, dI/dt = β φ_I ψ′(θ), and dI/dt ≥ 0 when φ_I ≥ 0 and
ψ′(θ) ≥ 0. -/
@[sa_reference "InvariantRegion.R122a"]
def T : Prop :=
  (∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI R : ℚ), 1 - ψ.eval θ - R = 0 →
      IDot p ψ θ φI R = p.β * φI * pgfDeriv ψ θ) ∧
  (∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI R : ℚ), 1 - ψ.eval θ - R = 0 →
      0 ≤ φI → 0 ≤ pgfDeriv ψ θ → 0 ≤ IDot p ψ θ φI R)

/-- S1: on {I = 0} the drift equals β φ_I ψ′(θ). -/
@[sa_shadow "InvariantRegion.R122a" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI R : ℚ), 1 - ψ.eval θ - R = 0 →
    IDot p ψ θ φI R = p.β * φI * pgfDeriv ψ θ

/-- S2: on {I = 0} the drift is ≥ 0 whenever φ_I ≥ 0 and ψ′(θ) ≥ 0. -/
@[sa_shadow "InvariantRegion.R122a" 2]
def S2 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI R : ℚ), 1 - ψ.eval θ - R = 0 →
    0 ≤ φI → 0 ≤ pgfDeriv ψ θ → 0 ≤ IDot p ψ θ φI R

@[sa_ref_forward "InvariantRegion.R122a" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "InvariantRegion.R122a" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "InvariantRegion.R122a"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end R122a

/-! ## `InvariantRegion.iDotGeneral.a`

Text: "Alternative formulation: dI/dt = β φ_I ψ′(θ) − γ I." -/
namespace iDotGeneral_a

/-- Intended statement: at every state, the drift dI/dt (chain rule) equals
β φ_I ψ′(θ) − γ I with I = 1 − ψ(θ) − R. -/
@[sa_reference "InvariantRegion.iDotGeneral.a"]
def T : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI R : ℚ),
    IDot p ψ θ φI R = p.β * φI * pgfDeriv ψ θ - p.γ * (1 - ψ.eval θ - R)

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "InvariantRegion.iDotGeneral.a" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI R : ℚ),
    IDot p ψ θ φI R = p.β * φI * pgfDeriv ψ θ - p.γ * (1 - ψ.eval θ - R)

@[sa_ref_forward "InvariantRegion.iDotGeneral.a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "InvariantRegion.iDotGeneral.a"]
theorem complete (s1 : S1) : T := s1

end iDotGeneral_a

/-! ## `InvariantRegion.iDotGeneral.b`

Text: "When I = 0 the γ I term vanishes, leaving the nonneg inward term." -/
namespace iDotGeneral_b

-- "the γ I term vanishes, leaving [the term β φ_I ψ′(θ)]": on {I = 0}, dI/dt = β φ_I ψ′(θ)
-- (S1).
-- AMBIGUITY: "the nonneg inward term" carries no hypotheses here; read with the hypotheses
-- of Result 122 (φ_I ≥ 0, ψ′(θ) ≥ 0) under which the term is nonnegative (S2).

/-- Intended statement: on {I = 0} the drift is β φ_I ψ′(θ), which is ≥ 0 when φ_I ≥ 0 and
ψ′(θ) ≥ 0. -/
@[sa_reference "InvariantRegion.iDotGeneral.b"]
def T : Prop :=
  (∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI R : ℚ), 1 - ψ.eval θ - R = 0 →
      IDot p ψ θ φI R = p.β * φI * pgfDeriv ψ θ) ∧
  (∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI R : ℚ), 1 - ψ.eval θ - R = 0 →
      0 ≤ φI → 0 ≤ pgfDeriv ψ θ → 0 ≤ IDot p ψ θ φI R)

/-- S1: on {I = 0} the γ I term drops out: dI/dt = β φ_I ψ′(θ). -/
@[sa_shadow "InvariantRegion.iDotGeneral.b" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI R : ℚ), 1 - ψ.eval θ - R = 0 →
    IDot p ψ θ φI R = p.β * φI * pgfDeriv ψ θ

/-- S2: the remaining (inward) drift is nonnegative (φ_I ≥ 0, ψ′(θ) ≥ 0). -/
@[sa_shadow "InvariantRegion.iDotGeneral.b" 2]
def S2 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI R : ℚ), 1 - ψ.eval θ - R = 0 →
    0 ≤ φI → 0 ≤ pgfDeriv ψ θ → 0 ≤ IDot p ψ θ φI R

@[sa_ref_forward "InvariantRegion.iDotGeneral.b" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "InvariantRegion.iDotGeneral.b" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "InvariantRegion.iDotGeneral.b"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end iDotGeneral_b

/-! ## `InvariantRegion.iDotAtZero`

Text: "When I = 0, the I-derivative reduces to the nonneg inward term." -/
namespace iDotAtZero

-- "the nonneg inward term" = β φ_I ψ′(θ) (Result 122).
-- AMBIGUITY: no hypotheses are stated for "nonneg"; read with Result 122's hypotheses
-- φ_I ≥ 0 and ψ′(θ) ≥ 0 (S2).

/-- Intended statement: on {I = 0}, dI/dt = β φ_I ψ′(θ), and it is ≥ 0 when φ_I ≥ 0 and
ψ′(θ) ≥ 0. -/
@[sa_reference "InvariantRegion.iDotAtZero"]
def T : Prop :=
  (∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI R : ℚ), 1 - ψ.eval θ - R = 0 →
      IDot p ψ θ φI R = p.β * φI * pgfDeriv ψ θ) ∧
  (∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI R : ℚ), 1 - ψ.eval θ - R = 0 →
      0 ≤ φI → 0 ≤ pgfDeriv ψ θ → 0 ≤ IDot p ψ θ φI R)

/-- S1: on {I = 0}, dI/dt reduces to β φ_I ψ′(θ). -/
@[sa_shadow "InvariantRegion.iDotAtZero" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI R : ℚ), 1 - ψ.eval θ - R = 0 →
    IDot p ψ θ φI R = p.β * φI * pgfDeriv ψ θ

/-- S2: on {I = 0}, dI/dt ≥ 0 (φ_I ≥ 0, ψ′(θ) ≥ 0). -/
@[sa_shadow "InvariantRegion.iDotAtZero" 2]
def S2 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI R : ℚ), 1 - ψ.eval θ - R = 0 →
    0 ≤ φI → 0 ≤ pgfDeriv ψ θ → 0 ≤ IDot p ψ θ φI R

@[sa_ref_forward "InvariantRegion.iDotAtZero" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "InvariantRegion.iDotAtZero" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "InvariantRegion.iDotAtZero"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end iDotAtZero

/-! ## `InvariantRegion.sFromRegion`

Text: "For a point in the invariant region, S = ψ(θ) is automatically in [0, 1]." -/
namespace sFromRegion

/-- Intended statement: for every PGF and every point of the invariant region,
0 ≤ ψ(θ) ≤ 1. -/
@[sa_reference "InvariantRegion.sFromRegion"]
def T : Prop :=
  ∀ (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), 0 ≤ ψ.eval x.θ ∧ ψ.eval x.θ ≤ 1

/-- S1: S ≥ 0 at every region point. -/
@[sa_shadow "InvariantRegion.sFromRegion" 1]
def S1 : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), 0 ≤ ψ.eval x.θ

/-- S2: S ≤ 1 at every region point. -/
@[sa_shadow "InvariantRegion.sFromRegion" 2]
def S2 : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), ψ.eval x.θ ≤ 1

@[sa_ref_forward "InvariantRegion.sFromRegion" 1]
theorem ref_fwd1 : T → S1 := fun t n ψ x => (t n ψ x).1
@[sa_ref_forward "InvariantRegion.sFromRegion" 2]
theorem ref_fwd2 : T → S2 := fun t n ψ x => (t n ψ x).2

@[sa_complete "InvariantRegion.sFromRegion"]
theorem complete (s1 : S1) (s2 : S2) : T := fun n ψ x => ⟨s1 n ψ x, s2 n ψ x⟩

end sFromRegion

/-! ## `InvariantRegion.iNonnegFromRegion`

Text: "Given S from region and R ≥ 0 with S + R ≤ 1, the infected fraction I ≥ 0." -/
namespace iNonnegFromRegion

-- "S from region": S = ψ(θ) for a point x of the invariant region.
-- AMBIGUITY: "R ≥ 0" read either as a separately given R with R ≥ 0 (S1), or as the region
-- point's own R (S2, where R ≥ 0 comes from the region). Both included; S1 implies S2.
-- (A third reading, with S an arbitrary number in [0, 1], is not listed.)

/-- Intended statement: for a region point x, S = ψ(x.θ), and R ≥ 0 with S + R ≤ 1, the
infected fraction 1 − S − R is ≥ 0 (for a given R, and for the region's own R). -/
@[sa_reference "InvariantRegion.iNonnegFromRegion"]
def T : Prop :=
  (∀ (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion) (R : ℚ), 0 ≤ R → ψ.eval x.θ + R ≤ 1 →
      0 ≤ 1 - ψ.eval x.θ - R) ∧
  (∀ (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), ψ.eval x.θ + x.R ≤ 1 →
      0 ≤ 1 - ψ.eval x.θ - x.R)

/-- S1: separately given R ≥ 0 with ψ(x.θ) + R ≤ 1 gives I ≥ 0. -/
@[sa_shadow "InvariantRegion.iNonnegFromRegion" 1]
def S1 : Prop :=
  ∀ (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion) (R : ℚ), 0 ≤ R → ψ.eval x.θ + R ≤ 1 →
    0 ≤ 1 - ψ.eval x.θ - R

/-- S2: the region point's own R with ψ(x.θ) + x.R ≤ 1 gives I ≥ 0. -/
@[sa_shadow "InvariantRegion.iNonnegFromRegion" 2]
def S2 : Prop :=
  ∀ (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), ψ.eval x.θ + x.R ≤ 1 →
    0 ≤ 1 - ψ.eval x.θ - x.R

@[sa_ref_forward "InvariantRegion.iNonnegFromRegion" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "InvariantRegion.iNonnegFromRegion" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "InvariantRegion.iNonnegFromRegion"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end iNonnegFromRegion

/-! ## `InvariantRegion.R123b`

Text: "1. **θ face** (θ = 0 and θ = 1): θ is non-increasing since dθ/dt ≤ 0. This handles the
upper face θ ≤ 1 automatically (θ starts at 1 and can only decrease)." -/
namespace R123b

-- S1: dθ/dt = −β φ_I ≤ 0 at every point of the invariant region (so at both θ faces).
-- AMBIGUITY: "dθ/dt ≤ 0" could be read only at the two θ faces; the global reading on the
-- region is used (it covers both faces).
-- VOCAB-GAP: "θ is non-increasing" and "θ starts at 1 and can only decrease" are statements
-- about trajectories; no ODE-solution notion exists in the DataTypes. They are stated for real
-- functions θ, φ_I of time with θ′(t) = −β φ_I(t) and φ_I(t) ≥ 0 for t ≥ 0 (S2, S3).

/-- Intended statement: dθ/dt ≤ 0 on the invariant region; along any trajectory with
θ′ = −β φ_I and φ_I ≥ 0, θ is non-increasing on [0, ∞) and, if θ(0) = 1, stays ≤ 1. -/
@[sa_reference "InvariantRegion.R123b"]
def T : Prop :=
  (∀ (p : EBCMParams) (x : EBCMRegion), -p.β * x.φ_I ≤ 0) ∧
  (∀ (p : EBCMParams) (θ φI : ℝ → ℝ),
      (∀ t : ℝ, 0 ≤ t → HasDerivAt θ (-(p.β : ℝ) * φI t) t) →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ φI t) → AntitoneOn θ (Set.Ici 0)) ∧
  (∀ (p : EBCMParams) (θ φI : ℝ → ℝ),
      (∀ t : ℝ, 0 ≤ t → HasDerivAt θ (-(p.β : ℝ) * φI t) t) →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ φI t) → θ 0 = 1 → ∀ t : ℝ, 0 ≤ t → θ t ≤ 1)

/-- S1: dθ/dt = −β φ_I ≤ 0 at every point of the invariant region. -/
@[sa_shadow "InvariantRegion.R123b" 1]
def S1 : Prop := ∀ (p : EBCMParams) (x : EBCMRegion), -p.β * x.φ_I ≤ 0

/-- S2: θ is non-increasing along trajectories (θ′ = −β φ_I, φ_I ≥ 0). -/
@[sa_shadow "InvariantRegion.R123b" 2]
def S2 : Prop :=
  ∀ (p : EBCMParams) (θ φI : ℝ → ℝ),
    (∀ t : ℝ, 0 ≤ t → HasDerivAt θ (-(p.β : ℝ) * φI t) t) →
    (∀ t : ℝ, 0 ≤ t → 0 ≤ φI t) → AntitoneOn θ (Set.Ici 0)

/-- S3: the upper face is handled automatically: θ(0) = 1 implies θ(t) ≤ 1 for t ≥ 0. -/
@[sa_shadow "InvariantRegion.R123b" 3]
def S3 : Prop :=
  ∀ (p : EBCMParams) (θ φI : ℝ → ℝ),
    (∀ t : ℝ, 0 ≤ t → HasDerivAt θ (-(p.β : ℝ) * φI t) t) →
    (∀ t : ℝ, 0 ≤ t → 0 ≤ φI t) → θ 0 = 1 → ∀ t : ℝ, 0 ≤ t → θ t ≤ 1

@[sa_ref_forward "InvariantRegion.R123b" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "InvariantRegion.R123b" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "InvariantRegion.R123b" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2

@[sa_complete "InvariantRegion.R123b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end R123b

/-! ## `InvariantRegion.R123d`

Text: "2. **φ_I face** (φ_I = 0): dφ_I/dt = 0 there — the face is absorbing." -/
namespace R123d

-- "the face is absorbing" is read as the interpretation of dφ_I/dt = 0 on the face (the claim's
-- checkable content); a trajectory-level invariance statement is not listed.

/-- Intended statement: at every point of the invariant region with φ_I = 0, dφ_I/dt = 0. -/
@[sa_reference "InvariantRegion.R123d"]
def T : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), x.φ_I = 0 →
    phiIDot p ψ x.θ x.φ_I = 0

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "InvariantRegion.R123d" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), x.φ_I = 0 →
    phiIDot p ψ x.θ x.φ_I = 0

@[sa_ref_forward "InvariantRegion.R123d" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "InvariantRegion.R123d"]
theorem complete (s1 : S1) : T := s1

end R123d

/-! ## `InvariantRegion.R123e`

Text: "3. **φ_R face** (φ_R = 0): dφ_R/dt = γ φ_I ≥ 0 — inward pointing." -/
namespace R123e

/-- Intended statement: at every point of the invariant region with φ_R = 0,
dφ_R/dt = γ φ_I ≥ 0. -/
@[sa_reference "InvariantRegion.R123e"]
def T : Prop := ∀ (p : EBCMParams) (x : EBCMRegion), x.φ_R = 0 → 0 ≤ p.γ * x.φ_I

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "InvariantRegion.R123e" 1]
def S1 : Prop := ∀ (p : EBCMParams) (x : EBCMRegion), x.φ_R = 0 → 0 ≤ p.γ * x.φ_I

@[sa_ref_forward "InvariantRegion.R123e" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "InvariantRegion.R123e"]
theorem complete (s1 : S1) : T := s1

end R123e

/-! ## `InvariantRegion.R123f`

Text: "4. **I face** (I = 0, equivalently S + R = 1): dI/dt = β φ_I ψ′(θ) ≥ 0 — the Nagumo
tangency condition holds." -/
namespace R123f

-- Points of the face are `EBCMRegion` points with I = 1 − ψ(θ) − R = 0. No hypothesis on
-- ψ′(θ) is stated here (unlike Result 122), so none is assumed.
-- "equivalently S + R = 1" gives the two directions S3, S4.

/-- Intended statement: on the I face of the invariant region, dI/dt = β φ_I ψ′(θ) and
dI/dt ≥ 0; and I = 0 ↔ S + R = 1 there. -/
@[sa_reference "InvariantRegion.R123f"]
def T : Prop :=
  (∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), 1 - ψ.eval x.θ - x.R = 0 →
      IDot p ψ x.θ x.φ_I x.R = p.β * x.φ_I * pgfDeriv ψ x.θ) ∧
  (∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), 1 - ψ.eval x.θ - x.R = 0 →
      0 ≤ IDot p ψ x.θ x.φ_I x.R) ∧
  (∀ (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), 1 - ψ.eval x.θ - x.R = 0 →
      ψ.eval x.θ + x.R = 1) ∧
  (∀ (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), ψ.eval x.θ + x.R = 1 →
      1 - ψ.eval x.θ - x.R = 0)

/-- S1: on the I face, dI/dt = β φ_I ψ′(θ). -/
@[sa_shadow "InvariantRegion.R123f" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), 1 - ψ.eval x.θ - x.R = 0 →
    IDot p ψ x.θ x.φ_I x.R = p.β * x.φ_I * pgfDeriv ψ x.θ

/-- S2: on the I face, dI/dt ≥ 0 (Nagumo tangency). -/
@[sa_shadow "InvariantRegion.R123f" 2]
def S2 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), 1 - ψ.eval x.θ - x.R = 0 →
    0 ≤ IDot p ψ x.θ x.φ_I x.R

/-- S3: I = 0 implies S + R = 1. -/
@[sa_shadow "InvariantRegion.R123f" 3]
def S3 : Prop :=
  ∀ (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), 1 - ψ.eval x.θ - x.R = 0 →
    ψ.eval x.θ + x.R = 1

/-- S4: S + R = 1 implies I = 0. -/
@[sa_shadow "InvariantRegion.R123f" 4]
def S4 : Prop :=
  ∀ (n : ℕ) (ψ : PolyPGF n) (x : EBCMRegion), ψ.eval x.θ + x.R = 1 →
    1 - ψ.eval x.θ - x.R = 0

@[sa_ref_forward "InvariantRegion.R123f" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "InvariantRegion.R123f" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "InvariantRegion.R123f" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "InvariantRegion.R123f" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2

@[sa_complete "InvariantRegion.R123f"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end R123f

/-! ## `InvariantRegion.header.thetaFace.a`

Text: "The θ ≥ 0 face requires the *edge conservation* constraint φ_I ≤ θ: when θ = 0, we have
φ_I ≤ θ = 0, so φ_I = 0, and therefore dθ/dt = 0 (the wall is absorbing)." -/
namespace header_thetaFace_a

-- Points of the face are `EBCMRegion` points (φ_I ≥ 0 comes from the region).
-- "(the wall is absorbing)" is read as the interpretation of dθ/dt = 0.
-- AMBIGUITY: "requires" could also assert necessity (without φ_I ≤ θ the face condition
-- fails); read as "needs as a hypothesis", necessity is not listed.

/-- Intended statement: at a region point with θ = 0 and φ_I ≤ θ, φ_I = 0 and dθ/dt = 0. -/
@[sa_reference "InvariantRegion.header.thetaFace.a"]
def T : Prop :=
  (∀ (x : EBCMRegion), x.θ = 0 → x.φ_I ≤ x.θ → x.φ_I = 0) ∧
  (∀ (p : EBCMParams) (x : EBCMRegion), x.θ = 0 → x.φ_I ≤ x.θ → -p.β * x.φ_I = 0)

/-- S1: θ = 0 and φ_I ≤ θ force φ_I = 0. -/
@[sa_shadow "InvariantRegion.header.thetaFace.a" 1]
def S1 : Prop := ∀ (x : EBCMRegion), x.θ = 0 → x.φ_I ≤ x.θ → x.φ_I = 0

/-- S2: θ = 0 and φ_I ≤ θ give dθ/dt = −β φ_I = 0. -/
@[sa_shadow "InvariantRegion.header.thetaFace.a" 2]
def S2 : Prop :=
  ∀ (p : EBCMParams) (x : EBCMRegion), x.θ = 0 → x.φ_I ≤ x.θ → -p.β * x.φ_I = 0

@[sa_ref_forward "InvariantRegion.header.thetaFace.a" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "InvariantRegion.header.thetaFace.a" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "InvariantRegion.header.thetaFace.a"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end header_thetaFace_a

/-! ## `InvariantRegion.thetaLowerBoundaryAbsorbing`

Text: "Assuming the edge conservation identity φ_I ≤ θ (a physical constraint of the EBCM),
the lower boundary θ = 0 is absorbing: dθ/dt = 0." -/
namespace thetaLowerBoundaryAbsorbing

-- "absorbing" is defined by the text after the colon: dθ/dt = 0. Points of the boundary are
-- `EBCMRegion` points (φ_I ≥ 0 comes from the region).

/-- Intended statement: at a region point with φ_I ≤ θ and θ = 0, dθ/dt = −β φ_I = 0. -/
@[sa_reference "InvariantRegion.thetaLowerBoundaryAbsorbing"]
def T : Prop :=
  ∀ (p : EBCMParams) (x : EBCMRegion), x.φ_I ≤ x.θ → x.θ = 0 → -p.β * x.φ_I = 0

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "InvariantRegion.thetaLowerBoundaryAbsorbing" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (x : EBCMRegion), x.φ_I ≤ x.θ → x.θ = 0 → -p.β * x.φ_I = 0

@[sa_ref_forward "InvariantRegion.thetaLowerBoundaryAbsorbing" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "InvariantRegion.thetaLowerBoundaryAbsorbing"]
theorem complete (s1 : S1) : T := s1

end thetaLowerBoundaryAbsorbing

end Alignment.Shadows.InvariantRegion

noncomputable section

/-! ## Shared notions for the re-authored InvariantRegion blocks (blind)

Not registered; inlined by the audit. From the model text (`InvariantRegion.header.model`): for a
PGF ψ(x) = Σᵢ pᵢ xⁱ (`PolyPGF`), ψ′(x) = Σᵢ i pᵢ x^(i−1) and ψ″(x) = Σᵢ i(i−1) pᵢ x^(i−2) (formal
derivatives, the low-order terms vanish through the factors i and i−1). The correct φ_I field is
`β φ_I ψ″(θ)/ψ′(1) − (β + γ) φ_I`; the incorrect form used by some Lean statements is
`(β φ_I / θ)(ψ′(θ)/ψ′(1)) − (β + γ) φ_I`. Over `ℚ` for pointwise statements, and over `ℝ`
(coefficients cast) for trajectories and continuity. A solution of the correct expanded EBCM is a
quadruple of real functions with the model's derivatives at every `t ≥ 0`. -/
namespace Alignment.Shadows.InvariantRegion.Shared2

/-- ψ′(x) over ℚ. -/
def dpsiQ {n : ℕ} (ψ : PolyPGF n) (x : ℚ) : ℚ :=
  ∑ i : Fin n, ((i : ℕ) : ℚ) * ψ.coeffs i * x ^ ((i : ℕ) - 1)
/-- ψ″(x) over ℚ. -/
def ddpsiQ {n : ℕ} (ψ : PolyPGF n) (x : ℚ) : ℚ :=
  ∑ i : Fin n, ((i : ℕ) : ℚ) * (((i : ℕ) : ℚ) - 1) * ψ.coeffs i * x ^ ((i : ℕ) - 2)
/-- The correct φ_I field `β φ_I ψ″(θ)/ψ′(1) − (β + γ) φ_I` over ℚ. -/
def correctQ (p : EBCMParams) {n : ℕ} (ψ : PolyPGF n) (θ φI : ℚ) : ℚ :=
  p.β * φI * ddpsiQ ψ θ / dpsiQ ψ 1 - (p.β + p.γ) * φI
/-- The incorrect form `(β φ_I / θ)(ψ′(θ)/ψ′(1)) − (β + γ) φ_I` over ℚ. -/
def wrongQ (p : EBCMParams) {n : ℕ} (ψ : PolyPGF n) (θ φI : ℚ) : ℚ :=
  (p.β * φI / θ) * (dpsiQ ψ θ / dpsiQ ψ 1) - (p.β + p.γ) * φI

/-- ψ(x) over ℝ. -/
def psiR {n : ℕ} (ψ : PolyPGF n) (x : ℝ) : ℝ := ∑ i : Fin n, (ψ.coeffs i : ℝ) * x ^ (i : ℕ)
/-- ψ′(x) over ℝ. -/
def dpsiR {n : ℕ} (ψ : PolyPGF n) (x : ℝ) : ℝ :=
  ∑ i : Fin n, ((i : ℕ) : ℝ) * (ψ.coeffs i : ℝ) * x ^ ((i : ℕ) - 1)
/-- ψ″(x) over ℝ. -/
def ddpsiR {n : ℕ} (ψ : PolyPGF n) (x : ℝ) : ℝ :=
  ∑ i : Fin n, ((i : ℕ) : ℝ) * (((i : ℕ) : ℝ) - 1) * (ψ.coeffs i : ℝ) * x ^ ((i : ℕ) - 2)
/-- The correct φ_I field over ℝ. -/
def correctR (p : EBCMParams) {n : ℕ} (ψ : PolyPGF n) (θ φI : ℝ) : ℝ :=
  (p.β : ℝ) * φI * ddpsiR ψ θ / dpsiR ψ 1 - ((p.β : ℝ) + p.γ) * φI
/-- The incorrect form over ℝ. -/
def wrongR (p : EBCMParams) {n : ℕ} (ψ : PolyPGF n) (θ φI : ℝ) : ℝ :=
  ((p.β : ℝ) * φI / θ) * (dpsiR ψ θ / dpsiR ψ 1) - ((p.β : ℝ) + p.γ) * φI

/-- `(θ, φ_I, φ_R, R)` solves the correct expanded EBCM for all `t ≥ 0`. -/
def IsSol (p : EBCMParams) {n : ℕ} (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    HasDerivAt θ (-(p.β : ℝ) * φI t) t ∧ HasDerivAt φI (correctR p ψ (θ t) (φI t)) t ∧
    HasDerivAt φR ((p.γ : ℝ) * φI t) t ∧ HasDerivAt R ((p.γ : ℝ) * (1 - psiR ψ (θ t) - R t)) t

/-- Physically meaningful initial state: θ ∈ [0, 1], φ_I, φ_R, R ≥ 0, edge conservation
θ = ψ′(θ)/ψ′(1) + φ_I + φ_R, I = 1 − ψ(θ) − R ≥ 0, and a positive mean degree ψ′(1). -/
def InitOK {n : ℕ} (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ) : Prop :=
  0 ≤ θ 0 ∧ θ 0 ≤ 1 ∧ 0 ≤ φI 0 ∧ 0 ≤ φR 0 ∧ 0 ≤ R 0 ∧
    θ 0 = dpsiR ψ (θ 0) / dpsiR ψ 1 + φI 0 + φR 0 ∧ psiR ψ (θ 0) + R 0 ≤ 1 ∧ 0 < dpsiR ψ 1

end Alignment.Shadows.InvariantRegion.Shared2

/-! ## `InvariantRegion.R117a` (re-authored blind)

Text: "**Result 117.** When φ_I = 0, the full φ_I component of the EBCM vector field vanishes:
dφ_I/dt = β φ_I ψ″(θ)/ψ′(1) − (β + γ) φ_I = 0. The Lean statement uses the incorrect form
(β φ_I / θ)(ψ′(θ)/ψ′(1)) − (β + γ) φ_I; the correct form is
`phi_I_dot_correct_zero_at_boundary`."

The claim is about the (correct) φ_I component quoted in the first sentence; the remark on the
form used by the Lean statement describes the implementation and is not formalised. -/
namespace Alignment.Shadows.InvariantRegion.R117a

open Alignment.Shadows.InvariantRegion.Shared2

@[sa_reference "InvariantRegion.R117a"]
def T : Prop := ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ : ℚ), correctQ p ψ θ 0 = 0

/-- S1: the φ_I component vanishes at φ_I = 0, for every θ. -/
@[sa_shadow "InvariantRegion.R117a" 1]
def S1 : Prop := ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ : ℚ), correctQ p ψ θ 0 = 0

@[sa_ref_forward "InvariantRegion.R117a" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "InvariantRegion.R117a"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.InvariantRegion.R117a

/-! ## `InvariantRegion.R120b.guard` (re-authored blind)

Text: "This identity records the arithmetic behind a regression in which the expanded-form EBCM used
`S = ψ(θ)` while still seeding `I(0)=ρ`, which overcounted population by exactly ρ at t=0. It is
not linked to the Julia builders and cannot detect that regression."

At t = 0, θ = 1 and R = 0, so `S = ψ(1)` and `S + I + R − 1 = ψ(1) + ρ + 0 − 1 = ρ`. The second
sentence is a remark about the (absent) link to Julia code. -/
namespace Alignment.Shadows.InvariantRegion.R120b_guard

@[sa_reference "InvariantRegion.R120b.guard"]
def T : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (ρ : ℚ), ψ.eval 1 + ρ + 0 - 1 = ρ

/-- S1: with `S = ψ(θ(0)) = ψ(1)`, `I(0) = ρ`, `R(0) = 0`, the population exceeds 1 by ρ. -/
@[sa_shadow "InvariantRegion.R120b.guard" 1]
def S1 : Prop := ∀ (n : ℕ) (ψ : PolyPGF n) (ρ : ℚ), ψ.eval 1 + ρ + 0 - 1 = ρ

@[sa_ref_forward "InvariantRegion.R120b.guard" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "InvariantRegion.R120b.guard"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.InvariantRegion.R120b_guard

/-! ## `InvariantRegion.R123a` (re-authored blind)

Text: "**Result 123 (Invariant Region Boundary Conditions).** Four sign conditions at the boundary
faces of the EBCM region hold at every point of `EBCMRegion`. They are the conditions Nagumo's
theorem would need, except that the θ = 0 face also needs φ_I ≤ θ, which `EBCMRegion` omits:"

-- AMBIGUITY: the four conditions are not listed in the quoted text. Read as the inward-normal
sign conditions of the model's vector field (header.model) on the faces of `EBCMRegion` other
than θ = 0: θ = 1 (dθ/dt ≤ 0), φ_I = 0 (dφ_I/dt ≥ 0), φ_R = 0 (dφ_R/dt ≥ 0), R = 0 (dR/dt ≥ 0).
The θ = 0 face (dθ/dt ≥ 0) holds given φ_I ≤ θ (S5) and can fail without it (S6). That these
are Nagumo's hypotheses is a remark. -/
namespace Alignment.Shadows.InvariantRegion.R123a

open Alignment.Shadows.InvariantRegion.Shared2

@[sa_reference "InvariantRegion.R123a"]
def T : Prop :=
  (∀ (x : EBCMRegion) (p : EBCMParams), x.θ = 1 → -p.β * x.φ_I ≤ 0) ∧
  (∀ (x : EBCMRegion) (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), x.φ_I = 0 →
      0 ≤ correctQ p ψ x.θ x.φ_I) ∧
  (∀ (x : EBCMRegion) (p : EBCMParams), x.φ_R = 0 → 0 ≤ p.γ * x.φ_I) ∧
  (∀ (x : EBCMRegion) (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), x.R = 0 →
      0 ≤ p.γ * (1 - ψ.eval x.θ - x.R)) ∧
  (∀ (x : EBCMRegion) (p : EBCMParams), x.θ = 0 → x.φ_I ≤ x.θ → 0 ≤ -p.β * x.φ_I) ∧
  (∃ (x : EBCMRegion) (p : EBCMParams), x.θ = 0 ∧ -p.β * x.φ_I < 0)

/-- S1: θ = 1 face: dθ/dt ≤ 0. -/
@[sa_shadow "InvariantRegion.R123a" 1]
def S1 : Prop := ∀ (x : EBCMRegion) (p : EBCMParams), x.θ = 1 → -p.β * x.φ_I ≤ 0
/-- S2: φ_I = 0 face: dφ_I/dt ≥ 0. -/
@[sa_shadow "InvariantRegion.R123a" 2]
def S2 : Prop :=
  ∀ (x : EBCMRegion) (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), x.φ_I = 0 →
    0 ≤ correctQ p ψ x.θ x.φ_I
/-- S3: φ_R = 0 face: dφ_R/dt ≥ 0. -/
@[sa_shadow "InvariantRegion.R123a" 3]
def S3 : Prop := ∀ (x : EBCMRegion) (p : EBCMParams), x.φ_R = 0 → 0 ≤ p.γ * x.φ_I
/-- S4: R = 0 face: dR/dt ≥ 0. -/
@[sa_shadow "InvariantRegion.R123a" 4]
def S4 : Prop :=
  ∀ (x : EBCMRegion) (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), x.R = 0 →
    0 ≤ p.γ * (1 - ψ.eval x.θ - x.R)
/-- S5: θ = 0 face: dθ/dt ≥ 0 given φ_I ≤ θ. -/
@[sa_shadow "InvariantRegion.R123a" 5]
def S5 : Prop := ∀ (x : EBCMRegion) (p : EBCMParams), x.θ = 0 → x.φ_I ≤ x.θ → 0 ≤ -p.β * x.φ_I
/-- S6: without φ_I ≤ θ the θ = 0 condition fails at some point of `EBCMRegion`. -/
@[sa_shadow "InvariantRegion.R123a" 6]
def S6 : Prop := ∃ (x : EBCMRegion) (p : EBCMParams), x.θ = 0 ∧ -p.β * x.φ_I < 0

@[sa_ref_forward "InvariantRegion.R123a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "InvariantRegion.R123a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "InvariantRegion.R123a" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "InvariantRegion.R123a" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "InvariantRegion.R123a" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2.1
@[sa_ref_forward "InvariantRegion.R123a" 6] theorem ref_fwd6 : T → S6 := fun t => t.2.2.2.2.2
@[sa_complete "InvariantRegion.R123a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T :=
  ⟨s1, s2, s3, s4, s5, s6⟩

end Alignment.Shadows.InvariantRegion.R123a

/-! ## `InvariantRegion.R123c` (blind)

Text: "The lower face θ = 0 requires the additional physical constraint φ_I ≤ θ (edge
conservation), which holds in the full model; it is not a hypothesis of this theorem (see
`theta_lower_boundary_absorbing` and `phi_I_le_theta`)."

S1: with φ_I ≤ θ the θ = 0 face condition dθ/dt = −βφ_I ≥ 0 holds; S2 ("requires"): without it,
it fails at some point of `EBCMRegion`; S3 ("holds in the full model"): edge conservation
θ = φ_S + φ_I + φ_R with φ_S, φ_R ≥ 0 gives φ_I ≤ θ. That it is not a hypothesis of the theorem
describes the implementation. -/
namespace Alignment.Shadows.InvariantRegion.R123c

@[sa_reference "InvariantRegion.R123c"]
def T : Prop :=
  (∀ (x : EBCMRegion) (p : EBCMParams), x.θ = 0 → x.φ_I ≤ x.θ → 0 ≤ -p.β * x.φ_I) ∧
  (∃ (x : EBCMRegion) (p : EBCMParams), x.θ = 0 ∧ -p.β * x.φ_I < 0) ∧
  (∀ θ φS φI φR : ℚ, θ = φS + φI + φR → 0 ≤ φS → 0 ≤ φR → φI ≤ θ)

/-- S1: the θ = 0 face condition holds given φ_I ≤ θ. -/
@[sa_shadow "InvariantRegion.R123c" 1]
def S1 : Prop := ∀ (x : EBCMRegion) (p : EBCMParams), x.θ = 0 → x.φ_I ≤ x.θ → 0 ≤ -p.β * x.φ_I
/-- S2: it can fail without φ_I ≤ θ. -/
@[sa_shadow "InvariantRegion.R123c" 2]
def S2 : Prop := ∃ (x : EBCMRegion) (p : EBCMParams), x.θ = 0 ∧ -p.β * x.φ_I < 0
/-- S3: edge conservation gives φ_I ≤ θ. -/
@[sa_shadow "InvariantRegion.R123c" 3]
def S3 : Prop := ∀ θ φS φI φR : ℚ, θ = φS + φI + φR → 0 ≤ φS → 0 ≤ φR → φI ≤ θ

@[sa_ref_forward "InvariantRegion.R123c" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "InvariantRegion.R123c" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "InvariantRegion.R123c" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "InvariantRegion.R123c"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.InvariantRegion.R123c

/-! ## `InvariantRegion.header.faceConditions` (re-authored blind)

Text: "**Sign/monotone conditions**: at each face of the region the component of the vector field
normal to the face is ≥ 0 (it vanishes or points inward), given the constraints φ_I ≤ θ and
S + R ≤ 1, which `EBCMRegion` omits."

Faces of `EBCMRegion`: θ = 0, θ = 1, φ_I = 0, φ_R = 0, R = 0; the inward normal components are
dθ/dt, −dθ/dt, dφ_I/dt, dφ_R/dt, dR/dt of the model's field (header.model), with S = ψ(θ). That
the structure omits the constraints is a remark. -/
namespace Alignment.Shadows.InvariantRegion.header_faceConditions

open Alignment.Shadows.InvariantRegion.Shared2

/-- The constraints φ_I ≤ θ and S + R ≤ 1. -/
def Hyp {n : ℕ} (ψ : PolyPGF n) (x : EBCMRegion) : Prop := x.φ_I ≤ x.θ ∧ ψ.eval x.θ + x.R ≤ 1

@[sa_reference "InvariantRegion.header.faceConditions"]
def T : Prop :=
  (∀ (x : EBCMRegion) (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), Hyp ψ x → x.θ = 0 →
      0 ≤ -p.β * x.φ_I) ∧
  (∀ (x : EBCMRegion) (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), Hyp ψ x → x.θ = 1 →
      0 ≤ -(-p.β * x.φ_I)) ∧
  (∀ (x : EBCMRegion) (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), Hyp ψ x → x.φ_I = 0 →
      0 ≤ correctQ p ψ x.θ x.φ_I) ∧
  (∀ (x : EBCMRegion) (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), Hyp ψ x → x.φ_R = 0 →
      0 ≤ p.γ * x.φ_I) ∧
  (∀ (x : EBCMRegion) (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), Hyp ψ x → x.R = 0 →
      0 ≤ p.γ * (1 - ψ.eval x.θ - x.R))

/-- S1: θ = 0 face. -/
@[sa_shadow "InvariantRegion.header.faceConditions" 1]
def S1 : Prop :=
  ∀ (x : EBCMRegion) (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), Hyp ψ x → x.θ = 0 →
    0 ≤ -p.β * x.φ_I
/-- S2: θ = 1 face (inward normal −θ). -/
@[sa_shadow "InvariantRegion.header.faceConditions" 2]
def S2 : Prop :=
  ∀ (x : EBCMRegion) (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), Hyp ψ x → x.θ = 1 →
    0 ≤ -(-p.β * x.φ_I)
/-- S3: φ_I = 0 face. -/
@[sa_shadow "InvariantRegion.header.faceConditions" 3]
def S3 : Prop :=
  ∀ (x : EBCMRegion) (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), Hyp ψ x → x.φ_I = 0 →
    0 ≤ correctQ p ψ x.θ x.φ_I
/-- S4: φ_R = 0 face. -/
@[sa_shadow "InvariantRegion.header.faceConditions" 4]
def S4 : Prop :=
  ∀ (x : EBCMRegion) (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), Hyp ψ x → x.φ_R = 0 →
    0 ≤ p.γ * x.φ_I
/-- S5: R = 0 face. -/
@[sa_shadow "InvariantRegion.header.faceConditions" 5]
def S5 : Prop :=
  ∀ (x : EBCMRegion) (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n), Hyp ψ x → x.R = 0 →
    0 ≤ p.γ * (1 - ψ.eval x.θ - x.R)

@[sa_ref_forward "InvariantRegion.header.faceConditions" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "InvariantRegion.header.faceConditions" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "InvariantRegion.header.faceConditions" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "InvariantRegion.header.faceConditions" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2.1
@[sa_ref_forward "InvariantRegion.header.faceConditions" 5] theorem ref_fwd5 : T → S5 :=
  fun t => t.2.2.2.2
@[sa_complete "InvariantRegion.header.faceConditions"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.InvariantRegion.header_faceConditions

/-! ## `InvariantRegion.header.invariance.I` (blind)

Text: "The state variables of the single-type static SIR edge-based compartmental model (EBCM)
remain in a physically meaningful region for all t ≥ 0 (for the correct field below; this is not
proved here — the file records only pointwise sign conditions on the right-hand side): [...]
* I = 1 − S − R ≥ 0 — infected fraction"

For every solution of the correct expanded EBCM (Shared2.IsSol) that starts in the physical
region (Shared2.InitOK), I(t) = 1 − ψ(θ(t)) − R(t) ≥ 0 for all t ≥ 0. -/
namespace Alignment.Shadows.InvariantRegion.header_invariance_I

open Alignment.Shadows.InvariantRegion.Shared2

@[sa_reference "InvariantRegion.header.invariance.I"]
def T : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → InitOK ψ θ φI φR R → ∀ t : ℝ, 0 ≤ t → 0 ≤ 1 - psiR ψ (θ t) - R t

/-- S1: the infected fraction stays nonnegative. -/
@[sa_shadow "InvariantRegion.header.invariance.I" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → InitOK ψ θ φI φR R → ∀ t : ℝ, 0 ≤ t → 0 ≤ 1 - psiR ψ (θ t) - R t

@[sa_ref_forward "InvariantRegion.header.invariance.I" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "InvariantRegion.header.invariance.I"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.InvariantRegion.header_invariance_I

/-! ## `InvariantRegion.header.invariance.R` (blind)

Text: "The state variables ... remain in a physically meaningful region for all t ≥ 0 (for the
correct field below; this is not proved here ...): [...] * R ≥ 0, non-decreasing" -/
namespace Alignment.Shadows.InvariantRegion.header_invariance_R

open Alignment.Shadows.InvariantRegion.Shared2

@[sa_reference "InvariantRegion.header.invariance.R"]
def T : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → InitOK ψ θ φI φR R →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ R t) ∧ MonotoneOn R (Set.Ici 0)

/-- S1: R stays nonnegative. -/
@[sa_shadow "InvariantRegion.header.invariance.R" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → InitOK ψ θ φI φR R → ∀ t : ℝ, 0 ≤ t → 0 ≤ R t
/-- S2: R is non-decreasing on [0, ∞). -/
@[sa_shadow "InvariantRegion.header.invariance.R" 2]
def S2 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → InitOK ψ θ φI φR R → MonotoneOn R (Set.Ici 0)

@[sa_ref_forward "InvariantRegion.header.invariance.R" 1] theorem ref_fwd1 : T → S1 :=
  fun t p n ψ θ φI φR R h1 h2 => (t p n ψ θ φI φR R h1 h2).1
@[sa_ref_forward "InvariantRegion.header.invariance.R" 2] theorem ref_fwd2 : T → S2 :=
  fun t p n ψ θ φI φR R h1 h2 => (t p n ψ θ φI φR R h1 h2).2
@[sa_complete "InvariantRegion.header.invariance.R"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun p n ψ θ φI φR R h1 h2 => ⟨s1 p n ψ θ φI φR R h1 h2, s2 p n ψ θ φI φR R h1 h2⟩

end Alignment.Shadows.InvariantRegion.header_invariance_R

/-! ## `InvariantRegion.header.invariance.S` (blind)

Text: "The state variables ... remain in a physically meaningful region for all t ≥ 0 (for the
correct field below; this is not proved here ...): [...] * S = ψ(θ) ∈ [0, 1] — susceptible
fraction" -/
namespace Alignment.Shadows.InvariantRegion.header_invariance_S

open Alignment.Shadows.InvariantRegion.Shared2

@[sa_reference "InvariantRegion.header.invariance.S"]
def T : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → InitOK ψ θ φI φR R →
      ∀ t : ℝ, 0 ≤ t → 0 ≤ psiR ψ (θ t) ∧ psiR ψ (θ t) ≤ 1

/-- S1: S = ψ(θ) stays nonnegative. -/
@[sa_shadow "InvariantRegion.header.invariance.S" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → InitOK ψ θ φI φR R → ∀ t : ℝ, 0 ≤ t → 0 ≤ psiR ψ (θ t)
/-- S2: S = ψ(θ) stays at most one. -/
@[sa_shadow "InvariantRegion.header.invariance.S" 2]
def S2 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → InitOK ψ θ φI φR R → ∀ t : ℝ, 0 ≤ t → psiR ψ (θ t) ≤ 1

@[sa_ref_forward "InvariantRegion.header.invariance.S" 1] theorem ref_fwd1 : T → S1 :=
  fun t p n ψ θ φI φR R h1 h2 s hs => (t p n ψ θ φI φR R h1 h2 s hs).1
@[sa_ref_forward "InvariantRegion.header.invariance.S" 2] theorem ref_fwd2 : T → S2 :=
  fun t p n ψ θ φI φR R h1 h2 s hs => (t p n ψ θ φI φR R h1 h2 s hs).2
@[sa_complete "InvariantRegion.header.invariance.S"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun p n ψ θ φI φR R h1 h2 s hs =>
    ⟨s1 p n ψ θ φI φR R h1 h2 s hs, s2 p n ψ θ φI φR R h1 h2 s hs⟩

end Alignment.Shadows.InvariantRegion.header_invariance_S

/-! ## `InvariantRegion.header.invariance.phi` (blind)

Text: "The state variables ... remain in a physically meaningful region for all t ≥ 0 (for the
correct field below; this is not proved here ...): [...] * φ_I, φ_R ≥ 0 — excess-degree
fractions" -/
namespace Alignment.Shadows.InvariantRegion.header_invariance_phi

open Alignment.Shadows.InvariantRegion.Shared2

@[sa_reference "InvariantRegion.header.invariance.phi"]
def T : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → InitOK ψ θ φI φR R → ∀ t : ℝ, 0 ≤ t → 0 ≤ φI t ∧ 0 ≤ φR t

/-- S1: φ_I stays nonnegative. -/
@[sa_shadow "InvariantRegion.header.invariance.phi" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → InitOK ψ θ φI φR R → ∀ t : ℝ, 0 ≤ t → 0 ≤ φI t
/-- S2: φ_R stays nonnegative. -/
@[sa_shadow "InvariantRegion.header.invariance.phi" 2]
def S2 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → InitOK ψ θ φI φR R → ∀ t : ℝ, 0 ≤ t → 0 ≤ φR t

@[sa_ref_forward "InvariantRegion.header.invariance.phi" 1] theorem ref_fwd1 : T → S1 :=
  fun t p n ψ θ φI φR R h1 h2 s hs => (t p n ψ θ φI φR R h1 h2 s hs).1
@[sa_ref_forward "InvariantRegion.header.invariance.phi" 2] theorem ref_fwd2 : T → S2 :=
  fun t p n ψ θ φI φR R h1 h2 s hs => (t p n ψ θ φI φR R h1 h2 s hs).2
@[sa_complete "InvariantRegion.header.invariance.phi"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun p n ψ θ φI φR R h1 h2 s hs =>
    ⟨s1 p n ψ θ φI φR R h1 h2 s hs, s2 p n ψ θ φI φR R h1 h2 s hs⟩

end Alignment.Shadows.InvariantRegion.header_invariance_phi

/-! ## `InvariantRegion.header.invariance.theta` (blind)

Text: "The state variables ... remain in a physically meaningful region for all t ≥ 0 (for the
correct field below; this is not proved here ...): [...] * θ ∈ [0, 1] — edge survival
probability" -/
namespace Alignment.Shadows.InvariantRegion.header_invariance_theta

open Alignment.Shadows.InvariantRegion.Shared2

@[sa_reference "InvariantRegion.header.invariance.theta"]
def T : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → InitOK ψ θ φI φR R → ∀ t : ℝ, 0 ≤ t → 0 ≤ θ t ∧ θ t ≤ 1

/-- S1: θ stays nonnegative. -/
@[sa_shadow "InvariantRegion.header.invariance.theta" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → InitOK ψ θ φI φR R → ∀ t : ℝ, 0 ≤ t → 0 ≤ θ t
/-- S2: θ stays at most one. -/
@[sa_shadow "InvariantRegion.header.invariance.theta" 2]
def S2 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → InitOK ψ θ φI φR R → ∀ t : ℝ, 0 ≤ t → θ t ≤ 1

@[sa_ref_forward "InvariantRegion.header.invariance.theta" 1] theorem ref_fwd1 : T → S1 :=
  fun t p n ψ θ φI φR R h1 h2 s hs => (t p n ψ θ φI φR R h1 h2 s hs).1
@[sa_ref_forward "InvariantRegion.header.invariance.theta" 2] theorem ref_fwd2 : T → S2 :=
  fun t p n ψ θ φI φR R h1 h2 s hs => (t p n ψ θ φI φR R h1 h2 s hs).2
@[sa_complete "InvariantRegion.header.invariance.theta"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun p n ψ θ φI φR R h1 h2 s hs =>
    ⟨s1 p n ψ θ φI φR R h1 h2 s hs, s2 p n ψ θ φI φR R h1 h2 s hs⟩

end Alignment.Shadows.InvariantRegion.header_invariance_theta

/-! ## `InvariantRegion.header.model` (blind)

Text (abridged): "The expanded single-type SIR EBCM (Volz 2008, Miller 2011) has ODE variables θ,
φ_I, φ_R, R with the vector field: dθ/dt = −β φ_I dφ_I/dt = β φ_I ψ″(θ) / ψ′(1) − (β + γ) φ_I
dφ_R/dt = γ φ_I dR/dt = γ (1 − ψ(θ) − R) (The φ_I equation follows from φ_I = θ − φ_S − φ_R with
φ_S = ψ′(θ)/ψ′(1); it is the form the Julia builders integrate. ...) Derived observables ...:
S = ψ(θ) I = 1 − S − R ← by definition; so S + I + R = 1 identically φ_S = ψ′(θ)/ψ′(1)"

The vector field itself is a definition (used by the other blocks through `Shared2`). The
proposition in the text is the derivation: if θ and φ_R follow their equations and
φ_I = θ − ψ′(θ)/ψ′(1) − φ_R, then φ_I follows the stated φ_I equation. "S + I + R = 1" holds by the
definition I := 1 − S − R and is not a separate requirement; the Julia remark is not formalised. -/
namespace Alignment.Shadows.InvariantRegion.header_model

open Alignment.Shadows.InvariantRegion.Shared2

@[sa_reference "InvariantRegion.header.model"]
def T : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φR : ℝ → ℝ) (t : ℝ),
    HasDerivAt θ (-(p.β : ℝ) * (θ t - dpsiR ψ (θ t) / dpsiR ψ 1 - φR t)) t →
    HasDerivAt φR ((p.γ : ℝ) * (θ t - dpsiR ψ (θ t) / dpsiR ψ 1 - φR t)) t →
    HasDerivAt (fun s => θ s - dpsiR ψ (θ s) / dpsiR ψ 1 - φR s)
      (correctR p ψ (θ t) (θ t - dpsiR ψ (θ t) / dpsiR ψ 1 - φR t)) t

/-- S1: the φ_I equation follows from φ_I = θ − φ_S − φ_R. -/
@[sa_shadow "InvariantRegion.header.model" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φR : ℝ → ℝ) (t : ℝ),
    HasDerivAt θ (-(p.β : ℝ) * (θ t - dpsiR ψ (θ t) / dpsiR ψ 1 - φR t)) t →
    HasDerivAt φR ((p.γ : ℝ) * (θ t - dpsiR ψ (θ t) / dpsiR ψ 1 - φR t)) t →
    HasDerivAt (fun s => θ s - dpsiR ψ (θ s) / dpsiR ψ 1 - φR s)
      (correctR p ψ (θ t) (θ t - dpsiR ψ (θ t) / dpsiR ψ 1 - φR t)) t

@[sa_ref_forward "InvariantRegion.header.model" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "InvariantRegion.header.model"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.InvariantRegion.header_model

/-! ## `InvariantRegion.header.thetaFace.b` (blind)

Text: "This constraint follows from θ = φ_S + φ_I + φ_R with φ_S, φ_R ≥ 0 (`phi_I_le_theta`)."

"This constraint" is φ_I ≤ θ (the θ = 0 face). -/
namespace Alignment.Shadows.InvariantRegion.header_thetaFace_b

@[sa_reference "InvariantRegion.header.thetaFace.b"]
def T : Prop := ∀ θ φS φI φR : ℚ, θ = φS + φI + φR → 0 ≤ φS → 0 ≤ φR → φI ≤ θ

/-- S1: θ = φ_S + φ_I + φ_R with φ_S, φ_R ≥ 0 gives φ_I ≤ θ. -/
@[sa_shadow "InvariantRegion.header.thetaFace.b" 1]
def S1 : Prop := ∀ θ φS φI φR : ℚ, θ = φS + φI + φR → 0 ≤ φS → 0 ≤ φR → φI ≤ θ

@[sa_ref_forward "InvariantRegion.header.thetaFace.b" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "InvariantRegion.header.thetaFace.b"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.InvariantRegion.header_thetaFace_b

/-! ## `InvariantRegion.header.thetaFace.c` (blind)

Text: "The factor 1/θ in the φ_I equation used in this file is an artefact of an incorrect form; the
correct equation dφ_I/dt = β φ_I ψ″(θ)/ψ′(1) − (β + γ) φ_I has no singularity at θ = 0."

S1: the correct φ_I field is continuous in θ at θ = 0; S2: the form with 1/θ is not the correct
field (it differs at some state). -/
namespace Alignment.Shadows.InvariantRegion.header_thetaFace_c

open Alignment.Shadows.InvariantRegion.Shared2

@[sa_reference "InvariantRegion.header.thetaFace.c"]
def T : Prop :=
  (∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (φI : ℝ),
      ContinuousAt (fun θ => correctR p ψ θ φI) 0) ∧
  (∃ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI : ℚ), wrongQ p ψ θ φI ≠ correctQ p ψ θ φI)

/-- S1: the correct field has no singularity at θ = 0. -/
@[sa_shadow "InvariantRegion.header.thetaFace.c" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (φI : ℝ), ContinuousAt (fun θ => correctR p ψ θ φI) 0
/-- S2: the 1/θ form is not the correct field. -/
@[sa_shadow "InvariantRegion.header.thetaFace.c" 2]
def S2 : Prop :=
  ∃ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI : ℚ), wrongQ p ψ θ φI ≠ correctQ p ψ θ φI

@[sa_ref_forward "InvariantRegion.header.thetaFace.c" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "InvariantRegion.header.thetaFace.c" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "InvariantRegion.header.thetaFace.c"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.InvariantRegion.header_thetaFace_c

/-! ## `InvariantRegion.phiIDotFactors.b` (blind)

Text: "so along a solution φ_I keeps its sign and {φ_I = 0} is invariant; the sign of dφ_I/dt also
depends on the second factor. [...] here we record the factorization for the form
(β φ_I / θ)(ψ′(θ)/ψ′(1)) − (β + γ) φ_I used in this file (the correct field is
`phi_I_dot_correct_factors`)."

S1: the factorization of the file's form, `φ_I · ((β/θ)(ψ′(θ)/ψ′(1)) − (β + γ))`.
-- AMBIGUITY: "along a solution": read for solutions of the model (the correct field, header.model),
whose φ_I component has the same factor φ_I: {φ_I = 0} is invariant (S2) and a positive φ_I stays
positive (S3), for t ≥ 0. S4: the sign of the file's form also depends on the second factor (two
states with the same φ_I > 0 and opposite signs). -/
namespace Alignment.Shadows.InvariantRegion.phiIDotFactors_b

open Alignment.Shadows.InvariantRegion.Shared2

@[sa_reference "InvariantRegion.phiIDotFactors.b"]
def T : Prop :=
  (∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI : ℚ),
      wrongQ p ψ θ φI = φI * (p.β / θ * (dpsiQ ψ θ / dpsiQ ψ 1) - (p.β + p.γ))) ∧
  (∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
      IsSol p ψ θ φI φR R → φI 0 = 0 → ∀ t : ℝ, 0 ≤ t → φI t = 0) ∧
  (∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
      IsSol p ψ θ φI φR R → 0 < φI 0 → ∀ t : ℝ, 0 ≤ t → 0 < φI t) ∧
  (∃ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ₁ θ₂ φI : ℚ), 0 < φI ∧
      0 < wrongQ p ψ θ₁ φI ∧ wrongQ p ψ θ₂ φI < 0)

/-- S1: the factorization of the file's φ_I form. -/
@[sa_shadow "InvariantRegion.phiIDotFactors.b" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI : ℚ),
    wrongQ p ψ θ φI = φI * (p.β / θ * (dpsiQ ψ θ / dpsiQ ψ 1) - (p.β + p.γ))
/-- S2: {φ_I = 0} is invariant along solutions. -/
@[sa_shadow "InvariantRegion.phiIDotFactors.b" 2]
def S2 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → φI 0 = 0 → ∀ t : ℝ, 0 ≤ t → φI t = 0
/-- S3: a positive φ_I stays positive along solutions. -/
@[sa_shadow "InvariantRegion.phiIDotFactors.b" 3]
def S3 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI φR R : ℝ → ℝ),
    IsSol p ψ θ φI φR R → 0 < φI 0 → ∀ t : ℝ, 0 ≤ t → 0 < φI t
/-- S4: the sign of dφ_I/dt also depends on the second factor. -/
@[sa_shadow "InvariantRegion.phiIDotFactors.b" 4]
def S4 : Prop :=
  ∃ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ₁ θ₂ φI : ℚ), 0 < φI ∧
    0 < wrongQ p ψ θ₁ φI ∧ wrongQ p ψ θ₂ φI < 0

@[sa_ref_forward "InvariantRegion.phiIDotFactors.b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "InvariantRegion.phiIDotFactors.b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "InvariantRegion.phiIDotFactors.b" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "InvariantRegion.phiIDotFactors.b" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2
@[sa_complete "InvariantRegion.phiIDotFactors.b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.InvariantRegion.phiIDotFactors_b

/-! ## `InvariantRegion.phiIDotCorrectZeroAtBoundary` (blind)

Text: "The correct φ_I field β φ_I ψ″(θ)/ψ′(1) − (β + γ) φ_I vanishes at φ_I = 0." -/
namespace Alignment.Shadows.InvariantRegion.phiIDotCorrectZeroAtBoundary

open Alignment.Shadows.InvariantRegion.Shared2

@[sa_reference "InvariantRegion.phiIDotCorrectZeroAtBoundary"]
def T : Prop := ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ : ℚ), correctQ p ψ θ 0 = 0

/-- S1: the correct φ_I field vanishes at φ_I = 0. -/
@[sa_shadow "InvariantRegion.phiIDotCorrectZeroAtBoundary" 1]
def S1 : Prop := ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ : ℚ), correctQ p ψ θ 0 = 0

@[sa_ref_forward "InvariantRegion.phiIDotCorrectZeroAtBoundary" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t
@[sa_complete "InvariantRegion.phiIDotCorrectZeroAtBoundary"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.InvariantRegion.phiIDotCorrectZeroAtBoundary

/-! ## `InvariantRegion.phiIDotCorrectFactors` (blind)

Text: "The correct φ_I field factors as φ_I · (β ψ″(θ)/ψ′(1) − (β + γ)), with no condition on θ:
unlike the form with 1/θ, it is regular at θ = 0."

S1: the factorization for all θ (no condition); S2: the correct field is continuous in θ at 0;
S3 ("unlike the form with 1/θ"): the 1/θ form is not continuous at θ = 0 for some PGF and φ_I. -/
namespace Alignment.Shadows.InvariantRegion.phiIDotCorrectFactors

open Alignment.Shadows.InvariantRegion.Shared2

@[sa_reference "InvariantRegion.phiIDotCorrectFactors"]
def T : Prop :=
  (∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI : ℚ),
      correctQ p ψ θ φI = φI * (p.β * ddpsiQ ψ θ / dpsiQ ψ 1 - (p.β + p.γ))) ∧
  (∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (φI : ℝ),
      ContinuousAt (fun θ => correctR p ψ θ φI) 0) ∧
  (∃ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (φI : ℝ),
      ¬ ContinuousAt (fun θ => wrongR p ψ θ φI) 0)

/-- S1: the correct field factors as φ_I · (β ψ″(θ)/ψ′(1) − (β + γ)), for every θ. -/
@[sa_shadow "InvariantRegion.phiIDotCorrectFactors" 1]
def S1 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (θ φI : ℚ),
    correctQ p ψ θ φI = φI * (p.β * ddpsiQ ψ θ / dpsiQ ψ 1 - (p.β + p.γ))
/-- S2: the correct field is regular at θ = 0. -/
@[sa_shadow "InvariantRegion.phiIDotCorrectFactors" 2]
def S2 : Prop :=
  ∀ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (φI : ℝ), ContinuousAt (fun θ => correctR p ψ θ φI) 0
/-- S3: the 1/θ form is not regular at θ = 0. -/
@[sa_shadow "InvariantRegion.phiIDotCorrectFactors" 3]
def S3 : Prop :=
  ∃ (p : EBCMParams) (n : ℕ) (ψ : PolyPGF n) (φI : ℝ), ¬ ContinuousAt (fun θ => wrongR p ψ θ φI) 0

@[sa_ref_forward "InvariantRegion.phiIDotCorrectFactors" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "InvariantRegion.phiIDotCorrectFactors" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "InvariantRegion.phiIDotCorrectFactors" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2
@[sa_complete "InvariantRegion.phiIDotCorrectFactors"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.InvariantRegion.phiIDotCorrectFactors

/-! ## `InvariantRegion.phiILeTheta` (blind)

Text: "Edge conservation: θ = φ_S + φ_I + φ_R with φ_S, φ_R ≥ 0 gives φ_I ≤ θ." -/
namespace Alignment.Shadows.InvariantRegion.phiILeTheta

@[sa_reference "InvariantRegion.phiILeTheta"]
def T : Prop := ∀ θ φS φI φR : ℚ, θ = φS + φI + φR → 0 ≤ φS → 0 ≤ φR → φI ≤ θ

/-- S1: edge conservation gives φ_I ≤ θ. -/
@[sa_shadow "InvariantRegion.phiILeTheta" 1]
def S1 : Prop := ∀ θ φS φI φR : ℚ, θ = φS + φI + φR → 0 ≤ φS → 0 ≤ φR → φI ≤ θ

@[sa_ref_forward "InvariantRegion.phiILeTheta" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "InvariantRegion.phiILeTheta"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.InvariantRegion.phiILeTheta

end
