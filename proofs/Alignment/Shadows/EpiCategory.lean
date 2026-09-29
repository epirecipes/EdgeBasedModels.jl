import Alignment.Registry
import EBCMCategory.EpiCategory
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Blind shadow sets for group `EpiCategory`

Written blind: the author read only the claims' entries in `claims_blind.yaml`,
`Alignment/DataTypes/EpiCategory.md`, `Alignment/README.md`, `Example/ExampleShadows.lean` and
`SA-PASS_SKILL.md`. No trusted source file, theorem statement, definition body, checker or report
was opened.

Vocabulary (from `DataTypes/EpiCategory.md`):
* `PGFData` (fields `mean` = ψ'(1), `secondFactorial` = ψ''(1)); `PGFData.poisson κ hκ` is
  "the Poisson PGF with mean κ";
* `PGFData.excessDegree` ("the excess degree ratio ψ''(1)/ψ'(1)") and `PGFData.variance`
  ("Var(k) = ψ''(1) + ψ'(1) − ψ'(1)²"). The docstrings say these represent the text's notions,
  so the shadows use them directly (per the author guidelines) instead of restating them;
* `SIRParams` (`β`, `γ` > 0) and `SIRParams.transmissibility` ("T = β/(β+γ)");
* `EpiModel` (`dim`, `R0`) with the refinement preorder: `M₁ ≤ M₂` iff `M₂` carries at least as
  much structural information as `M₁`; `nodeModel p κ` (node-based SIR, mean degree κ) and
  `edgeModel p ψ` (edge-based SIR on a network with degree PGF data ψ).

Note (no shadow depends on it): `PGFData` holds only the two numbers ψ'(1) and ψ''(1), not a
function, so "Poisson" can only be expressed as `PGFData.poisson κ hκ`. A literal reading over
genuine PGFs (ψ(x) = exp(κ(x − 1))) cannot be tied to `PGFData` and is not used.

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace). Ids of that pass not formalised (remarks on proof status, on which notions the library
defines, or cited results needing models the vocabulary lacks): `header.twoCategories`.
-/

/-! ## `EpiCategory.R1`

Text: "**Result 1.** For Poisson, the excess degree equals the mean degree." -/
namespace Alignment.Shadows.EpiCategory.R1

-- AMBIGUITY: "the mean degree" read as the Poisson parameter κ (S1) or as the PGF's own mean
-- ψ'(1) = `(PGFData.poisson κ hκ).mean` (S2). Both readings are defensible, so both are required.
-- AMBIGUITY: "the excess degree" read as the mean excess degree ψ''(1)/ψ'(1)
-- (`PGFData.excessDegree`). "Equals the mean degree" compares numbers, so the claim is not
-- about the excess degree *distribution*.
-- AMBIGUITY: "For Poisson" read as "for every Poisson degree distribution", i.e. for every mean
-- κ > 0, `PGFData.poisson κ hκ`. It is not read as "for every ψ with ψ''(1) = ψ'(1)²", because
-- `PGFData` has no notion of "being Poisson" other than `PGFData.poisson`.

/-- Intended statement: for every κ > 0, the Poisson PGF with mean κ has excess degree
ψ''(1)/ψ'(1) equal to κ and equal to its own mean ψ'(1). -/
@[sa_reference "EpiCategory.R1"]
def T : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ),
    PGFData.excessDegree (PGFData.poisson κ hκ) = κ ∧
      PGFData.excessDegree (PGFData.poisson κ hκ) = (PGFData.poisson κ hκ).mean

/-- S1: the excess degree of the Poisson PGF with mean κ equals κ. -/
@[sa_shadow "EpiCategory.R1" 1]
def S1 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ), PGFData.excessDegree (PGFData.poisson κ hκ) = κ

/-- S2: the excess degree of the Poisson PGF equals its mean ψ'(1). -/
@[sa_shadow "EpiCategory.R1" 2]
def S2 : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ),
    PGFData.excessDegree (PGFData.poisson κ hκ) = (PGFData.poisson κ hκ).mean

@[sa_ref_forward "EpiCategory.R1" 1]
theorem ref_fwd1 : T → S1 := fun t κ hκ => (t κ hκ).1

@[sa_ref_forward "EpiCategory.R1" 2]
theorem ref_fwd2 : T → S2 := fun t κ hκ => (t κ hκ).2

@[sa_complete "EpiCategory.R1"]
theorem complete (s1 : S1) (s2 : S2) : T := fun κ hκ => ⟨s1 κ hκ, s2 κ hκ⟩

end Alignment.Shadows.EpiCategory.R1

/-! ## `EpiCategory.R2`

Text: "**Result 2.** For Poisson, the variance equals the mean (equidispersion)." -/
namespace Alignment.Shadows.EpiCategory.R2

-- AMBIGUITY: "the mean" read as the Poisson parameter κ (S1) or as the PGF's own mean
-- ψ'(1) = `(PGFData.poisson κ hκ).mean` (S2). Both are required.
-- AMBIGUITY: "(equidispersion)" read as the name of the property "variance = mean". It is not
-- a separate requirement stated through `PGFData.dispersionIndex` (σ²/κ = 1), which is the same
-- property whenever κ > 0.
-- AMBIGUITY: "the variance" read as the degree variance `PGFData.variance`
-- (ψ''(1) + ψ'(1) − ψ'(1)²); "For Poisson" is read as in R1.

/-- Intended statement: for every κ > 0, the Poisson degree distribution with mean κ has degree
variance equal to κ and equal to its PGF mean ψ'(1). -/
@[sa_reference "EpiCategory.R2"]
def T : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ),
    PGFData.variance (PGFData.poisson κ hκ) = κ ∧
      PGFData.variance (PGFData.poisson κ hκ) = (PGFData.poisson κ hκ).mean

/-- S1: the variance of the Poisson distribution with mean κ equals κ. -/
@[sa_shadow "EpiCategory.R2" 1]
def S1 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ), PGFData.variance (PGFData.poisson κ hκ) = κ

/-- S2: the variance of the Poisson distribution equals its PGF mean ψ'(1). -/
@[sa_shadow "EpiCategory.R2" 2]
def S2 : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ), PGFData.variance (PGFData.poisson κ hκ) = (PGFData.poisson κ hκ).mean

@[sa_ref_forward "EpiCategory.R2" 1]
theorem ref_fwd1 : T → S1 := fun t κ hκ => (t κ hκ).1

@[sa_ref_forward "EpiCategory.R2" 2]
theorem ref_fwd2 : T → S2 := fun t κ hκ => (t κ hκ).2

@[sa_complete "EpiCategory.R2"]
theorem complete (s1 : S1) (s2 : S2) : T := fun κ hκ => ⟨s1 κ hκ, s2 κ hκ⟩

end Alignment.Shadows.EpiCategory.R2

/-! ## `EpiCategory.transmissibilityPos`

Text: "Transmissibility is positive." -/
namespace Alignment.Shadows.EpiCategory.transmissibilityPos

-- AMBIGUITY: "positive" read as strictly positive (0 < T), not 0 ≤ T. The claim holds for all
-- SIR parameters (β, γ > 0); "Transmissibility" is `SIRParams.transmissibility`
-- (T = β/(β+γ), per its docstring).

/-- Intended statement: for all SIR parameters, the transmissibility is strictly positive. -/
@[sa_reference "EpiCategory.transmissibilityPos"]
def T : Prop := ∀ p : SIRParams, 0 < p.transmissibility

/-- S1: the transmissibility is strictly positive for every SIR parameter set (one atomic
requirement). -/
@[sa_shadow "EpiCategory.transmissibilityPos" 1]
def S1 : Prop := ∀ p : SIRParams, 0 < p.transmissibility

@[sa_ref_forward "EpiCategory.transmissibilityPos" 1]
theorem ref_fwd1 : T → S1 := fun t p => t p

@[sa_complete "EpiCategory.transmissibilityPos"]
theorem complete (s1 : S1) : T := fun p => s1 p

end Alignment.Shadows.EpiCategory.transmissibilityPos

/-! ## `EpiCategory.transmissibilityLtOne`

Text: "Transmissibility is less than 1." -/
namespace Alignment.Shadows.EpiCategory.transmissibilityLtOne

-- AMBIGUITY: "less than 1" read as strict (T < 1), for all SIR parameters (β, γ > 0).

/-- Intended statement: for all SIR parameters, the transmissibility is strictly below 1. -/
@[sa_reference "EpiCategory.transmissibilityLtOne"]
def T : Prop := ∀ p : SIRParams, p.transmissibility < 1

/-- S1: the transmissibility is strictly less than one for every SIR parameter set. -/
@[sa_shadow "EpiCategory.transmissibilityLtOne" 1]
def S1 : Prop := ∀ p : SIRParams, p.transmissibility < 1

@[sa_ref_forward "EpiCategory.transmissibilityLtOne" 1]
theorem ref_fwd1 : T → S1 := fun t p => t p

@[sa_complete "EpiCategory.transmissibilityLtOne"]
theorem complete (s1 : S1) : T := fun p => s1 p

end Alignment.Shadows.EpiCategory.transmissibilityLtOne

/-! ## `EpiCategory.R3`

Text: "**Result 3.** The edge model always refines the node model."

The module header defines refinement: `M₁ ≤ M₂` iff `M₂` carries at least as much structural
information as `M₁`. "The edge model refines the node model" is therefore
`nodeModel … ≤ edgeModel …`. -/
namespace Alignment.Shadows.EpiCategory.R3

-- AMBIGUITY: "always" together with "the edge model" / "the node model". Two readings are
-- defensible and both are required:
--   S1 (corresponding models): for all SIR parameters p and every network ψ, the node model of
--      the same epidemic, with mean degree κ = ψ'(1), is refined by the edge model:
--      `nodeModel p ψ.mean ≤ edgeModel p ψ`;
--   S2 (unconditional in κ): for all p, every κ and every ψ, `nodeModel p κ ≤ edgeModel p ψ`.
-- A third reading, with different SIR parameters for the two models, is not used: the definite
-- articles ("the edge model", "the node model") point to models of the same epidemic (same p).
-- AMBIGUITY: "refines" read as the non-strict refinement preorder `≤` from the header, with
-- direction node ≤ edge (the edge model carries at least as much information).

/-- Intended statement: for all SIR parameters, the edge model refines the node model, both for
the corresponding node model (κ = ψ'(1)) and for a node model with any κ. -/
@[sa_reference "EpiCategory.R3"]
def T : Prop :=
  (∀ (p : SIRParams) (ψ : PGFData), nodeModel p ψ.mean ≤ edgeModel p ψ) ∧
    (∀ (p : SIRParams) (κ : ℚ) (ψ : PGFData), nodeModel p κ ≤ edgeModel p ψ)

/-- S1: the edge model on a network with PGF data ψ refines the node model with κ = ψ'(1). -/
@[sa_shadow "EpiCategory.R3" 1]
def S1 : Prop := ∀ (p : SIRParams) (ψ : PGFData), nodeModel p ψ.mean ≤ edgeModel p ψ

/-- S2: the edge model refines the node model for every mean degree κ of the node model. -/
@[sa_shadow "EpiCategory.R3" 2]
def S2 : Prop := ∀ (p : SIRParams) (κ : ℚ) (ψ : PGFData), nodeModel p κ ≤ edgeModel p ψ

@[sa_ref_forward "EpiCategory.R3" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "EpiCategory.R3" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "EpiCategory.R3"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.EpiCategory.R3

/-! ## `EpiCategory.R4`

Text: "**Result 4.** For Poisson networks, both models compute the same R₀." -/
namespace Alignment.Shadows.EpiCategory.R4

-- AMBIGUITY: "For Poisson networks": the network has the Poisson degree PGF
-- `PGFData.poisson κ hκ` for some κ > 0, and "both models" are the edge model on that network
-- and the node model of the same epidemic (same SIR parameters p). The node model's mean degree
-- is read as the Poisson parameter κ (S1) or as the network PGF's mean ψ'(1) =
-- `(PGFData.poisson κ hκ).mean` (S2). Both are required.
-- AMBIGUITY: "compute the same R₀" read as equality of the models' `R0` observables. No
-- particular closed form for R₀ is claimed.

/-- Intended statement: for all SIR parameters and every Poisson network (mean κ > 0), the node
model and the edge model have equal R₀, under both readings of the node model's mean degree. -/
@[sa_reference "EpiCategory.R4"]
def T : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
    (nodeModel p κ).R0 = (edgeModel p (PGFData.poisson κ hκ)).R0 ∧
      (nodeModel p (PGFData.poisson κ hκ).mean).R0 = (edgeModel p (PGFData.poisson κ hκ)).R0

/-- S1: the node model with mean degree κ and the edge model on the Poisson(κ) network have the
same R₀. -/
@[sa_shadow "EpiCategory.R4" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
    (nodeModel p κ).R0 = (edgeModel p (PGFData.poisson κ hκ)).R0

/-- S2: the node model with mean degree ψ'(1) of the Poisson network and the edge model on that
network have the same R₀. -/
@[sa_shadow "EpiCategory.R4" 2]
def S2 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
    (nodeModel p (PGFData.poisson κ hκ).mean).R0 = (edgeModel p (PGFData.poisson κ hκ)).R0

@[sa_ref_forward "EpiCategory.R4" 1]
theorem ref_fwd1 : T → S1 := fun t p κ hκ => (t p κ hκ).1

@[sa_ref_forward "EpiCategory.R4" 2]
theorem ref_fwd2 : T → S2 := fun t p κ hκ => (t p κ hκ).2

@[sa_complete "EpiCategory.R4"]
theorem complete (s1 : S1) (s2 : S2) : T := fun p κ hκ => ⟨s1 p κ hκ, s2 p κ hκ⟩

end Alignment.Shadows.EpiCategory.R4

noncomputable section

/-! ## `EpiCategory.dispersionIndexOneIffPoisson` (blind)

Text: "Index of dispersion: σ²/κ. Poisson ⇒ dispersion index 1 (`poisson_dispersion_eq_one`). The
converse is false for degree distributions: the law with P(0) = P(2) = 1/2, ψ(u) = (1 + u²)/2, has
mean 1 and variance 1 but is not Poisson."

S1: `dispersionIndex` is σ²/κ with σ² = ψ''(1) + ψ'(1) − ψ'(1)² in primitive terms; S2: the
Poisson record has dispersion index 1. The converse fails at the level of degree distributions:
the law's PGF `ψ(u) = (1 + u²)/2` has mean ψ'(1) = 1 (S3) and variance ψ''(1) + ψ'(1) − ψ'(1)² = 1
(S4), its moment record ⟨1, 1⟩ has dispersion index 1 (S5), and ψ is no Poisson PGF
`u ↦ e^{λ(u−1)}` (S6). -/
namespace Alignment.Shadows.EpiCategory.dispersionIndexOneIffPoisson

/-- PGF of the law P(0) = P(2) = 1/2. -/
def psiMix (u : ℝ) : ℝ := (1 + u ^ 2) / 2
/-- The moment record of that law: ψ'(1) = 1, ψ''(1) = 1. -/
def mixRecord : PGFData := ⟨1, 1, by norm_num, by norm_num⟩

@[sa_reference "EpiCategory.dispersionIndexOneIffPoisson"]
def T : Prop :=
  (∀ ψ : PGFData,
      ψ.dispersionIndex = (ψ.secondFactorial + ψ.mean - ψ.mean ^ 2) / ψ.mean) ∧
  (∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).dispersionIndex = 1) ∧
  deriv psiMix 1 = 1 ∧
  iteratedDeriv 2 psiMix 1 + deriv psiMix 1 - deriv psiMix 1 ^ 2 = 1 ∧
  mixRecord.dispersionIndex = 1 ∧
  (∀ lam : ℝ, psiMix ≠ fun u => Real.exp (lam * (u - 1)))

/-- S1: the index of dispersion is σ²/κ. -/
@[sa_shadow "EpiCategory.dispersionIndexOneIffPoisson" 1]
def S1 : Prop :=
  ∀ ψ : PGFData, ψ.dispersionIndex = (ψ.secondFactorial + ψ.mean - ψ.mean ^ 2) / ψ.mean
/-- S2: Poisson ⇒ dispersion index 1. -/
@[sa_shadow "EpiCategory.dispersionIndexOneIffPoisson" 2]
def S2 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).dispersionIndex = 1
/-- S3: the law (1 + u²)/2 has mean 1. -/
@[sa_shadow "EpiCategory.dispersionIndexOneIffPoisson" 3]
def S3 : Prop := deriv psiMix 1 = 1
/-- S4: the law (1 + u²)/2 has variance 1. -/
@[sa_shadow "EpiCategory.dispersionIndexOneIffPoisson" 4]
def S4 : Prop := iteratedDeriv 2 psiMix 1 + deriv psiMix 1 - deriv psiMix 1 ^ 2 = 1
/-- S5: its moment record has dispersion index 1. -/
@[sa_shadow "EpiCategory.dispersionIndexOneIffPoisson" 5]
def S5 : Prop := mixRecord.dispersionIndex = 1
/-- S6: the law (1 + u²)/2 is not Poisson. -/
@[sa_shadow "EpiCategory.dispersionIndexOneIffPoisson" 6]
def S6 : Prop := ∀ lam : ℝ, psiMix ≠ fun u => Real.exp (lam * (u - 1))

@[sa_ref_forward "EpiCategory.dispersionIndexOneIffPoisson" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "EpiCategory.dispersionIndexOneIffPoisson" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "EpiCategory.dispersionIndexOneIffPoisson" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "EpiCategory.dispersionIndexOneIffPoisson" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2.1
@[sa_ref_forward "EpiCategory.dispersionIndexOneIffPoisson" 5] theorem ref_fwd5 : T → S5 :=
  fun t => t.2.2.2.2.1
@[sa_ref_forward "EpiCategory.dispersionIndexOneIffPoisson" 6] theorem ref_fwd6 : T → S6 :=
  fun t => t.2.2.2.2.2
@[sa_complete "EpiCategory.dispersionIndexOneIffPoisson"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T :=
  ⟨s1, s2, s3, s4, s5, s6⟩

end Alignment.Shadows.EpiCategory.dispersionIndexOneIffPoisson

/-! ## `EpiCategory.header.refinementPreorder` (blind)

Text: "The only order is the preorder `M₁ ≤ M₂ iff M₁.dim ≤ M₂.dim`; "refinement" below means "has at
least as many state variables" and nothing more."

The order is the `Preorder EpiModel` instance; both directions of the iff are required ("nothing
more": R₀ plays no role). That no other order exists is a remark about the file. -/
namespace Alignment.Shadows.EpiCategory.header_refinementPreorder

@[sa_reference "EpiCategory.header.refinementPreorder"]
def T : Prop :=
  (∀ M₁ M₂ : EpiModel, M₁ ≤ M₂ → M₁.dim ≤ M₂.dim) ∧ (∀ M₁ M₂ : EpiModel, M₁.dim ≤ M₂.dim → M₁ ≤ M₂)

/-- S1: refinement implies at most as many state variables. -/
@[sa_shadow "EpiCategory.header.refinementPreorder" 1]
def S1 : Prop := ∀ M₁ M₂ : EpiModel, M₁ ≤ M₂ → M₁.dim ≤ M₂.dim
/-- S2: at most as many state variables implies refinement (whatever the R₀). -/
@[sa_shadow "EpiCategory.header.refinementPreorder" 2]
def S2 : Prop := ∀ M₁ M₂ : EpiModel, M₁.dim ≤ M₂.dim → M₁ ≤ M₂

@[sa_ref_forward "EpiCategory.header.refinementPreorder" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "EpiCategory.header.refinementPreorder" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "EpiCategory.header.refinementPreorder"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.EpiCategory.header_refinementPreorder

/-! ## `EpiCategory.dispersionIndexEqOneIff` (blind)

Text: "A `PGFData` record has dispersion index 1 iff it is the Poisson record of its own mean, i.e.
iff ψ''(1) = ψ'(1)²." -/
namespace Alignment.Shadows.EpiCategory.dispersionIndexEqOneIff

@[sa_reference "EpiCategory.dispersionIndexEqOneIff"]
def T : Prop :=
  (∀ ψ : PGFData, ψ.dispersionIndex = 1 → ψ = PGFData.poisson ψ.mean ψ.mean_pos) ∧
  (∀ ψ : PGFData, ψ = PGFData.poisson ψ.mean ψ.mean_pos → ψ.dispersionIndex = 1) ∧
  (∀ ψ : PGFData, ψ.dispersionIndex = 1 → ψ.secondFactorial = ψ.mean ^ 2) ∧
  (∀ ψ : PGFData, ψ.secondFactorial = ψ.mean ^ 2 → ψ.dispersionIndex = 1)

/-- S1: dispersion index 1 ⇒ the Poisson record of its mean. -/
@[sa_shadow "EpiCategory.dispersionIndexEqOneIff" 1]
def S1 : Prop := ∀ ψ : PGFData, ψ.dispersionIndex = 1 → ψ = PGFData.poisson ψ.mean ψ.mean_pos
/-- S2: the Poisson record of its mean ⇒ dispersion index 1. -/
@[sa_shadow "EpiCategory.dispersionIndexEqOneIff" 2]
def S2 : Prop := ∀ ψ : PGFData, ψ = PGFData.poisson ψ.mean ψ.mean_pos → ψ.dispersionIndex = 1
/-- S3: dispersion index 1 ⇒ ψ''(1) = ψ'(1)². -/
@[sa_shadow "EpiCategory.dispersionIndexEqOneIff" 3]
def S3 : Prop := ∀ ψ : PGFData, ψ.dispersionIndex = 1 → ψ.secondFactorial = ψ.mean ^ 2
/-- S4: ψ''(1) = ψ'(1)² ⇒ dispersion index 1. -/
@[sa_shadow "EpiCategory.dispersionIndexEqOneIff" 4]
def S4 : Prop := ∀ ψ : PGFData, ψ.secondFactorial = ψ.mean ^ 2 → ψ.dispersionIndex = 1

@[sa_ref_forward "EpiCategory.dispersionIndexEqOneIff" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "EpiCategory.dispersionIndexEqOneIff" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "EpiCategory.dispersionIndexEqOneIff" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "EpiCategory.dispersionIndexEqOneIff" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2
@[sa_complete "EpiCategory.dispersionIndexEqOneIff"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.EpiCategory.dispersionIndexEqOneIff

end
