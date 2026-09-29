import Alignment.Registry
import EBCMCategory.Hierarchy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Blind shadow sets for group `Hierarchy`

Written blind: the author read only the claims' entries in `claims_blind.yaml`,
`Alignment/DataTypes/Hierarchy.md`, `Alignment/README.md`, `Example/ExampleShadows.lean` and
`SA-PASS_SKILL.md`, and used `#check` on the listed data types and operations only.

Vocabulary used (from `DataTypes/Hierarchy.md`):

* `levelDim level N`: state-space dimension ("number of variables") of a modelling level for an
  `N`-node SIR network model; levels `ModelLevel.{fullStochastic, pairApproximation, edgeBased,
  meanField}` ("EBCM" = `edgeBased`, "Mean-field (SIR)" = `meanField`).
* `PGFData` (fields `mean` = ψ'(1), `secondFactorial` = ψ''(1)); `PGFData.poisson κ hκ` ("the
  Poisson PGF with mean κ"); `PGFData.excessDegree ψ` (= ψ''(1)/ψ'(1)).
* "Poisson" for `ψ : PGFData`: `ψ = PGFData.poisson ψ.mean ψ.mean_pos`; "excess degree = mean"
  (named "the exactness condition" in the text of Result 27): `ψ.excessDegree = ψ.mean`.
* `nodeModel p κ` (node-based SIR model, 3 state variables), `edgeModel p ψ` (edge-based SIR model,
  4 state variables), `EpiModel` with fields `dim : ℕ` and `R0 : ℚ` (learned by `#check`).

Shared reading of "lift" (Results 26-28, table rows 26-28):
-- AMBIGUITY: "lift". The DataTypes have no notion of "lift" or "lift space" (VOCAB-GAP). Read,
-- following the texts themselves ("lifts to an edge model via Poisson", "the Poisson lift is the
-- UNIQUE PGF", "the lift space is parameterised by PGFs with matching mean"): a lift of the node
-- model `nodeModel p κ` is the edge model `edgeModel p ψ` with the same SIR parameters `p` and a PGF
-- `ψ` whose mean matches the node model's mean degree `κ`; the (canonical) Poisson lift is
-- `edgeModel p (PGFData.poisson κ hκ)`. The alternative categorical reading "E lifts M iff
-- `coarseGrain E = M`" was considered and not used: `coarseGrain` preserves R₀ (its docstring), so
-- every lift would preserve R₀, which contradicts the texts singling out R₀-preservation for the
-- Poisson lift (Result 26) and the Poisson lift as the unique exact one (Result 27).

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace). Ids of that pass not formalised (remarks on proof status, on which notions the library
defines, or cited results needing models the vocabulary lacks): `header.stepsAreCoarseGrainings`.
-/

namespace Alignment.Shadows.Hierarchy

/-! ## Helpers for the literal (genuine PGF) reading

VOCAB-GAP: `PGFData` records only the first two factorial moments of a PGF, so quantifying over
`PGFData` is not quantifying over PGFs. Where a text quantifies over *all PGFs* ("the UNIQUE PGF",
"iff Poisson"), the text's generality is kept by an extra shadow over genuine degree distributions
`p : ℕ → ℝ` (weights `p k ≥ 0` summing to 1). For a PGF ψ(x) = ∑ p_k x^k with finite first and second
factorial moments, ψ'(1) = ∑ k p_k and ψ''(1) = ∑ k(k-1) p_k, which is how they are written below. -/

namespace Literal

/-- `p` is a degree distribution on ℕ: nonnegative weights with total mass 1. -/
def IsDegreeDist (p : ℕ → ℝ) : Prop := (∀ k, 0 ≤ p k) ∧ HasSum p 1

/-- The first and second factorial moments of `p` are finite (so ψ'(1), ψ''(1) exist). -/
def HasFiniteFactorialMoments (p : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => (k : ℝ) * p k) ∧ Summable (fun k : ℕ => (k : ℝ) * ((k : ℝ) - 1) * p k)

/-- ψ'(1) = ∑ k p_k: the mean degree. -/
noncomputable def pgfMean (p : ℕ → ℝ) : ℝ := ∑' k : ℕ, (k : ℝ) * p k

/-- ψ''(1) = ∑ k (k - 1) p_k: the second factorial moment. -/
noncomputable def pgfSecondFactorial (p : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) * ((k : ℝ) - 1) * p k

/-- The excess degree ψ''(1)/ψ'(1). -/
noncomputable def pgfExcessDegree (p : ℕ → ℝ) : ℝ := pgfSecondFactorial p / pgfMean p

/-- The Poisson(κ) weights e^{-κ} κ^k / k!. -/
noncomputable def poissonWeight (κ : ℝ) (k : ℕ) : ℝ := Real.exp (-κ) * κ ^ k / (k.factorial : ℝ)

end Literal

end Alignment.Shadows.Hierarchy

/-! ## `Hierarchy.table.R23`

Blind text: "| 23 | Mean-field < EBCM |" -/

namespace Alignment.Shadows.Hierarchy.table_R23

-- AMBIGUITY: "<" read as "has fewer state variables than" (`levelDim`), as in Result 23; no
-- range of N is given, so every N.

/-- Intended statement: for every network size N, the mean-field level has a smaller state-space
dimension than the EBCM (edge-based) level. -/
@[sa_reference "Hierarchy.table.R23"]
def T : Prop := ∀ N : ℕ, levelDim ModelLevel.meanField N < levelDim ModelLevel.edgeBased N

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "Hierarchy.table.R23" 1]
def S1 : Prop := ∀ N : ℕ, levelDim ModelLevel.meanField N < levelDim ModelLevel.edgeBased N

@[sa_ref_forward "Hierarchy.table.R23" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "Hierarchy.table.R23"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Hierarchy.table_R23

/-! ## `Hierarchy.table.R24`

Blind text: "| 24 | EBCM < Pair approximation (for N ≥ 1) |" -/

namespace Alignment.Shadows.Hierarchy.table_R24

-- AMBIGUITY: "<" read as "has fewer state variables than" (`levelDim`), as in Result 24.

/-- Intended statement: for every N ≥ 1, the EBCM level has a smaller state-space dimension than
the pair-approximation level. -/
@[sa_reference "Hierarchy.table.R24"]
def T : Prop :=
  ∀ N : ℕ, 1 ≤ N → levelDim ModelLevel.edgeBased N < levelDim ModelLevel.pairApproximation N

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "Hierarchy.table.R24" 1]
def S1 : Prop :=
  ∀ N : ℕ, 1 ≤ N → levelDim ModelLevel.edgeBased N < levelDim ModelLevel.pairApproximation N

@[sa_ref_forward "Hierarchy.table.R24" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "Hierarchy.table.R24"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Hierarchy.table_R24

/-! ## `Hierarchy.table.R25`

Blind text: "| 25 | EBCM → Mean-field is exact for Poisson networks |" -/

namespace Alignment.Shadows.Hierarchy.table_R25

-- AMBIGUITY: "exact" read as the exactness condition "excess degree = mean" (so named in the text
-- of Result 27), `ψ.excessDegree = ψ.mean`. A dynamical reading (EBCM trajectories coincide with
-- the mean-field SIR trajectories) is not expressible with the DataTypes (VOCAB-GAP: no
-- trajectories). "Poisson networks": networks whose degree PGF is `PGFData.poisson κ hκ`, any κ > 0.

/-- Intended statement: for every Poisson degree distribution (every mean κ > 0), the exactness
condition excess degree = mean holds. -/
@[sa_reference "Hierarchy.table.R25"]
def T : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).excessDegree = (PGFData.poisson κ hκ).mean

/-- S1: the whole statement (one direction only is claimed by the row). -/
@[sa_shadow "Hierarchy.table.R25" 1]
def S1 : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).excessDegree = (PGFData.poisson κ hκ).mean

@[sa_ref_forward "Hierarchy.table.R25" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "Hierarchy.table.R25"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Hierarchy.table_R25

/-! ## `Hierarchy.table.R26`

Blind text: "| 26 | Every node model has a canonical Poisson lift |" -/

namespace Alignment.Shadows.Hierarchy.table_R26

-- AMBIGUITY: "has a canonical Poisson lift". Existence alone is trivial (`edgeModel p
-- (PGFData.poisson κ hκ)` always exists), so the row is read as the summary of Result 26: the
-- canonical Poisson lift of `nodeModel p κ` is `edgeModel p (PGFData.poisson κ hκ)` (same SIR
-- parameters, Poisson with the node model's mean degree κ) and it is a lift in the sense of Result
-- 26, i.e. it preserves R₀. "Every node model" is read as every `nodeModel p κ` with κ > 0 (no
-- Poisson PGF exists for κ ≤ 0). The existential reading "some Poisson edge model preserves R₀" is
-- implied by this reading and is not a separate shadow.

/-- Intended statement: for all SIR parameters p and mean degrees κ > 0, the Poisson edge model
`edgeModel p (PGFData.poisson κ hκ)` has the same R₀ as the node model `nodeModel p κ`. -/
@[sa_reference "Hierarchy.table.R26"]
def T : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
    (edgeModel p (PGFData.poisson κ hκ)).R0 = (nodeModel p κ).R0

/-- S1: the canonical Poisson lift preserves R₀ (a single atomic requirement). -/
@[sa_shadow "Hierarchy.table.R26" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
    (edgeModel p (PGFData.poisson κ hκ)).R0 = (nodeModel p κ).R0

@[sa_ref_forward "Hierarchy.table.R26" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "Hierarchy.table.R26"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Hierarchy.table_R26

/-! ## `Hierarchy.R23`

Blind text: "**Result 23.** Mean-field has fewer variables than EBCM." -/

namespace Alignment.Shadows.Hierarchy.R23

-- "Number of variables" of a level = `levelDim level N` (DataTypes). No range of N is given
-- (contrast Result 24's "for N ≥ 1"), so every N.

/-- Intended statement: for every N, the mean-field level has fewer state variables than EBCM. -/
@[sa_reference "Hierarchy.R23"]
def T : Prop := ∀ N : ℕ, levelDim ModelLevel.meanField N < levelDim ModelLevel.edgeBased N

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "Hierarchy.R23" 1]
def S1 : Prop := ∀ N : ℕ, levelDim ModelLevel.meanField N < levelDim ModelLevel.edgeBased N

@[sa_ref_forward "Hierarchy.R23" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "Hierarchy.R23"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Hierarchy.R23

/-! ## `Hierarchy.R24`

Blind text: "**Result 24.** EBCM has fewer variables than pair approximation for N ≥ 1." -/

namespace Alignment.Shadows.Hierarchy.R24

/-- Intended statement: for every N ≥ 1, EBCM has fewer state variables than pair
approximation. -/
@[sa_reference "Hierarchy.R24"]
def T : Prop :=
  ∀ N : ℕ, 1 ≤ N → levelDim ModelLevel.edgeBased N < levelDim ModelLevel.pairApproximation N

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "Hierarchy.R24" 1]
def S1 : Prop :=
  ∀ N : ℕ, 1 ≤ N → levelDim ModelLevel.edgeBased N < levelDim ModelLevel.pairApproximation N

@[sa_ref_forward "Hierarchy.R24" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "Hierarchy.R24"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Hierarchy.R24

/-! ## `Hierarchy.R25`

Blind text: "**Result 25.** The EBCM → Mean-field step is exact iff Poisson." -/

namespace Alignment.Shadows.Hierarchy.R25

open Alignment.Shadows.Hierarchy.Literal

-- AMBIGUITY: "exact" read as the exactness condition excess degree = mean (so named in Result
-- 27), `ψ.excessDegree = ψ.mean`; a dynamical reading (EBCM trajectories reduce to mean-field SIR
-- trajectories) is not expressible with the DataTypes (VOCAB-GAP). "Poisson" for `ψ : PGFData`:
-- `ψ = PGFData.poisson ψ.mean ψ.mean_pos` (DataTypes). Split along the iff: S1 (Poisson ⇒
-- exact, for every Poisson PGF), S2 (exact ⇒ Poisson, over `PGFData`).
-- AMBIGUITY / VOCAB-GAP: "exact iff Poisson" quantifies over all degree distributions. Keeping
-- that generality over genuine PGFs (not only moment data) gives S3 for the "only if" direction.

/-- Intended statement: every Poisson PGF satisfies excess degree = mean, and every PGF (moment
data, and genuine degree distribution) satisfying excess degree = mean is the Poisson PGF with
its own mean. -/
@[sa_reference "Hierarchy.R25"]
def T : Prop :=
  (∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).excessDegree = (PGFData.poisson κ hκ).mean) ∧
    (∀ ψ : PGFData, ψ.excessDegree = ψ.mean → ψ = PGFData.poisson ψ.mean ψ.mean_pos) ∧
    (∀ p : ℕ → ℝ, IsDegreeDist p → HasFiniteFactorialMoments p → 0 < pgfMean p →
        pgfExcessDegree p = pgfMean p → ∀ k : ℕ, p k = poissonWeight (pgfMean p) k)

/-- S1 (Poisson ⇒ exact): every Poisson PGF satisfies excess degree = mean. -/
@[sa_shadow "Hierarchy.R25" 1]
def S1 : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).excessDegree = (PGFData.poisson κ hκ).mean

/-- S2 (exact ⇒ Poisson, over `PGFData`): a PGF with excess degree = mean is the Poisson PGF with
the same mean. -/
@[sa_shadow "Hierarchy.R25" 2]
def S2 : Prop := ∀ ψ : PGFData, ψ.excessDegree = ψ.mean → ψ = PGFData.poisson ψ.mean ψ.mean_pos

/-- S3 (exact ⇒ Poisson, over genuine PGFs, literal reading): a degree distribution with positive
mean and finite second factorial moment whose excess degree equals its mean is Poisson. -/
@[sa_shadow "Hierarchy.R25" 3]
def S3 : Prop :=
  ∀ p : ℕ → ℝ, IsDegreeDist p → HasFiniteFactorialMoments p → 0 < pgfMean p →
    pgfExcessDegree p = pgfMean p → ∀ k : ℕ, p k = poissonWeight (pgfMean p) k

@[sa_ref_forward "Hierarchy.R25" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "Hierarchy.R25" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "Hierarchy.R25" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2

@[sa_complete "Hierarchy.R25"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Hierarchy.R25

/-! ## `Hierarchy.R26`

Blind text: "**Result 26.** Every node model lifts to an edge model via Poisson, preserving R₀." -/

namespace Alignment.Shadows.Hierarchy.R26

-- AMBIGUITY: "Every node model" read as every `nodeModel p κ` with κ > 0 (no Poisson PGF exists
-- for κ ≤ 0). "lifts to an edge model via Poisson" read as the canonical Poisson lift
-- `edgeModel p (PGFData.poisson κ hκ)`: same SIR parameters, Poisson PGF with the node model's
-- mean degree κ (see the module header for the reading of "lift"). "preserving R₀": equal `R0`.
-- The existential reading ("some Poisson edge model has the same R₀") is implied and not a
-- separate shadow.

/-- Intended statement: for all SIR parameters p and κ > 0, the Poisson edge model
`edgeModel p (PGFData.poisson κ hκ)` has the same R₀ as `nodeModel p κ`. -/
@[sa_reference "Hierarchy.R26"]
def T : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
    (edgeModel p (PGFData.poisson κ hκ)).R0 = (nodeModel p κ).R0

/-- S1: the Poisson lift preserves R₀ (a single atomic requirement). -/
@[sa_shadow "Hierarchy.R26" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
    (edgeModel p (PGFData.poisson κ hκ)).R0 = (nodeModel p κ).R0

@[sa_ref_forward "Hierarchy.R26" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "Hierarchy.R26"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Hierarchy.R26

noncomputable section

/-! ## `Hierarchy.R27` (re-authored blind)

Text: "**Result 27.** For a two-moment record with mean κ, excess degree = mean forces
variance = mean, so the record is the Poisson record `poisson κ`
(`PGFData.dispersionIndex_eq_one_iff`). This does not make Poisson the unique degree distribution
with excess degree = mean: ψ(u) = (1 + u²)/2 has ψ''(1)/ψ'(1) = 1 = ψ'(1) and is not Poisson."

Records: `PGFData` with `excessDegree`, `variance` and `PGFData.poisson`. The counterexample is read
at the level of degree distributions, through its PGF `ψ(u) = (1 + u²)/2` as a real function; "not
Poisson" = not of the form `u ↦ e^{λ(u−1)}`. -/
namespace Alignment.Shadows.Hierarchy.R27

/-- The PGF `ψ(u) = (1 + u²)/2`. -/
def psiMix (u : ℝ) : ℝ := (1 + u ^ 2) / 2

@[sa_reference "Hierarchy.R27"]
def T : Prop :=
  (∀ ψ : PGFData, ψ.excessDegree = ψ.mean → ψ.variance = ψ.mean) ∧
  (∀ ψ : PGFData, ψ.excessDegree = ψ.mean → ψ = PGFData.poisson ψ.mean ψ.mean_pos) ∧
  iteratedDeriv 2 psiMix 1 / deriv psiMix 1 = 1 ∧ deriv psiMix 1 = 1 ∧
  (∀ lam : ℝ, psiMix ≠ fun u => Real.exp (lam * (u - 1)))

/-- S1: for records, excess degree = mean forces variance = mean. -/
@[sa_shadow "Hierarchy.R27" 1]
def S1 : Prop := ∀ ψ : PGFData, ψ.excessDegree = ψ.mean → ψ.variance = ψ.mean
/-- S2: such a record is the Poisson record of its mean. -/
@[sa_shadow "Hierarchy.R27" 2]
def S2 : Prop := ∀ ψ : PGFData, ψ.excessDegree = ψ.mean → ψ = PGFData.poisson ψ.mean ψ.mean_pos
/-- S3: `(1 + u²)/2` has `ψ''(1)/ψ'(1) = 1`. -/
@[sa_shadow "Hierarchy.R27" 3]
def S3 : Prop := iteratedDeriv 2 psiMix 1 / deriv psiMix 1 = 1
/-- S4: `(1 + u²)/2` has `ψ'(1) = 1`. -/
@[sa_shadow "Hierarchy.R27" 4]
def S4 : Prop := deriv psiMix 1 = 1
/-- S5: `(1 + u²)/2` is not a Poisson PGF. -/
@[sa_shadow "Hierarchy.R27" 5]
def S5 : Prop := ∀ lam : ℝ, psiMix ≠ fun u => Real.exp (lam * (u - 1))

@[sa_ref_forward "Hierarchy.R27" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Hierarchy.R27" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Hierarchy.R27" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Hierarchy.R27" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "Hierarchy.R27" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2
@[sa_complete "Hierarchy.R27"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.Hierarchy.R27

/-! ## `Hierarchy.R28` (re-authored blind)

Text: "**Result 28.** Some PGF record with mean κ (the Poisson record) gives an edge model with
R₀ = T·ψ''(1)/ψ'(1). Matching the mean does not preserve R₀: the edge model of a record ψ has the
node model's R₀ T·κ iff ψ''(1)/ψ'(1) = κ (`edge_lift_R0_eq_iff`)."

T = β/(β+γ); ψ''(1)/ψ'(1) = `secondFactorial / mean`; the node model with mean degree κ is
`nodeModel p κ`, the edge model of ψ is `edgeModel p ψ`. -/
namespace Alignment.Shadows.Hierarchy.R28

@[sa_reference "Hierarchy.R28"]
def T : Prop :=
  (∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).mean = κ) ∧
  (∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ), (edgeModel p (PGFData.poisson κ hκ)).R0 =
      p.β / (p.β + p.γ) *
        ((PGFData.poisson κ hκ).secondFactorial / (PGFData.poisson κ hκ).mean)) ∧
  (∃ (p : SIRParams) (ψ : PGFData), (edgeModel p ψ).R0 ≠ (nodeModel p ψ.mean).R0) ∧
  (∀ (p : SIRParams) (κ : ℚ), (nodeModel p κ).R0 = p.β / (p.β + p.γ) * κ) ∧
  (∀ (p : SIRParams) (ψ : PGFData) (κ : ℚ),
      (edgeModel p ψ).R0 = (nodeModel p κ).R0 → ψ.secondFactorial / ψ.mean = κ) ∧
  (∀ (p : SIRParams) (ψ : PGFData) (κ : ℚ),
      ψ.secondFactorial / ψ.mean = κ → (edgeModel p ψ).R0 = (nodeModel p κ).R0)

/-- S1: the Poisson record with mean κ has mean κ. -/
@[sa_shadow "Hierarchy.R28" 1]
def S1 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).mean = κ
/-- S2: its edge model has `R₀ = T·ψ''(1)/ψ'(1)`. -/
@[sa_shadow "Hierarchy.R28" 2]
def S2 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ), (edgeModel p (PGFData.poisson κ hκ)).R0 =
    p.β / (p.β + p.γ) * ((PGFData.poisson κ hκ).secondFactorial / (PGFData.poisson κ hκ).mean)
/-- S3: matching the mean does not preserve R₀. -/
@[sa_shadow "Hierarchy.R28" 3]
def S3 : Prop := ∃ (p : SIRParams) (ψ : PGFData), (edgeModel p ψ).R0 ≠ (nodeModel p ψ.mean).R0
/-- S4: the node model's R₀ is `T·κ`. -/
@[sa_shadow "Hierarchy.R28" 4]
def S4 : Prop := ∀ (p : SIRParams) (κ : ℚ), (nodeModel p κ).R0 = p.β / (p.β + p.γ) * κ
/-- S5: equal R₀ ⇒ `ψ''(1)/ψ'(1) = κ`. -/
@[sa_shadow "Hierarchy.R28" 5]
def S5 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData) (κ : ℚ),
    (edgeModel p ψ).R0 = (nodeModel p κ).R0 → ψ.secondFactorial / ψ.mean = κ
/-- S6: `ψ''(1)/ψ'(1) = κ` ⇒ equal R₀. -/
@[sa_shadow "Hierarchy.R28" 6]
def S6 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData) (κ : ℚ),
    ψ.secondFactorial / ψ.mean = κ → (edgeModel p ψ).R0 = (nodeModel p κ).R0

@[sa_ref_forward "Hierarchy.R28" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Hierarchy.R28" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Hierarchy.R28" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Hierarchy.R28" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "Hierarchy.R28" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2.1
@[sa_ref_forward "Hierarchy.R28" 6] theorem ref_fwd6 : T → S6 := fun t => t.2.2.2.2.2
@[sa_complete "Hierarchy.R28"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T :=
  ⟨s1, s2, s3, s4, s5, s6⟩

end Alignment.Shadows.Hierarchy.R28

/-! ## `Hierarchy.header.fullGtPair` (blind)

Text: "Epidemic models are compared here by the state-space dimension of an N-node SIR network model
(`levelDim`): Full stochastic (3^N) > Pair approximation (12N) [...] The first inequality holds
only for N ≥ 4 (`pair_lt_full`); for N = 3, 3³ = 27 < 36 = 12·3 (`full_lt_pair_three`)."

-- AMBIGUITY: "holds only for N ≥ 4" read for networks with at least one node (it fails for
1 ≤ N ≤ 3; at N = 0, 12·0 < 3⁰). -/
namespace Alignment.Shadows.Hierarchy.header_fullGtPair

@[sa_reference "Hierarchy.header.fullGtPair"]
def T : Prop :=
  (∀ N : ℕ, levelDim .fullStochastic N = 3 ^ N) ∧
  (∀ N : ℕ, levelDim .pairApproximation N = 12 * N) ∧
  (∀ N : ℕ, 4 ≤ N → levelDim .pairApproximation N < levelDim .fullStochastic N) ∧
  (∀ N : ℕ, 1 ≤ N → N ≤ 3 → ¬ levelDim .pairApproximation N < levelDim .fullStochastic N) ∧
  levelDim .fullStochastic 3 < levelDim .pairApproximation 3

/-- S1: the full stochastic model has 3^N variables. -/
@[sa_shadow "Hierarchy.header.fullGtPair" 1]
def S1 : Prop := ∀ N : ℕ, levelDim .fullStochastic N = 3 ^ N
/-- S2: the pair approximation has 12N variables. -/
@[sa_shadow "Hierarchy.header.fullGtPair" 2]
def S2 : Prop := ∀ N : ℕ, levelDim .pairApproximation N = 12 * N
/-- S3: full > pair for N ≥ 4. -/
@[sa_shadow "Hierarchy.header.fullGtPair" 3]
def S3 : Prop := ∀ N : ℕ, 4 ≤ N → levelDim .pairApproximation N < levelDim .fullStochastic N
/-- S4: full > pair fails for 1 ≤ N ≤ 3. -/
@[sa_shadow "Hierarchy.header.fullGtPair" 4]
def S4 : Prop :=
  ∀ N : ℕ, 1 ≤ N → N ≤ 3 → ¬ levelDim .pairApproximation N < levelDim .fullStochastic N
/-- S5: for N = 3, full < pair. -/
@[sa_shadow "Hierarchy.header.fullGtPair" 5]
def S5 : Prop := levelDim .fullStochastic 3 < levelDim .pairApproximation 3

@[sa_ref_forward "Hierarchy.header.fullGtPair" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Hierarchy.header.fullGtPair" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Hierarchy.header.fullGtPair" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Hierarchy.header.fullGtPair" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2.1
@[sa_ref_forward "Hierarchy.header.fullGtPair" 5] theorem ref_fwd5 : T → S5 :=
  fun t => t.2.2.2.2
@[sa_complete "Hierarchy.header.fullGtPair"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.Hierarchy.header_fullGtPair

/-! ## `Hierarchy.header.pairGtEbcmGtMeanField` (re-authored blind)

Text: "Pair approximation (12N) > EBCM (4) > Mean-field SIR (3)"

-- AMBIGUITY: N is not given; the first inequality is read for N ≥ 1 (at N = 0 the pair level has
0 variables). -/
namespace Alignment.Shadows.Hierarchy.header_pairGtEbcmGtMeanField

@[sa_reference "Hierarchy.header.pairGtEbcmGtMeanField"]
def T : Prop :=
  (∀ N : ℕ, 1 ≤ N → levelDim .edgeBased N < levelDim .pairApproximation N) ∧
  (∀ N : ℕ, levelDim .meanField N < levelDim .edgeBased N) ∧
  (∀ N : ℕ, levelDim .pairApproximation N = 12 * N) ∧
  (∀ N : ℕ, levelDim .edgeBased N = 4) ∧ (∀ N : ℕ, levelDim .meanField N = 3)

/-- S1: pair > EBCM (N ≥ 1). -/
@[sa_shadow "Hierarchy.header.pairGtEbcmGtMeanField" 1]
def S1 : Prop := ∀ N : ℕ, 1 ≤ N → levelDim .edgeBased N < levelDim .pairApproximation N
/-- S2: EBCM > mean-field. -/
@[sa_shadow "Hierarchy.header.pairGtEbcmGtMeanField" 2]
def S2 : Prop := ∀ N : ℕ, levelDim .meanField N < levelDim .edgeBased N
/-- S3: the pair level has 12N variables. -/
@[sa_shadow "Hierarchy.header.pairGtEbcmGtMeanField" 3]
def S3 : Prop := ∀ N : ℕ, levelDim .pairApproximation N = 12 * N
/-- S4: the EBCM has 4 variables. -/
@[sa_shadow "Hierarchy.header.pairGtEbcmGtMeanField" 4]
def S4 : Prop := ∀ N : ℕ, levelDim .edgeBased N = 4
/-- S5: mean-field SIR has 3 variables. -/
@[sa_shadow "Hierarchy.header.pairGtEbcmGtMeanField" 5]
def S5 : Prop := ∀ N : ℕ, levelDim .meanField N = 3

@[sa_ref_forward "Hierarchy.header.pairGtEbcmGtMeanField" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "Hierarchy.header.pairGtEbcmGtMeanField" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "Hierarchy.header.pairGtEbcmGtMeanField" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "Hierarchy.header.pairGtEbcmGtMeanField" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2.1
@[sa_ref_forward "Hierarchy.header.pairGtEbcmGtMeanField" 5] theorem ref_fwd5 : T → S5 :=
  fun t => t.2.2.2.2
@[sa_complete "Hierarchy.header.pairGtEbcmGtMeanField"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.Hierarchy.header_pairGtEbcmGtMeanField

/-! ## `Hierarchy.table.R27` (re-authored blind)

Text: "| 27 | Excess = mean forces variance = mean (records only) |" -/
namespace Alignment.Shadows.Hierarchy.table_R27

@[sa_reference "Hierarchy.table.R27"]
def T : Prop := ∀ ψ : PGFData, ψ.excessDegree = ψ.mean → ψ.variance = ψ.mean

/-- S1: for records, excess degree = mean forces variance = mean. -/
@[sa_shadow "Hierarchy.table.R27" 1]
def S1 : Prop := ∀ ψ : PGFData, ψ.excessDegree = ψ.mean → ψ.variance = ψ.mean

@[sa_ref_forward "Hierarchy.table.R27" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Hierarchy.table.R27"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Hierarchy.table_R27

/-! ## `Hierarchy.table.R28` (re-authored blind)

Text: "| 28 | A Poisson-record lift exists; R₀ kept iff excess = κ |"

A Poisson-record lift of the node model with mean degree κ: the edge model of `PGFData.poisson κ`,
which has mean κ and keeps R₀. "R₀ kept iff excess = κ" for every record (`excessDegree`). -/
namespace Alignment.Shadows.Hierarchy.table_R28

@[sa_reference "Hierarchy.table.R28"]
def T : Prop :=
  (∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).mean = κ) ∧
  (∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
      (edgeModel p (PGFData.poisson κ hκ)).R0 = (nodeModel p κ).R0) ∧
  (∀ (p : SIRParams) (ψ : PGFData) (κ : ℚ),
      (edgeModel p ψ).R0 = (nodeModel p κ).R0 → ψ.excessDegree = κ) ∧
  (∀ (p : SIRParams) (ψ : PGFData) (κ : ℚ),
      ψ.excessDegree = κ → (edgeModel p ψ).R0 = (nodeModel p κ).R0)

/-- S1: the Poisson record of mean κ has mean κ. -/
@[sa_shadow "Hierarchy.table.R28" 1]
def S1 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).mean = κ
/-- S2: its edge model keeps the node model's R₀. -/
@[sa_shadow "Hierarchy.table.R28" 2]
def S2 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ), (edgeModel p (PGFData.poisson κ hκ)).R0 = (nodeModel p κ).R0
/-- S3: R₀ kept ⇒ excess = κ. -/
@[sa_shadow "Hierarchy.table.R28" 3]
def S3 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData) (κ : ℚ), (edgeModel p ψ).R0 = (nodeModel p κ).R0 → ψ.excessDegree = κ
/-- S4: excess = κ ⇒ R₀ kept. -/
@[sa_shadow "Hierarchy.table.R28" 4]
def S4 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData) (κ : ℚ), ψ.excessDegree = κ → (edgeModel p ψ).R0 = (nodeModel p κ).R0

@[sa_ref_forward "Hierarchy.table.R28" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Hierarchy.table.R28" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Hierarchy.table.R28" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Hierarchy.table.R28" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "Hierarchy.table.R28"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.Hierarchy.table_R28

/-! ## `Hierarchy.edgeLiftR0EqIff` (blind)

Text: "The edge model of a record ψ has the R₀ of the node model with mean degree κ iff
ψ''(1)/ψ'(1) = κ." -/
namespace Alignment.Shadows.Hierarchy.edgeLiftR0EqIff

@[sa_reference "Hierarchy.edgeLiftR0EqIff"]
def T : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData) (κ : ℚ),
    (edgeModel p ψ).R0 = (nodeModel p κ).R0 ↔ ψ.secondFactorial / ψ.mean = κ

/-- S1 (→). -/
@[sa_shadow "Hierarchy.edgeLiftR0EqIff" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData) (κ : ℚ),
    (edgeModel p ψ).R0 = (nodeModel p κ).R0 → ψ.secondFactorial / ψ.mean = κ
/-- S2 (←). -/
@[sa_shadow "Hierarchy.edgeLiftR0EqIff" 2]
def S2 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData) (κ : ℚ),
    ψ.secondFactorial / ψ.mean = κ → (edgeModel p ψ).R0 = (nodeModel p κ).R0

@[sa_ref_forward "Hierarchy.edgeLiftR0EqIff" 1] theorem ref_fwd1 : T → S1 :=
  fun t p ψ κ => (t p ψ κ).1
@[sa_ref_forward "Hierarchy.edgeLiftR0EqIff" 2] theorem ref_fwd2 : T → S2 :=
  fun t p ψ κ => (t p ψ κ).2
@[sa_complete "Hierarchy.edgeLiftR0EqIff"]
theorem complete (s1 : S1) (s2 : S2) : T := fun p ψ κ => ⟨s1 p ψ κ, s2 p ψ κ⟩

end Alignment.Shadows.Hierarchy.edgeLiftR0EqIff

/-! ## `Hierarchy.pairLtFull` (blind)

Text: "The pair approximation has fewer variables than the full stochastic model for N ≥ 4:
12N < 3^N."

The variable counts are `levelDim`; the colon gives them as 12N and 3^N. -/
namespace Alignment.Shadows.Hierarchy.pairLtFull

@[sa_reference "Hierarchy.pairLtFull"]
def T : Prop :=
  (∀ N : ℕ, 4 ≤ N → levelDim .pairApproximation N < levelDim .fullStochastic N) ∧
  (∀ N : ℕ, levelDim .pairApproximation N = 12 * N) ∧
  (∀ N : ℕ, levelDim .fullStochastic N = 3 ^ N)

/-- S1: pair < full for N ≥ 4. -/
@[sa_shadow "Hierarchy.pairLtFull" 1]
def S1 : Prop := ∀ N : ℕ, 4 ≤ N → levelDim .pairApproximation N < levelDim .fullStochastic N
/-- S2: the pair approximation has 12N variables. -/
@[sa_shadow "Hierarchy.pairLtFull" 2]
def S2 : Prop := ∀ N : ℕ, levelDim .pairApproximation N = 12 * N
/-- S3: the full stochastic model has 3^N variables. -/
@[sa_shadow "Hierarchy.pairLtFull" 3]
def S3 : Prop := ∀ N : ℕ, levelDim .fullStochastic N = 3 ^ N

@[sa_ref_forward "Hierarchy.pairLtFull" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Hierarchy.pairLtFull" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Hierarchy.pairLtFull" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Hierarchy.pairLtFull"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Hierarchy.pairLtFull

/-! ## `Hierarchy.fullLtPairThree` (blind)

Text: "For N = 3 the full stochastic model has fewer variables than the pair approximation:
3³ = 27 < 36 = 12·3." -/
namespace Alignment.Shadows.Hierarchy.fullLtPairThree

@[sa_reference "Hierarchy.fullLtPairThree"]
def T : Prop :=
  levelDim .fullStochastic 3 < levelDim .pairApproximation 3 ∧
    levelDim .fullStochastic 3 = 27 ∧ levelDim .pairApproximation 3 = 36

/-- S1: for N = 3, full < pair. -/
@[sa_shadow "Hierarchy.fullLtPairThree" 1]
def S1 : Prop := levelDim .fullStochastic 3 < levelDim .pairApproximation 3
/-- S2: for N = 3 the full model has 27 variables. -/
@[sa_shadow "Hierarchy.fullLtPairThree" 2]
def S2 : Prop := levelDim .fullStochastic 3 = 27
/-- S3: for N = 3 the pair approximation has 36 variables. -/
@[sa_shadow "Hierarchy.fullLtPairThree" 3]
def S3 : Prop := levelDim .pairApproximation 3 = 36

@[sa_ref_forward "Hierarchy.fullLtPairThree" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Hierarchy.fullLtPairThree" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Hierarchy.fullLtPairThree" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Hierarchy.fullLtPairThree"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Hierarchy.fullLtPairThree

end
