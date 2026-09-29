import Alignment.Registry
import EBCMCategory.PairwiseClosureConditions

/-!
# Blind shadow sets: group `PairwiseClosureConditions`

Written blind from `Alignment/claims_blind.yaml` (ids, sources, texts only),
`Alignment/DataTypes/PairwiseClosureConditions.md`, `Alignment/README.md` and
`Alignment/Example/ExampleShadows.lean`. No trusted source, checker or report was read.

Vocabulary (DataTypes §(c)):
* closed triple `[ASI]_A` for state `a`: `tripleTerm base p a` (base term `B = base`, weights `p`);
* total triple mass: `∑ a, tripleTerm base p a`;
* normalized weights: `∑ a, p a = 1`; nonnegative weights: `∀ a, 0 ≤ p a`;
* "safe" closure: total-mass conservation `∑ a, tripleTerm base w a = base` together with
  pointwise nonnegativity `∀ a, 0 ≤ tripleTerm base w a` of the triple terms (DataTypes usage);
* "convex" mixing parameter: `0 ≤ φ ∧ φ ≤ 1`;
* Barnard mixed weights `barnardWeights φ p_uc p_c`, convex mixing `convexMix φ x y`, Keeling
  factor `keelingFactor φ corr`, Keeling reweighted weights `keelingWeights φ p corr`.

Conventions used throughout (and noted where they matter):
* The finite state set `α` is universally quantified with `[Fintype α] [DecidableEq α]` (the
  module's section variables); existential witnesses only need `Fintype α` (for the sum).
* Standing assumption of the module header: "`B = (n - 1)[SI]` is a nonnegative base term". It is
  used as a hypothesis `0 ≤ base` wherever a text speaks of positivity/safety without restating it;
  where a text says a conclusion needs *only* normalization, both readings (with / without
  `0 ≤ base`) are shadowed.
* "positivity" of triples is read as nonnegativity (the header's conclusion 2); its failure as
  "some triple is strictly negative" (`∃ a, tripleTerm base p a < 0`).
* "does not imply / cannot certify / needs" (non-implication) is read as the existence of a
  counterexample over some finite state set.

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace).
-/

open scoped BigOperators
open PairwiseClosureConditions

/-! ## `PairwiseClosureConditions.header.safeRegime` -/
namespace Alignment.Shadows.PairwiseClosureConditions.header_safeRegime

/-
Text: "If a closed triple is written in the form `[ASI]_A = B * p_A` where `B = (n - 1)[SI]` is a
nonnegative base term and the weights `p_A` satisfy * `∑_A p_A = 1`, * `p_A ≥ 0` for every state
`A`, then two things follow: 1. the total triple mass is conserved: `∑_A [ASI]_A = B`, 2. each
triple count is nonnegative."

AMBIGUITY: "a closed triple ... written in the form `[ASI]_A = B * p_A`" read (i) as the module's
closed triple `tripleTerm base p a` (DataTypes vocabulary; S1, S2) and (ii) literally as the
product `base * p a` (S3, S4). Both readings are required.
-/

/-- Intended statement: for nonnegative `B` and normalized nonnegative weights, the total triple
mass equals `B` and every triple is nonnegative, both for `tripleTerm` and for the literal form
`B * p_A`. -/
@[sa_reference "PairwiseClosureConditions.header.safeRegime"]
def T : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → ∑ a, p a = 1 → (∀ a, 0 ≤ p a) →
      (∑ a, tripleTerm base p a = base ∧ ∀ a, 0 ≤ tripleTerm base p a) ∧
        (∑ a, base * p a = base ∧ ∀ a, 0 ≤ base * p a)

/-- S1: conclusion 1 (mass conservation) for `tripleTerm`. -/
@[sa_shadow "PairwiseClosureConditions.header.safeRegime" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → ∑ a, p a = 1 → (∀ a, 0 ≤ p a) → ∑ a, tripleTerm base p a = base

/-- S2: conclusion 2 (each triple nonnegative) for `tripleTerm`. -/
@[sa_shadow "PairwiseClosureConditions.header.safeRegime" 2]
def S2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → ∑ a, p a = 1 → (∀ a, 0 ≤ p a) → ∀ a, 0 ≤ tripleTerm base p a

/-- S3: conclusion 1 for the literal form `[ASI]_A = B * p_A`. -/
@[sa_shadow "PairwiseClosureConditions.header.safeRegime" 3]
def S3 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → ∑ a, p a = 1 → (∀ a, 0 ≤ p a) → ∑ a, base * p a = base

/-- S4: conclusion 2 for the literal form `[ASI]_A = B * p_A`. -/
@[sa_shadow "PairwiseClosureConditions.header.safeRegime" 4]
def S4 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → ∑ a, p a = 1 → (∀ a, 0 ≤ p a) → ∀ a, 0 ≤ base * p a

@[sa_ref_forward "PairwiseClosureConditions.header.safeRegime" 1]
theorem ref_fwd1 : T → S1 := by
  intro t α _ _ base p hb hs hn
  exact (t base p hb hs hn).1.1

@[sa_ref_forward "PairwiseClosureConditions.header.safeRegime" 2]
theorem ref_fwd2 : T → S2 := by
  intro t α _ _ base p hb hs hn
  exact (t base p hb hs hn).1.2

@[sa_ref_forward "PairwiseClosureConditions.header.safeRegime" 3]
theorem ref_fwd3 : T → S3 := by
  intro t α _ _ base p hb hs hn
  exact (t base p hb hs hn).2.1

@[sa_ref_forward "PairwiseClosureConditions.header.safeRegime" 4]
theorem ref_fwd4 : T → S4 := by
  intro t α _ _ base p hb hs hn
  exact (t base p hb hs hn).2.2

@[sa_complete "PairwiseClosureConditions.header.safeRegime"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := by
  intro α _ _ base p hb hs hn
  exact ⟨⟨s1 base p hb hs hn, s2 base p hb hs hn⟩, ⟨s3 base p hb hs hn, s4 base p hb hs hn⟩⟩

end Alignment.Shadows.PairwiseClosureConditions.header_safeRegime

/-! ## `PairwiseClosureConditions.header.normalizationOnly` -/
namespace Alignment.Shadows.PairwiseClosureConditions.header_normalizationOnly

/-
Text: "The first conclusion only needs normalization."
(First conclusion of the header: the total triple mass is conserved, `∑_A [ASI]_A = B`.)

AMBIGUITY: "only needs normalization" read as sufficiency (normalization alone suffices), not as
necessity. Which of the other header conditions are dropped:
  (i) the weight sign condition only, with `B ≥ 0` kept as the header's standing description of
      the base term (S1);
  (ii) every other condition, i.e. any base `B` of any sign (S2).
Both readings are required.
-/

/-- Intended statement: for every base term `B` and all normalized weights (of any sign) the total
triple mass equals `B` (reading (ii); reading (i) is its restriction to `B ≥ 0`). -/
@[sa_reference "PairwiseClosureConditions.header.normalizationOnly"]
def T : Prop :=
  (∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → ∑ a, p a = 1 → ∑ a, tripleTerm base p a = base) ∧
  (∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    ∑ a, p a = 1 → ∑ a, tripleTerm base p a = base)

/-- S1: with `B ≥ 0` standing, normalization alone (no sign condition on `p`) conserves mass. -/
@[sa_shadow "PairwiseClosureConditions.header.normalizationOnly" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → ∑ a, p a = 1 → ∑ a, tripleTerm base p a = base

/-- S2: normalization alone conserves mass, for any base term. -/
@[sa_shadow "PairwiseClosureConditions.header.normalizationOnly" 2]
def S2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    ∑ a, p a = 1 → ∑ a, tripleTerm base p a = base

@[sa_ref_forward "PairwiseClosureConditions.header.normalizationOnly" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "PairwiseClosureConditions.header.normalizationOnly" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "PairwiseClosureConditions.header.normalizationOnly"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.PairwiseClosureConditions.header_normalizationOnly

/-! ## `PairwiseClosureConditions.header.nonnegNeedsPointwise` -/
namespace Alignment.Shadows.PairwiseClosureConditions.header_nonnegNeedsPointwise

/-
Text: "The second additionally needs pointwise nonnegativity of the weights."
(Second conclusion of the header: each triple count is nonnegative.)

AMBIGUITY: "additionally needs" read both as
  (i) sufficiency: normalization plus pointwise nonnegativity (with `B ≥ 0`) gives nonnegative
      triples (S1), and
  (ii) necessity: normalization (with `B ≥ 0`) alone does not give it, i.e. there is a finite
      state set, a base `B ≥ 0` and normalized weights with some strictly negative triple (S2).
Both readings are required.
-/

/-- Intended statement: (i) ∧ (ii). -/
@[sa_reference "PairwiseClosureConditions.header.nonnegNeedsPointwise"]
def T : Prop :=
  (∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → ∑ a, p a = 1 → (∀ a, 0 ≤ p a) → ∀ a, 0 ≤ tripleTerm base p a) ∧
  (∃ (α : Type) (_ : Fintype α) (base : ℚ) (p : α → ℚ),
    0 ≤ base ∧ ∑ a, p a = 1 ∧ ∃ a, tripleTerm base p a < 0)

/-- S1: with pointwise nonnegativity added to normalization (and `B ≥ 0`), every triple is
nonnegative. -/
@[sa_shadow "PairwiseClosureConditions.header.nonnegNeedsPointwise" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → ∑ a, p a = 1 → (∀ a, 0 ≤ p a) → ∀ a, 0 ≤ tripleTerm base p a

/-- S2: normalization alone is not enough: some normalized weights with `B ≥ 0` give a negative
triple. -/
@[sa_shadow "PairwiseClosureConditions.header.nonnegNeedsPointwise" 2]
def S2 : Prop :=
  ∃ (α : Type) (_ : Fintype α) (base : ℚ) (p : α → ℚ),
    0 ≤ base ∧ ∑ a, p a = 1 ∧ ∃ a, tripleTerm base p a < 0

@[sa_ref_forward "PairwiseClosureConditions.header.nonnegNeedsPointwise" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "PairwiseClosureConditions.header.nonnegNeedsPointwise" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "PairwiseClosureConditions.header.nonnegNeedsPointwise"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.PairwiseClosureConditions.header_nonnegNeedsPointwise

/-! ## `PairwiseClosureConditions.header.conservationNotPositivity` -/
namespace Alignment.Shadows.PairwiseClosureConditions.header_conservationNotPositivity

/-
Text: "This is exactly the distinction that matters for auditing clustered pairwise closures:
conservation alone does not imply positivity."

Only the mathematical part "conservation alone does not imply positivity" is checkable; "the
distinction that matters for auditing clustered pairwise closures" is a methodological remark and
is not formalised.

AMBIGUITY: "conservation" read (i) as the conserved total triple mass `∑_A [ASI]_A = B` (S1) and
(ii) as the normalization `∑_A p_A = 1` that yields it (S2). "does not imply positivity" is read as
a counterexample (some finite state set, `B ≥ 0` as in the header, and a strictly negative triple),
not as the constructively weaker `¬ ∀ …`. Both readings (i), (ii) are required.
-/

/-- Intended statement: counterexamples for both readings of "conservation". -/
@[sa_reference "PairwiseClosureConditions.header.conservationNotPositivity"]
def T : Prop :=
  (∃ (α : Type) (_ : Fintype α) (base : ℚ) (p : α → ℚ),
    0 ≤ base ∧ ∑ a, tripleTerm base p a = base ∧ ∃ a, tripleTerm base p a < 0) ∧
  (∃ (α : Type) (_ : Fintype α) (base : ℚ) (p : α → ℚ),
    0 ≤ base ∧ ∑ a, p a = 1 ∧ ∃ a, tripleTerm base p a < 0)

/-- S1: total triple mass is conserved yet some triple is negative. -/
@[sa_shadow "PairwiseClosureConditions.header.conservationNotPositivity" 1]
def S1 : Prop :=
  ∃ (α : Type) (_ : Fintype α) (base : ℚ) (p : α → ℚ),
    0 ≤ base ∧ ∑ a, tripleTerm base p a = base ∧ ∃ a, tripleTerm base p a < 0

/-- S2: the weights are normalized yet some triple is negative. -/
@[sa_shadow "PairwiseClosureConditions.header.conservationNotPositivity" 2]
def S2 : Prop :=
  ∃ (α : Type) (_ : Fintype α) (base : ℚ) (p : α → ℚ),
    0 ≤ base ∧ ∑ a, p a = 1 ∧ ∃ a, tripleTerm base p a < 0

@[sa_ref_forward "PairwiseClosureConditions.header.conservationNotPositivity" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "PairwiseClosureConditions.header.conservationNotPositivity" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "PairwiseClosureConditions.header.conservationNotPositivity"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.PairwiseClosureConditions.header_conservationNotPositivity

/-! ## `PairwiseClosureConditions.tripleMassConserved` -/
namespace Alignment.Shadows.PairwiseClosureConditions.tripleMassConserved

/-
Text: "Normalization of the closure weights is enough to conserve the total triple mass. No sign
condition on `p` is needed for this statement."

The second sentence fixes the generality: all weights `p` of any sign. AMBIGUITY: "enough" read
(i) with the header's standing `B ≥ 0` (S1) and (ii) for every base `B` (S2). Both required.
-/

/-- Intended statement: for every base term and every normalized `p` (no sign condition), the total
triple mass equals the base term. -/
@[sa_reference "PairwiseClosureConditions.tripleMassConserved"]
def T : Prop :=
  (∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → ∑ a, p a = 1 → ∑ a, tripleTerm base p a = base) ∧
  (∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    ∑ a, p a = 1 → ∑ a, tripleTerm base p a = base)

/-- S1: normalization conserves mass for every nonnegative base and every `p` of any sign. -/
@[sa_shadow "PairwiseClosureConditions.tripleMassConserved" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → ∑ a, p a = 1 → ∑ a, tripleTerm base p a = base

/-- S2: normalization conserves mass for every base and every `p` of any sign. -/
@[sa_shadow "PairwiseClosureConditions.tripleMassConserved" 2]
def S2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    ∑ a, p a = 1 → ∑ a, tripleTerm base p a = base

@[sa_ref_forward "PairwiseClosureConditions.tripleMassConserved" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "PairwiseClosureConditions.tripleMassConserved" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "PairwiseClosureConditions.tripleMassConserved"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.PairwiseClosureConditions.tripleMassConserved

/-! ## `PairwiseClosureConditions.tripleTermNonneg` -/
namespace Alignment.Shadows.PairwiseClosureConditions.tripleTermNonneg

/-
Text: "If the base term and all closure weights are nonnegative, then every closed triple term is
nonnegative."
No normalization is mentioned, so none is assumed.
-/

/-- Intended statement: `B ≥ 0` and `p ≥ 0` pointwise give `tripleTerm B p a ≥ 0` for every `a`. -/
@[sa_reference "PairwiseClosureConditions.tripleTermNonneg"]
def T : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → (∀ a, 0 ≤ p a) → ∀ a, 0 ≤ tripleTerm base p a

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "PairwiseClosureConditions.tripleTermNonneg" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → (∀ a, 0 ≤ p a) → ∀ a, 0 ≤ tripleTerm base p a

@[sa_ref_forward "PairwiseClosureConditions.tripleTermNonneg" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "PairwiseClosureConditions.tripleTermNonneg"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.PairwiseClosureConditions.tripleTermNonneg

/-! ## `PairwiseClosureConditions.weightInUnitInterval` -/
namespace Alignment.Shadows.PairwiseClosureConditions.weightInUnitInterval

/-
Text: "Under nonnegative normalized weights, each individual closure weight lies in `[0,1]`."

"lies in `[0,1]`" is `p a ∈ Set.Icc 0 1`. Its lower bound `0 ≤ p a` is literally a hypothesis, so a
separate shadow for it would be a tautology; the single non-trivial requirement is the upper bound
`p a ≤ 1` (S1), and completeness restores the lower bound from the hypothesis.
-/

/-- Intended statement: normalized nonnegative weights take values in `[0,1]`. -/
@[sa_reference "PairwiseClosureConditions.weightInUnitInterval"]
def T : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (p : α → ℚ),
    ∑ a, p a = 1 → (∀ a, 0 ≤ p a) → ∀ a, p a ∈ Set.Icc (0 : ℚ) 1

/-- S1: every individual weight is at most one. -/
@[sa_shadow "PairwiseClosureConditions.weightInUnitInterval" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (p : α → ℚ),
    ∑ a, p a = 1 → (∀ a, 0 ≤ p a) → ∀ a, p a ≤ 1

@[sa_ref_forward "PairwiseClosureConditions.weightInUnitInterval" 1]
theorem ref_fwd1 : T → S1 := by
  intro t α _ _ p hs hn a
  exact (t p hs hn a).2

@[sa_complete "PairwiseClosureConditions.weightInUnitInterval"]
theorem complete (s1 : S1) : T := by
  intro α _ _ p hs hn a
  exact ⟨hn a, s1 p hs hn a⟩

end Alignment.Shadows.PairwiseClosureConditions.weightInUnitInterval

/-! ## `PairwiseClosureConditions.negativeWeightGivesNegativeTriple.a` -/
namespace Alignment.Shadows.PairwiseClosureConditions.negativeWeightGivesNegativeTriple_a

/-
Text: "If some closure weight is negative and the base term is strictly positive, then the
corresponding closed triple is negative."
"negative" is read as strictly negative (`< 0`); no normalization or other sign condition is
mentioned, so none is assumed. "some weight ... the corresponding triple" is the universally
quantified state `a`.
-/

/-- Intended statement: `p a < 0` and `B > 0` give `tripleTerm B p a < 0`, for all `p`, `a`. -/
@[sa_reference "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.a"]
def T : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ) (a : α),
    p a < 0 → 0 < base → tripleTerm base p a < 0

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.a" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ) (a : α),
    p a < 0 → 0 < base → tripleTerm base p a < 0

@[sa_ref_forward "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.PairwiseClosureConditions.negativeWeightGivesNegativeTriple_a

/-! ## `PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b` -/
namespace Alignment.Shadows.PairwiseClosureConditions.negativeWeightGivesNegativeTriple_b

/-
Text: "This shows why mass conservation alone cannot certify positivity."

"This shows why" is explanatory; the checkable content is "mass conservation alone cannot certify
positivity", read as a counterexample within the header setting (`B ≥ 0`): a finite state set and
weights for which mass is conserved but some triple is strictly negative.

AMBIGUITY: "mass conservation" read (i) as `∑_A [ASI]_A = B` (S1) and (ii) as the normalization
`∑_A p_A = 1` that yields it (S2). Both required.
-/

/-- Intended statement: counterexamples for both readings of "mass conservation". -/
@[sa_reference "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b"]
def T : Prop :=
  (∃ (α : Type) (_ : Fintype α) (base : ℚ) (p : α → ℚ),
    0 ≤ base ∧ ∑ a, tripleTerm base p a = base ∧ ∃ a, tripleTerm base p a < 0) ∧
  (∃ (α : Type) (_ : Fintype α) (base : ℚ) (p : α → ℚ),
    0 ≤ base ∧ ∑ a, p a = 1 ∧ ∃ a, tripleTerm base p a < 0)

/-- S1: total triple mass conserved, yet some triple negative. -/
@[sa_shadow "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b" 1]
def S1 : Prop :=
  ∃ (α : Type) (_ : Fintype α) (base : ℚ) (p : α → ℚ),
    0 ≤ base ∧ ∑ a, tripleTerm base p a = base ∧ ∃ a, tripleTerm base p a < 0

/-- S2: weights normalized, yet some triple negative. -/
@[sa_shadow "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b" 2]
def S2 : Prop :=
  ∃ (α : Type) (_ : Fintype α) (base : ℚ) (p : α → ℚ),
    0 ≤ base ∧ ∑ a, p a = 1 ∧ ∃ a, tripleTerm base p a < 0

@[sa_ref_forward "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.PairwiseClosureConditions.negativeWeightGivesNegativeTriple_b

/-! ## `PairwiseClosureConditions.normalizedNonnegativeClosureSafe` -/
namespace Alignment.Shadows.PairwiseClosureConditions.normalizedNonnegativeClosureSafe

/-
Text: "A packaged version of the safe regime: normalized nonnegative weights yield both total-mass
conservation and pointwise nonnegativity of the triple terms."

AMBIGUITY: the base term's sign is not restated; "a packaged version of the safe regime" refers to
the header's safe regime, whose base term is nonnegative, so `0 ≤ base` is assumed.
-/

/-- Intended statement: `B ≥ 0` and normalized nonnegative weights give conservation and pointwise
nonnegativity of the triple terms. -/
@[sa_reference "PairwiseClosureConditions.normalizedNonnegativeClosureSafe"]
def T : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → ∑ a, p a = 1 → (∀ a, 0 ≤ p a) →
      ∑ a, tripleTerm base p a = base ∧ ∀ a, 0 ≤ tripleTerm base p a

/-- S1: total-mass conservation. -/
@[sa_shadow "PairwiseClosureConditions.normalizedNonnegativeClosureSafe" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → ∑ a, p a = 1 → (∀ a, 0 ≤ p a) → ∑ a, tripleTerm base p a = base

/-- S2: pointwise nonnegativity of the triple terms. -/
@[sa_shadow "PairwiseClosureConditions.normalizedNonnegativeClosureSafe" 2]
def S2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base : ℚ) (p : α → ℚ),
    0 ≤ base → ∑ a, p a = 1 → (∀ a, 0 ≤ p a) → ∀ a, 0 ≤ tripleTerm base p a

@[sa_ref_forward "PairwiseClosureConditions.normalizedNonnegativeClosureSafe" 1]
theorem ref_fwd1 : T → S1 := by
  intro t α _ _ base p hb hs hn
  exact (t base p hb hs hn).1

@[sa_ref_forward "PairwiseClosureConditions.normalizedNonnegativeClosureSafe" 2]
theorem ref_fwd2 : T → S2 := by
  intro t α _ _ base p hb hs hn
  exact (t base p hb hs hn).2

@[sa_complete "PairwiseClosureConditions.normalizedNonnegativeClosureSafe"]
theorem complete (s1 : S1) (s2 : S2) : T := by
  intro α _ _ base p hb hs hn
  exact ⟨s1 base p hb hs hn, s2 base p hb hs hn⟩

end Alignment.Shadows.PairwiseClosureConditions.normalizedNonnegativeClosureSafe

/-! ## `PairwiseClosureConditions.convexMixNonneg` -/
namespace Alignment.Shadows.PairwiseClosureConditions.convexMixNonneg

/-
Text: "A convex mixture of nonnegative weights is nonnegative."
"convex" is `0 ≤ φ ∧ φ ≤ 1` (DataTypes); the mixture is the operation `convexMix φ x y`.
-/

/-- Intended statement: for `φ ∈ [0,1]` and `x, y ≥ 0`, `convexMix φ x y ≥ 0`. -/
@[sa_reference "PairwiseClosureConditions.convexMixNonneg"]
def T : Prop :=
  ∀ (φ x y : ℚ), 0 ≤ φ → φ ≤ 1 → 0 ≤ x → 0 ≤ y → 0 ≤ convexMix φ x y

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "PairwiseClosureConditions.convexMixNonneg" 1]
def S1 : Prop :=
  ∀ (φ x y : ℚ), 0 ≤ φ → φ ≤ 1 → 0 ≤ x → 0 ≤ y → 0 ≤ convexMix φ x y

@[sa_ref_forward "PairwiseClosureConditions.convexMixNonneg" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "PairwiseClosureConditions.convexMixNonneg"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.PairwiseClosureConditions.convexMixNonneg

/-! ## `PairwiseClosureConditions.barnardWeightsNormalized.a` -/
namespace Alignment.Shadows.PairwiseClosureConditions.barnardWeightsNormalized_a

/-
Text: "A convex mixture of normalized weight families is normalized."
The mixture of two weight families is `barnardWeights φ p_uc p_c` (DataTypes: "a convex
combination of two normalized families of weights").

AMBIGUITY: "convex" read as the hypothesis `0 ≤ φ ∧ φ ≤ 1` (DataTypes meaning of "convex"), not
merely as the algebraic shape of the combination.
-/

/-- Intended statement: for `φ ∈ [0,1]` and two normalized families, the mixed family sums to 1. -/
@[sa_reference "PairwiseClosureConditions.barnardWeightsNormalized.a"]
def T : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (φ : ℚ) (p_uc p_c : α → ℚ),
    0 ≤ φ → φ ≤ 1 → ∑ a, p_uc a = 1 → ∑ a, p_c a = 1 → ∑ a, barnardWeights φ p_uc p_c a = 1

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "PairwiseClosureConditions.barnardWeightsNormalized.a" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (φ : ℚ) (p_uc p_c : α → ℚ),
    0 ≤ φ → φ ≤ 1 → ∑ a, p_uc a = 1 → ∑ a, p_c a = 1 → ∑ a, barnardWeights φ p_uc p_c a = 1

@[sa_ref_forward "PairwiseClosureConditions.barnardWeightsNormalized.a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "PairwiseClosureConditions.barnardWeightsNormalized.a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.PairwiseClosureConditions.barnardWeightsNormalized_a

/-! ## `PairwiseClosureConditions.barnardWeightsNonneg` -/
namespace Alignment.Shadows.PairwiseClosureConditions.barnardWeightsNonneg

/-
Text: "Barnard-style mixed weights stay nonnegative when both the unclustered and clustered
probability models are pointwise nonnegative."

AMBIGUITY: the text states no range for the mixing parameter; "Barnard-style mixed weights" are by
their DataTypes description a *convex* combination, so `0 ≤ φ ∧ φ ≤ 1` is assumed. Normalization of
the two models is not mentioned and not assumed (only pointwise nonnegativity is stated).
-/

/-- Intended statement: for `φ ∈ [0,1]` and pointwise nonnegative `p_uc`, `p_c`, every Barnard mixed
weight is nonnegative. -/
@[sa_reference "PairwiseClosureConditions.barnardWeightsNonneg"]
def T : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (φ : ℚ) (p_uc p_c : α → ℚ),
    0 ≤ φ → φ ≤ 1 → (∀ a, 0 ≤ p_uc a) → (∀ a, 0 ≤ p_c a) →
      ∀ a, 0 ≤ barnardWeights φ p_uc p_c a

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "PairwiseClosureConditions.barnardWeightsNonneg" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (φ : ℚ) (p_uc p_c : α → ℚ),
    0 ≤ φ → φ ≤ 1 → (∀ a, 0 ≤ p_uc a) → (∀ a, 0 ≤ p_c a) →
      ∀ a, 0 ≤ barnardWeights φ p_uc p_c a

@[sa_ref_forward "PairwiseClosureConditions.barnardWeightsNonneg" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "PairwiseClosureConditions.barnardWeightsNonneg"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.PairwiseClosureConditions.barnardWeightsNonneg

/-! ## `PairwiseClosureConditions.barnardStyleClosureSafe` -/
namespace Alignment.Shadows.PairwiseClosureConditions.barnardStyleClosureSafe

/-
Text: "Barnard-style closures are safe whenever both constituent probability models are normalized
and nonnegative."

"safe" = total-mass conservation and pointwise nonnegativity of the triple terms (DataTypes), for
the closure with weights `barnardWeights φ p_uc p_c`. Assumed as standing: `0 ≤ base` (header)
and `0 ≤ φ ≤ 1` (Barnard mixing is a convex combination). AMBIGUITY: both are implicit in the text.
-/

/-- Intended statement: the Barnard closure built from two normalized nonnegative models is safe. -/
@[sa_reference "PairwiseClosureConditions.barnardStyleClosureSafe"]
def T : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base φ : ℚ) (p_uc p_c : α → ℚ),
    0 ≤ base → 0 ≤ φ → φ ≤ 1 →
      ∑ a, p_uc a = 1 → (∀ a, 0 ≤ p_uc a) → ∑ a, p_c a = 1 → (∀ a, 0 ≤ p_c a) →
        ∑ a, tripleTerm base (barnardWeights φ p_uc p_c) a = base ∧
          ∀ a, 0 ≤ tripleTerm base (barnardWeights φ p_uc p_c) a

/-- S1: the Barnard closure conserves the total triple mass. -/
@[sa_shadow "PairwiseClosureConditions.barnardStyleClosureSafe" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base φ : ℚ) (p_uc p_c : α → ℚ),
    0 ≤ base → 0 ≤ φ → φ ≤ 1 →
      ∑ a, p_uc a = 1 → (∀ a, 0 ≤ p_uc a) → ∑ a, p_c a = 1 → (∀ a, 0 ≤ p_c a) →
        ∑ a, tripleTerm base (barnardWeights φ p_uc p_c) a = base

/-- S2: every Barnard closed triple term is nonnegative. -/
@[sa_shadow "PairwiseClosureConditions.barnardStyleClosureSafe" 2]
def S2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base φ : ℚ) (p_uc p_c : α → ℚ),
    0 ≤ base → 0 ≤ φ → φ ≤ 1 →
      ∑ a, p_uc a = 1 → (∀ a, 0 ≤ p_uc a) → ∑ a, p_c a = 1 → (∀ a, 0 ≤ p_c a) →
        ∀ a, 0 ≤ tripleTerm base (barnardWeights φ p_uc p_c) a

@[sa_ref_forward "PairwiseClosureConditions.barnardStyleClosureSafe" 1]
theorem ref_fwd1 : T → S1 := by
  intro t α _ _ base φ p_uc p_c hb h0 h1 hs1 hn1 hs2 hn2
  exact (t base φ p_uc p_c hb h0 h1 hs1 hn1 hs2 hn2).1

@[sa_ref_forward "PairwiseClosureConditions.barnardStyleClosureSafe" 2]
theorem ref_fwd2 : T → S2 := by
  intro t α _ _ base φ p_uc p_c hb h0 h1 hs1 hn1 hs2 hn2
  exact (t base φ p_uc p_c hb h0 h1 hs1 hn1 hs2 hn2).2

@[sa_complete "PairwiseClosureConditions.barnardStyleClosureSafe"]
theorem complete (s1 : S1) (s2 : S2) : T := by
  intro α _ _ base φ p_uc p_c hb h0 h1 hs1 hn1 hs2 hn2
  exact ⟨s1 base φ p_uc p_c hb h0 h1 hs1 hn1 hs2 hn2, s2 base φ p_uc p_c hb h0 h1 hs1 hn1 hs2 hn2⟩

end Alignment.Shadows.PairwiseClosureConditions.barnardStyleClosureSafe

/-! ## `PairwiseClosureConditions.keelingFactorNonneg` -/
namespace Alignment.Shadows.PairwiseClosureConditions.keelingFactorNonneg

/-
Text: "If the Keeling correlation correction stays nonnegative, then the Keeling weight factor is
nonnegative."

"the Keeling correlation correction" is the argument `corr`; "the Keeling weight factor" is
`keelingFactor φ corr` (the text distinguishes the two).

AMBIGUITY: the text states no range for the clustering parameter `φ`. Read (i) with `φ` a
clustering coefficient, `0 ≤ φ ∧ φ ≤ 1` (S1), and (ii) literally, for every `φ` (S2). Both
required.
-/

/-- Intended statement: `corr ≥ 0` gives `keelingFactor φ corr ≥ 0` for every `φ` (reading (ii);
reading (i) is its restriction to `φ ∈ [0,1]`). -/
@[sa_reference "PairwiseClosureConditions.keelingFactorNonneg"]
def T : Prop :=
  (∀ (φ corr : ℚ), 0 ≤ φ → φ ≤ 1 → 0 ≤ corr → 0 ≤ keelingFactor φ corr) ∧
  (∀ (φ corr : ℚ), 0 ≤ corr → 0 ≤ keelingFactor φ corr)

/-- S1: for `φ ∈ [0,1]`, a nonnegative correction gives a nonnegative factor. -/
@[sa_shadow "PairwiseClosureConditions.keelingFactorNonneg" 1]
def S1 : Prop := ∀ (φ corr : ℚ), 0 ≤ φ → φ ≤ 1 → 0 ≤ corr → 0 ≤ keelingFactor φ corr

/-- S2: for every `φ`, a nonnegative correction gives a nonnegative factor. -/
@[sa_shadow "PairwiseClosureConditions.keelingFactorNonneg" 2]
def S2 : Prop := ∀ (φ corr : ℚ), 0 ≤ corr → 0 ≤ keelingFactor φ corr

@[sa_ref_forward "PairwiseClosureConditions.keelingFactorNonneg" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "PairwiseClosureConditions.keelingFactorNonneg" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "PairwiseClosureConditions.keelingFactorNonneg"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.PairwiseClosureConditions.keelingFactorNonneg

/-! ## `PairwiseClosureConditions.keelingWeightsNonneg` -/
namespace Alignment.Shadows.PairwiseClosureConditions.keelingWeightsNonneg

/-
Text: "If the baseline weights and the correlation correction are both nonnegative, then the
Keeling-reweighted weights are nonnegative."

Baseline weights `p`, correlation correction `corr` (pointwise, `∀ a, 0 ≤ corr a`), reweighted
weights `keelingWeights φ p corr`.

AMBIGUITY: (a) "the correlation correction" is read as the argument `corr` (as in
`keelingFactorNonneg`, which distinguishes the correction from the weight factor), not as the
factor that multiplies `p a`. (b) No range for `φ` is stated: read (i) with `0 ≤ φ ∧ φ ≤ 1` (S1)
and (ii) for every `φ` (S2). Both (i) and (ii) required.
-/

/-- Intended statement: nonnegative baseline weights and corrections give nonnegative Keeling
weights, for every `φ` (reading (ii); reading (i) is its restriction to `φ ∈ [0,1]`). -/
@[sa_reference "PairwiseClosureConditions.keelingWeightsNonneg"]
def T : Prop :=
  (∀ {α : Type} [Fintype α] [DecidableEq α] (φ : ℚ) (p corr : α → ℚ),
    0 ≤ φ → φ ≤ 1 → (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ corr a) → ∀ a, 0 ≤ keelingWeights φ p corr a) ∧
  (∀ {α : Type} [Fintype α] [DecidableEq α] (φ : ℚ) (p corr : α → ℚ),
    (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ corr a) → ∀ a, 0 ≤ keelingWeights φ p corr a)

/-- S1: for `φ ∈ [0,1]`, the Keeling-reweighted weights are nonnegative. -/
@[sa_shadow "PairwiseClosureConditions.keelingWeightsNonneg" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (φ : ℚ) (p corr : α → ℚ),
    0 ≤ φ → φ ≤ 1 → (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ corr a) → ∀ a, 0 ≤ keelingWeights φ p corr a

/-- S2: for every `φ`, the Keeling-reweighted weights are nonnegative. -/
@[sa_shadow "PairwiseClosureConditions.keelingWeightsNonneg" 2]
def S2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (φ : ℚ) (p corr : α → ℚ),
    (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ corr a) → ∀ a, 0 ≤ keelingWeights φ p corr a

@[sa_ref_forward "PairwiseClosureConditions.keelingWeightsNonneg" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "PairwiseClosureConditions.keelingWeightsNonneg" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "PairwiseClosureConditions.keelingWeightsNonneg"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.PairwiseClosureConditions.keelingWeightsNonneg

/-! ## `PairwiseClosureConditions.keelingStyleClosureSafe.a` -/
namespace Alignment.Shadows.PairwiseClosureConditions.keelingStyleClosureSafe_a

/-
Text: "Keeling-style closures are safe only after an *additional normalization theorem* is
supplied."

The Keeling-style closure has weights `keelingWeights φ p corr`; "safe" = conservation and
pointwise nonnegativity of `tripleTerm base (keelingWeights φ p corr)` (DataTypes). The
"additional normalization theorem" is supplied as the hypothesis
`∑ a, keelingWeights φ p corr a = 1`, in addition to the positivity hypotheses of the same
docstring (nonnegative baseline weights `p`, nonnegative corrections `corr`) and the header's
`0 ≤ base`.

AMBIGUITY: (a) "safe ... after ... is supplied" (sufficiency) and "only after" (necessity) are both
read: sufficiency is S1–S4; necessity is S5, a Keeling closure (with `φ ∈ [0,1]`, `B ≥ 0`, `p ≥ 0`,
`corr ≥ 0`) that is not safe when no normalization is supplied. (b) No range for `φ` is stated:
sufficiency is required both for `φ ∈ [0,1]` (S1, S2) and for every `φ` (S3, S4).
-/

/-- Intended statement: with the normalization supplied the Keeling closure is safe (for every
`φ`, hence also for `φ ∈ [0,1]`), and without it safety can fail. -/
@[sa_reference "PairwiseClosureConditions.keelingStyleClosureSafe.a"]
def T : Prop :=
  (∀ {α : Type} [Fintype α] [DecidableEq α] (base φ : ℚ) (p corr : α → ℚ),
    0 ≤ φ → φ ≤ 1 → 0 ≤ base → (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ corr a) →
      ∑ a, keelingWeights φ p corr a = 1 →
        ∑ a, tripleTerm base (keelingWeights φ p corr) a = base ∧
          ∀ a, 0 ≤ tripleTerm base (keelingWeights φ p corr) a) ∧
  (∀ {α : Type} [Fintype α] [DecidableEq α] (base φ : ℚ) (p corr : α → ℚ),
    0 ≤ base → (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ corr a) →
      ∑ a, keelingWeights φ p corr a = 1 →
        ∑ a, tripleTerm base (keelingWeights φ p corr) a = base ∧
          ∀ a, 0 ≤ tripleTerm base (keelingWeights φ p corr) a) ∧
  (∃ (α : Type) (_ : Fintype α) (base φ : ℚ) (p corr : α → ℚ),
    0 ≤ φ ∧ φ ≤ 1 ∧ 0 ≤ base ∧ (∀ a, 0 ≤ p a) ∧ (∀ a, 0 ≤ corr a) ∧
      ¬ (∑ a, tripleTerm base (keelingWeights φ p corr) a = base ∧
          ∀ a, 0 ≤ tripleTerm base (keelingWeights φ p corr) a))

/-- S1: `φ ∈ [0,1]`, normalization supplied: the Keeling closure conserves mass. -/
@[sa_shadow "PairwiseClosureConditions.keelingStyleClosureSafe.a" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base φ : ℚ) (p corr : α → ℚ),
    0 ≤ φ → φ ≤ 1 → 0 ≤ base → (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ corr a) →
      ∑ a, keelingWeights φ p corr a = 1 →
        ∑ a, tripleTerm base (keelingWeights φ p corr) a = base

/-- S2: `φ ∈ [0,1]`, normalization supplied: the Keeling triple terms are nonnegative. -/
@[sa_shadow "PairwiseClosureConditions.keelingStyleClosureSafe.a" 2]
def S2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base φ : ℚ) (p corr : α → ℚ),
    0 ≤ φ → φ ≤ 1 → 0 ≤ base → (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ corr a) →
      ∑ a, keelingWeights φ p corr a = 1 →
        ∀ a, 0 ≤ tripleTerm base (keelingWeights φ p corr) a

/-- S3: any `φ`, normalization supplied: the Keeling closure conserves mass. -/
@[sa_shadow "PairwiseClosureConditions.keelingStyleClosureSafe.a" 3]
def S3 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base φ : ℚ) (p corr : α → ℚ),
    0 ≤ base → (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ corr a) →
      ∑ a, keelingWeights φ p corr a = 1 →
        ∑ a, tripleTerm base (keelingWeights φ p corr) a = base

/-- S4: any `φ`, normalization supplied: the Keeling triple terms are nonnegative. -/
@[sa_shadow "PairwiseClosureConditions.keelingStyleClosureSafe.a" 4]
def S4 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base φ : ℚ) (p corr : α → ℚ),
    0 ≤ base → (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ corr a) →
      ∑ a, keelingWeights φ p corr a = 1 →
        ∀ a, 0 ≤ tripleTerm base (keelingWeights φ p corr) a

/-- S5 ("only after"): without the normalization, a Keeling closure satisfying the positivity
hypotheses need not be safe. -/
@[sa_shadow "PairwiseClosureConditions.keelingStyleClosureSafe.a" 5]
def S5 : Prop :=
  ∃ (α : Type) (_ : Fintype α) (base φ : ℚ) (p corr : α → ℚ),
    0 ≤ φ ∧ φ ≤ 1 ∧ 0 ≤ base ∧ (∀ a, 0 ≤ p a) ∧ (∀ a, 0 ≤ corr a) ∧
      ¬ (∑ a, tripleTerm base (keelingWeights φ p corr) a = base ∧
          ∀ a, 0 ≤ tripleTerm base (keelingWeights φ p corr) a)

@[sa_ref_forward "PairwiseClosureConditions.keelingStyleClosureSafe.a" 1]
theorem ref_fwd1 : T → S1 := by
  intro t α _ _ base φ p corr h0 h1 hb hp hc hs
  exact (t.1 base φ p corr h0 h1 hb hp hc hs).1

@[sa_ref_forward "PairwiseClosureConditions.keelingStyleClosureSafe.a" 2]
theorem ref_fwd2 : T → S2 := by
  intro t α _ _ base φ p corr h0 h1 hb hp hc hs
  exact (t.1 base φ p corr h0 h1 hb hp hc hs).2

@[sa_ref_forward "PairwiseClosureConditions.keelingStyleClosureSafe.a" 3]
theorem ref_fwd3 : T → S3 := by
  intro t α _ _ base φ p corr hb hp hc hs
  exact (t.2.1 base φ p corr hb hp hc hs).1

@[sa_ref_forward "PairwiseClosureConditions.keelingStyleClosureSafe.a" 4]
theorem ref_fwd4 : T → S4 := by
  intro t α _ _ base φ p corr hb hp hc hs
  exact (t.2.1 base φ p corr hb hp hc hs).2

@[sa_ref_forward "PairwiseClosureConditions.keelingStyleClosureSafe.a" 5]
theorem ref_fwd5 : T → S5 := fun t => t.2.2

@[sa_complete "PairwiseClosureConditions.keelingStyleClosureSafe.a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := by
  refine ⟨?_, ?_, s5⟩
  · intro α _ _ base φ p corr h0 h1 hb hp hc hs
    exact ⟨s1 base φ p corr h0 h1 hb hp hc hs, s2 base φ p corr h0 h1 hb hp hc hs⟩
  · intro α _ _ base φ p corr hb hp hc hs
    exact ⟨s3 base φ p corr hb hp hc hs, s4 base φ p corr hb hp hc hs⟩

end Alignment.Shadows.PairwiseClosureConditions.keelingStyleClosureSafe_a

/-! ## `PairwiseClosureConditions.keelingStyleClosureSafe.b` -/
namespace Alignment.Shadows.PairwiseClosureConditions.keelingStyleClosureSafe_b

/-
Text: "Positivity follows from nonnegative baseline weights and nonnegative correlation
corrections,"

"Positivity" of the Keeling-style closure: pointwise nonnegativity of the closed triple terms
`tripleTerm base (keelingWeights φ p corr) a` (the positivity half of "safe"). No normalization is
assumed (the sentence continues "but conservation must be assumed separately"). The header's
`0 ≤ base` is assumed as standing.

AMBIGUITY: (a) "Positivity" could also be read as positivity of the reweighted weights themselves;
that is the separate claim `keelingWeightsNonneg`, and here the closure (triple) reading is taken.
(b) No range for `φ` is stated: read (i) with `0 ≤ φ ∧ φ ≤ 1` (S1) and (ii) for every `φ` (S2).
Both (i) and (ii) required.
-/

/-- Intended statement: nonnegative baseline weights and corrections (with `B ≥ 0`) give
nonnegative Keeling triple terms, without any normalization, for every `φ` (reading (ii);
reading (i) is its restriction to `φ ∈ [0,1]`). -/
@[sa_reference "PairwiseClosureConditions.keelingStyleClosureSafe.b"]
def T : Prop :=
  (∀ {α : Type} [Fintype α] [DecidableEq α] (base φ : ℚ) (p corr : α → ℚ),
    0 ≤ φ → φ ≤ 1 → 0 ≤ base → (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ corr a) →
      ∀ a, 0 ≤ tripleTerm base (keelingWeights φ p corr) a) ∧
  (∀ {α : Type} [Fintype α] [DecidableEq α] (base φ : ℚ) (p corr : α → ℚ),
    0 ≤ base → (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ corr a) →
      ∀ a, 0 ≤ tripleTerm base (keelingWeights φ p corr) a)

/-- S1: `φ ∈ [0,1]`: Keeling triple terms are nonnegative without normalization. -/
@[sa_shadow "PairwiseClosureConditions.keelingStyleClosureSafe.b" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base φ : ℚ) (p corr : α → ℚ),
    0 ≤ φ → φ ≤ 1 → 0 ≤ base → (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ corr a) →
      ∀ a, 0 ≤ tripleTerm base (keelingWeights φ p corr) a

/-- S2: any `φ`: Keeling triple terms are nonnegative without normalization. -/
@[sa_shadow "PairwiseClosureConditions.keelingStyleClosureSafe.b" 2]
def S2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (base φ : ℚ) (p corr : α → ℚ),
    0 ≤ base → (∀ a, 0 ≤ p a) → (∀ a, 0 ≤ corr a) →
      ∀ a, 0 ≤ tripleTerm base (keelingWeights φ p corr) a

@[sa_ref_forward "PairwiseClosureConditions.keelingStyleClosureSafe.b" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "PairwiseClosureConditions.keelingStyleClosureSafe.b" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "PairwiseClosureConditions.keelingStyleClosureSafe.b"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.PairwiseClosureConditions.keelingStyleClosureSafe_b

noncomputable section

/-! ## `PairwiseClosureConditions.barnardWeightsNormalized.b` (blind)

Text: "This is the key algebraic fact behind Barnard's improved closure: it mixes the unclustered
weights (probability 1 − φ) with the normalised clustered weights (probability φ), which gives
Σ_A [ASI] = (n − 1)[SI] (Barnard 2018, PhD thesis, University of Sussex, §4.3.2, "Improved
closure")."

S1: `barnardWeights` mixes with probabilities 1 − φ and φ; S2: with normalised unclustered and
clustered weights the total triple mass `Σ_A tripleTerm base (barnardWeights …) A` is the base
term `base = (n − 1)[SI]`. -- AMBIGUITY: "probability φ" read as `0 ≤ φ ≤ 1`. -/
namespace Alignment.Shadows.PairwiseClosureConditions.barnardWeightsNormalized_b

@[sa_reference "PairwiseClosureConditions.barnardWeightsNormalized.b"]
def T : Prop :=
  (∀ {α : Type} [Fintype α] [DecidableEq α] (φ : ℚ) (p_uc p_c : α → ℚ) (a : α), 0 ≤ φ → φ ≤ 1 →
      barnardWeights φ p_uc p_c a = (1 - φ) * p_uc a + φ * p_c a) ∧
  (∀ {α : Type} [Fintype α] [DecidableEq α] (φ base : ℚ) (p_uc p_c : α → ℚ), 0 ≤ φ → φ ≤ 1 →
      ∑ a, p_uc a = 1 → ∑ a, p_c a = 1 → ∑ a, tripleTerm base (barnardWeights φ p_uc p_c) a = base)

/-- S1: the mixture has weights 1 − φ (unclustered) and φ (clustered). -/
@[sa_shadow "PairwiseClosureConditions.barnardWeightsNormalized.b" 1]
def S1 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (φ : ℚ) (p_uc p_c : α → ℚ) (a : α), 0 ≤ φ → φ ≤ 1 →
    barnardWeights φ p_uc p_c a = (1 - φ) * p_uc a + φ * p_c a
/-- S2: the mixed closure gives `Σ_A [ASI] = (n − 1)[SI]`. -/
@[sa_shadow "PairwiseClosureConditions.barnardWeightsNormalized.b" 2]
def S2 : Prop :=
  ∀ {α : Type} [Fintype α] [DecidableEq α] (φ base : ℚ) (p_uc p_c : α → ℚ), 0 ≤ φ → φ ≤ 1 →
    ∑ a, p_uc a = 1 → ∑ a, p_c a = 1 → ∑ a, tripleTerm base (barnardWeights φ p_uc p_c) a = base

@[sa_ref_forward "PairwiseClosureConditions.barnardWeightsNormalized.b" 1] theorem ref_fwd1 :
    T → S1 := fun t => t.1
@[sa_ref_forward "PairwiseClosureConditions.barnardWeightsNormalized.b" 2] theorem ref_fwd2 :
    T → S2 := fun t => t.2
@[sa_complete "PairwiseClosureConditions.barnardWeightsNormalized.b"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.PairwiseClosureConditions.barnardWeightsNormalized_b

end
