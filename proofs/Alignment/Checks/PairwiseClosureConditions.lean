import Alignment.Registry
import Alignment.Shadows.PairwiseClosureConditions

/-!
# Checkers: group `PairwiseClosureConditions`

Checker author (SA-PASS role 3, non-blind). For every claim of
`EBCMCategory/PairwiseClosureConditions.lean` with `status: implemented` this file holds the
`sa_claim` registration (verbatim registry text, registry `impl` list in registry order), the
forward checkers `sa_impl% → Sᵢ`, the backward checker `S₁ → … → Sₙ → sa_impl%`, and `sa_fail_*`
records where a check cannot be proved because the implementation says something different from
the shadow.

No bridges are declared. The trusted definitions are used exactly as the shadows use them, and
`tripleTerm base p a := base * p a` is a plain definition, so the literal header form
`B * p_A` (`header.safeRegime` S3, S4) is reached by definitional unfolding alone.

Conventions of the proofs below (README "Writing structural proofs"): `intro` (including the
instance binders `[Fintype α] [DecidableEq α]`), application of `h` or of the shadows with the
hypotheses reordered, projections of conjunctions, anonymous constructors, and definitional
unfolding. No tactic automation, library lemma or kernel computation is used.

Summary of recorded failures.
* Non-implication claims (`header.nonnegNeedsPointwise` S2, `header.conservationNotPositivity`
  S1–S2, `negativeWeightGivesNegativeTriple.b` S1–S2, `keelingStyleClosureSafe.a` S5): the
  shadows are existence statements (a counterexample to "normalization/conservation implies
  positivity", or an unsafe Keeling closure). The implementations are universal implications and
  exhibit no witness; the shadows are closed propositions whose whole content (the witness and its
  normalization) would come from the checker's own kernel computation, so `h` would be at most
  inessential (README "Known limitations" 1). Recorded as failures, not forced. The corresponding
  backward checks fail too: a single counterexample does not give a universal implication.
* Readings "for every φ" of the Keeling claims (`keelingFactorNonneg` S2, `keelingWeightsNonneg`
  S2, `keelingStyleClosureSafe.a` S3–S4, `keelingStyleClosureSafe.b` S2) are marked `SHADOW?:`.
  All but `keelingStyleClosureSafe.a` S3 are false (explicit counterexamples below); φ is the
  clustering coefficient of Keeling's closure, with domain `[0,1]`.
* `barnardWeightsNormalized.a` backward: the implementation holds for every φ (affine
  combinations), the text and shadow only for convex φ ∈ [0,1].
* `header.nonnegNeedsPointwise` and `keelingStyleClosureSafe.b` backward: the implementations are
  general lemmas (no normalization; arbitrary weight families) that do not follow from the
  shadows' narrower composite statements.
-/

/-! ## `PairwiseClosureConditions.header.safeRegime` -/
namespace Alignment.Shadows.PairwiseClosureConditions.header_safeRegime

sa_claim "PairwiseClosureConditions.header.safeRegime" group "PairwiseClosureConditions" required
  text "If a closed triple is written in the form `[ASI]_A = B * p_A` where `B = (n - 1)[SI]` is a nonnegative base term and the weights `p_A` satisfy * `∑_A p_A = 1`, * `p_A ≥ 0` for every state `A`, then two things follow: 1. the total triple mass is conserved: `∑_A [ASI]_A = B`, 2. each triple count is nonnegative."
  impl PairwiseClosureConditions.normalized_nonnegative_closure_safe

/-- The impl takes the hypotheses in the order `0 ≤ base`, `p ≥ 0`, `∑ p = 1`. -/
@[sa_forward "PairwiseClosureConditions.header.safeRegime" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.header.safeRegime") : S1 := by
  intro α _ _ base p hb hn hs
  exact (h base p hb hs hn).1

@[sa_forward "PairwiseClosureConditions.header.safeRegime" 2]
theorem fwd2 (h : sa_impl% "PairwiseClosureConditions.header.safeRegime") : S2 := by
  intro α _ _ base p hb hn hs
  exact (h base p hb hs hn).2

/-- `tripleTerm base p a` unfolds definitionally to `base * p a` (the literal header form). -/
@[sa_forward "PairwiseClosureConditions.header.safeRegime" 3]
theorem fwd3 (h : sa_impl% "PairwiseClosureConditions.header.safeRegime") : S3 := by
  intro α _ _ base p hb hn hs
  exact (h base p hb hs hn).1

@[sa_forward "PairwiseClosureConditions.header.safeRegime" 4]
theorem fwd4 (h : sa_impl% "PairwiseClosureConditions.header.safeRegime") : S4 := by
  intro α _ _ base p hb hn hs
  exact (h base p hb hs hn).2

@[sa_backward "PairwiseClosureConditions.header.safeRegime"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) (_s4 : S4) :
    sa_impl% "PairwiseClosureConditions.header.safeRegime" := by
  intro α _ _ base p hb hs hn
  exact ⟨s1 base p hb hn hs, s2 base p hb hn hs⟩

end Alignment.Shadows.PairwiseClosureConditions.header_safeRegime

/-! ## `PairwiseClosureConditions.header.normalizationOnly` -/
namespace Alignment.Shadows.PairwiseClosureConditions.header_normalizationOnly

sa_claim "PairwiseClosureConditions.header.normalizationOnly" group "PairwiseClosureConditions"
  required text "The first conclusion only needs normalization."
  impl PairwiseClosureConditions.triple_mass_conserved

/-- The impl has no sign condition at all; the standing `0 ≤ base` of S1 is discarded. -/
@[sa_forward "PairwiseClosureConditions.header.normalizationOnly" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.header.normalizationOnly") : S1 := by
  intro α _ _ base p _hb hn
  exact h base p hn

@[sa_forward "PairwiseClosureConditions.header.normalizationOnly" 2]
theorem fwd2 (h : sa_impl% "PairwiseClosureConditions.header.normalizationOnly") : S2 := by
  intro α _ _ base p hn
  exact h base p hn

@[sa_backward "PairwiseClosureConditions.header.normalizationOnly"]
theorem bwd (_s1 : S1) (s2 : S2) :
    sa_impl% "PairwiseClosureConditions.header.normalizationOnly" := by
  intro α _ _ base p hn
  exact s2 base p hn

end Alignment.Shadows.PairwiseClosureConditions.header_normalizationOnly

/-! ## `PairwiseClosureConditions.header.nonnegNeedsPointwise` -/
namespace Alignment.Shadows.PairwiseClosureConditions.header_nonnegNeedsPointwise

sa_claim "PairwiseClosureConditions.header.nonnegNeedsPointwise" group "PairwiseClosureConditions"
  required text "The second additionally needs pointwise nonnegativity of the weights."
  impl PairwiseClosureConditions.triple_term_nonneg
    PairwiseClosureConditions.negative_weight_gives_negative_triple

/-- Sufficiency from the first conjunct `triple_term_nonneg` (the normalization is not needed). -/
@[sa_forward "PairwiseClosureConditions.header.nonnegNeedsPointwise" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.header.nonnegNeedsPointwise") : S1 := by
  intro α _ _ base p hb _hn hs a
  exact h.1 base p a hb hs

sa_fail_forward "PairwiseClosureConditions.header.nonnegNeedsPointwise" 2 "impl is the conjunction of triple_term_nonneg (0 ≤ base → (∀ b, 0 ≤ p b) → 0 ≤ tripleTerm base p a) and negative_weight_gives_negative_triple (∀ base p a, 0 < base → p a < 0 → tripleTerm base p a < 0). Both are universal implications; neither exhibits a weight family nor mentions normalization together with a negative weight. S2 is the existence statement ∃ α (Fintype), base ≥ 0, p with ∑ a, p a = 1 and some tripleTerm base p a < 0, i.e. that normalization (with B ≥ 0) does not suffice for nonnegativity. Its content, that a normalized family can have a strictly negative entry (e.g. Bool, p = (2, -1), base = 1), is not stated by impl. A checker would have to supply that witness and verify ∑ p = 1, 0 ≤ 1, 0 < 1 and p false < 0 by closed kernel computation on ℚ; tripleTerm 1 p false = -1 < 0 then holds by the same computation, so S2 is provable from scratch and any use of h would be inessential (README Known limitations 1). The registry impl_note already says necessity is proved 'only in the pointwise sense'. Recorded rather than forced."

sa_fail_backward "PairwiseClosureConditions.header.nonnegNeedsPointwise" "impl is stronger than, and partly different from, the shadows. (1) Its first conjunct triple_term_nonneg gives 0 ≤ tripleTerm base p a for every pointwise nonnegative p WITHOUT normalization, whereas S1 gives it only for normalized p (∑ a, p a = 1); an unnormalized p is not definitionally normalized, and rescaling is not structural. (2) Its second conjunct negative_weight_gives_negative_triple is a universal statement (every negative weight with positive base gives a negative triple), whereas S2 is a single existential counterexample and S1 is about nonnegativity; no universal implication about arbitrary negative weights follows from them."

end Alignment.Shadows.PairwiseClosureConditions.header_nonnegNeedsPointwise

/-! ## `PairwiseClosureConditions.header.conservationNotPositivity` -/
namespace Alignment.Shadows.PairwiseClosureConditions.header_conservationNotPositivity

sa_claim "PairwiseClosureConditions.header.conservationNotPositivity"
  group "PairwiseClosureConditions" required
  text "This is exactly the distinction that matters for auditing clustered pairwise closures: conservation alone does not imply positivity."
  impl PairwiseClosureConditions.negative_weight_gives_negative_triple

sa_fail_forward "PairwiseClosureConditions.header.conservationNotPositivity" 1 "impl negative_weight_gives_negative_triple is the pointwise implication ∀ base p a, 0 < base → p a < 0 → tripleTerm base p a < 0. It says nothing about conservation: no weight family with ∑ a, tripleTerm base p a = base (or ∑ p = 1) and a negative entry is exhibited. S1 is the non-implication 'conservation alone does not imply positivity' as a counterexample: ∃ α (Fintype), base ≥ 0, p with ∑ a, tripleTerm base p a = base and some tripleTerm base p a < 0. That existence is not stated by impl; a checker would have to supply the witness (e.g. Bool, p = (2, -1), base = 1) and verify the conservation equation and the sign facts by closed kernel computation on ℚ, which also proves the negative triple directly, so S1 is provable from scratch and h would be inessential (README Known limitations 1). The registry impl_note says the non-implication is 'only implicit'."

sa_fail_forward "PairwiseClosureConditions.header.conservationNotPositivity" 2 "impl negative_weight_gives_negative_triple is the pointwise implication ∀ base p a, 0 < base → p a < 0 → tripleTerm base p a < 0 and never mentions normalization. S2 requires ∃ α (Fintype), base ≥ 0, p with ∑ a, p a = 1 and some tripleTerm base p a < 0 (normalized weights that are not positive). impl exhibits no such family; its content would have to come entirely from a checker-supplied witness (e.g. Bool, p = (2, -1), base = 1) checked by closed kernel computation, which proves the whole of S2 without h (README Known limitations 1). The registry notes anticipate this failure ('no existence statement')."

sa_fail_backward "PairwiseClosureConditions.header.conservationNotPositivity" "impl is a universal statement (every negative weight with a strictly positive base gives a strictly negative triple, for every finite α, base and p). S1 and S2 are single existential counterexamples; they do not imply anything about arbitrary negative weights, so impl does not follow from the shadows. impl and the text are about different notions: a pointwise sign mechanism versus the non-implication 'conservation ⇏ positivity'."

end Alignment.Shadows.PairwiseClosureConditions.header_conservationNotPositivity

/-! ## `PairwiseClosureConditions.tripleMassConserved` -/
namespace Alignment.Shadows.PairwiseClosureConditions.tripleMassConserved

sa_claim "PairwiseClosureConditions.tripleMassConserved" group "PairwiseClosureConditions" required
  text "Normalization of the closure weights is enough to conserve the total triple mass. No sign condition on `p` is needed for this statement."
  impl PairwiseClosureConditions.triple_mass_conserved

@[sa_forward "PairwiseClosureConditions.tripleMassConserved" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.tripleMassConserved") : S1 := by
  intro α _ _ base p _hb hn
  exact h base p hn

@[sa_forward "PairwiseClosureConditions.tripleMassConserved" 2]
theorem fwd2 (h : sa_impl% "PairwiseClosureConditions.tripleMassConserved") : S2 := by
  intro α _ _ base p hn
  exact h base p hn

@[sa_backward "PairwiseClosureConditions.tripleMassConserved"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "PairwiseClosureConditions.tripleMassConserved" := by
  intro α _ _ base p hn
  exact s2 base p hn

end Alignment.Shadows.PairwiseClosureConditions.tripleMassConserved

/-! ## `PairwiseClosureConditions.tripleTermNonneg` -/
namespace Alignment.Shadows.PairwiseClosureConditions.tripleTermNonneg

sa_claim "PairwiseClosureConditions.tripleTermNonneg" group "PairwiseClosureConditions" required
  text "If the base term and all closure weights are nonnegative, then every closed triple term is nonnegative."
  impl PairwiseClosureConditions.triple_term_nonneg

/-- The impl quantifies the state `a` before the hypotheses; S1 after them. -/
@[sa_forward "PairwiseClosureConditions.tripleTermNonneg" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.tripleTermNonneg") : S1 := by
  intro α _ _ base p hb hs a
  exact h base p a hb hs

@[sa_backward "PairwiseClosureConditions.tripleTermNonneg"]
theorem bwd (s1 : S1) : sa_impl% "PairwiseClosureConditions.tripleTermNonneg" := by
  intro α _ _ base p a hb hs
  exact s1 base p hb hs a

end Alignment.Shadows.PairwiseClosureConditions.tripleTermNonneg

/-! ## `PairwiseClosureConditions.weightInUnitInterval` -/
namespace Alignment.Shadows.PairwiseClosureConditions.weightInUnitInterval

sa_claim "PairwiseClosureConditions.weightInUnitInterval" group "PairwiseClosureConditions"
  required
  text "Under nonnegative normalized weights, each individual closure weight lies in `[0,1]`."
  impl PairwiseClosureConditions.weight_in_unit_interval

@[sa_forward "PairwiseClosureConditions.weightInUnitInterval" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.weightInUnitInterval") : S1 := by
  intro α _ _ p hn hs a
  exact (h p a hs hn).2

/-- The lower bound `0 ≤ p a` of the impl is its own hypothesis `hs a`. -/
@[sa_backward "PairwiseClosureConditions.weightInUnitInterval"]
theorem bwd (s1 : S1) : sa_impl% "PairwiseClosureConditions.weightInUnitInterval" := by
  intro α _ _ p a hs hn
  exact ⟨hs a, s1 p hn hs a⟩

end Alignment.Shadows.PairwiseClosureConditions.weightInUnitInterval

/-! ## `PairwiseClosureConditions.negativeWeightGivesNegativeTriple.a` -/
namespace Alignment.Shadows.PairwiseClosureConditions.negativeWeightGivesNegativeTriple_a

sa_claim "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.a"
  group "PairwiseClosureConditions" required
  text "If some closure weight is negative and the base term is strictly positive, then the corresponding closed triple is negative."
  impl PairwiseClosureConditions.negative_weight_gives_negative_triple

/-- Same statement with the two hypotheses swapped. -/
@[sa_forward "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.a" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.a") :
    S1 := by
  intro α _ _ base p a hp hb
  exact h base p a hb hp

@[sa_backward "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.a"]
theorem bwd (s1 : S1) :
    sa_impl% "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.a" := by
  intro α _ _ base p a hb hp
  exact s1 base p a hp hb

end Alignment.Shadows.PairwiseClosureConditions.negativeWeightGivesNegativeTriple_a

/-! ## `PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b` -/
namespace Alignment.Shadows.PairwiseClosureConditions.negativeWeightGivesNegativeTriple_b

sa_claim "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b"
  group "PairwiseClosureConditions" required
  text "This shows why mass conservation alone cannot certify positivity."
  impl PairwiseClosureConditions.negative_weight_gives_negative_triple

sa_fail_forward "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b" 1 "impl negative_weight_gives_negative_triple is the pointwise implication ∀ base p a, 0 < base → p a < 0 → tripleTerm base p a < 0 and does not mention mass conservation. S1 requires the counterexample ∃ α (Fintype), base ≥ 0, p with ∑ a, tripleTerm base p a = base and some tripleTerm base p a < 0 ('mass conservation alone cannot certify positivity'). impl exhibits no weight family whose triple mass is conserved; the witness and its conservation equation would have to be supplied by the checker and checked by closed kernel computation on ℚ (e.g. Bool, p = (2, -1), base = 1), which also yields the negative triple without h, so S1 is provable from scratch and h would be inessential (README Known limitations 1). The registry impl_note: 'no statement combines ∑ p = 1 with a negative weight'."

sa_fail_forward "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b" 2 "impl negative_weight_gives_negative_triple (∀ base p a, 0 < base → p a < 0 → tripleTerm base p a < 0) never combines normalization with a negative weight. S2 requires ∃ α (Fintype), base ≥ 0, p with ∑ a, p a = 1 and some tripleTerm base p a < 0. That existence is not in impl; a proof would rest on a checker-supplied witness verified by closed kernel computation, which proves S2 without h (README Known limitations 1)."

sa_fail_backward "PairwiseClosureConditions.negativeWeightGivesNegativeTriple.b" "impl is universal (every negative weight with strictly positive base gives a strictly negative triple). S1 and S2 are single existential counterexamples and imply nothing about arbitrary negative weights, so impl does not follow from them. The statements are about different notions: a pointwise sign mechanism versus the non-implication 'conservation ⇏ positivity'."

end Alignment.Shadows.PairwiseClosureConditions.negativeWeightGivesNegativeTriple_b

/-! ## `PairwiseClosureConditions.normalizedNonnegativeClosureSafe` -/
namespace Alignment.Shadows.PairwiseClosureConditions.normalizedNonnegativeClosureSafe

sa_claim "PairwiseClosureConditions.normalizedNonnegativeClosureSafe"
  group "PairwiseClosureConditions" required
  text "A packaged version of the safe regime: normalized nonnegative weights yield both total-mass conservation and pointwise nonnegativity of the triple terms."
  impl PairwiseClosureConditions.normalized_nonnegative_closure_safe

@[sa_forward "PairwiseClosureConditions.normalizedNonnegativeClosureSafe" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.normalizedNonnegativeClosureSafe") :
    S1 := by
  intro α _ _ base p hb hn hs
  exact (h base p hb hs hn).1

@[sa_forward "PairwiseClosureConditions.normalizedNonnegativeClosureSafe" 2]
theorem fwd2 (h : sa_impl% "PairwiseClosureConditions.normalizedNonnegativeClosureSafe") :
    S2 := by
  intro α _ _ base p hb hn hs
  exact (h base p hb hs hn).2

@[sa_backward "PairwiseClosureConditions.normalizedNonnegativeClosureSafe"]
theorem bwd (s1 : S1) (s2 : S2) :
    sa_impl% "PairwiseClosureConditions.normalizedNonnegativeClosureSafe" := by
  intro α _ _ base p hb hs hn
  exact ⟨s1 base p hb hn hs, s2 base p hb hn hs⟩

end Alignment.Shadows.PairwiseClosureConditions.normalizedNonnegativeClosureSafe

/-! ## `PairwiseClosureConditions.convexMixNonneg` -/
namespace Alignment.Shadows.PairwiseClosureConditions.convexMixNonneg

sa_claim "PairwiseClosureConditions.convexMixNonneg" group "PairwiseClosureConditions" required
  text "A convex mixture of nonnegative weights is nonnegative."
  impl PairwiseClosureConditions.convexMix_nonneg

@[sa_forward "PairwiseClosureConditions.convexMixNonneg" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.convexMixNonneg") : S1 := by
  intro φ x y h0 h1 hx hy
  exact h φ x y h0 h1 hx hy

@[sa_backward "PairwiseClosureConditions.convexMixNonneg"]
theorem bwd (s1 : S1) : sa_impl% "PairwiseClosureConditions.convexMixNonneg" := by
  intro φ x y h0 h1 hx hy
  exact s1 φ x y h0 h1 hx hy

end Alignment.Shadows.PairwiseClosureConditions.convexMixNonneg

/-! ## `PairwiseClosureConditions.barnardWeightsNormalized.a` -/
namespace Alignment.Shadows.PairwiseClosureConditions.barnardWeightsNormalized_a

sa_claim "PairwiseClosureConditions.barnardWeightsNormalized.a" group "PairwiseClosureConditions"
  required text "A convex mixture of normalized weight families is normalized."
  impl PairwiseClosureConditions.barnardWeights_normalized

/-- The impl holds for every φ; the convexity hypotheses of S1 are discarded. -/
@[sa_forward "PairwiseClosureConditions.barnardWeightsNormalized.a" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.barnardWeightsNormalized.a") : S1 := by
  intro α _ _ φ p_uc p_c _h0 _h1 huc hc
  exact h φ p_uc p_c huc hc

sa_fail_backward "PairwiseClosureConditions.barnardWeightsNormalized.a" "impl barnardWeights_normalized is stronger than the text: it gives ∑ a, barnardWeights φ p_uc p_c a = 1 for EVERY φ ∈ ℚ (an affine combination (1 - φ)·p_uc + φ·p_c of two normalized families), with no hypothesis 0 ≤ φ ≤ 1. S1, the text's 'convex mixture', gives the normalization only for φ ∈ [0,1] (DataTypes: 'convex' means 0 ≤ φ ∧ φ ≤ 1). For φ outside [0,1] (e.g. φ = 2) S1 says nothing, so impl does not follow from S1. The registry impl_note records the same: 'for ANY φ (affine combination), i.e. stronger than convex'."

end Alignment.Shadows.PairwiseClosureConditions.barnardWeightsNormalized_a

/-! ## `PairwiseClosureConditions.barnardWeightsNonneg` -/
namespace Alignment.Shadows.PairwiseClosureConditions.barnardWeightsNonneg

sa_claim "PairwiseClosureConditions.barnardWeightsNonneg" group "PairwiseClosureConditions"
  required
  text "Barnard-style mixed weights stay nonnegative when both the unclustered and clustered probability models are pointwise nonnegative."
  impl PairwiseClosureConditions.barnardWeights_nonneg

@[sa_forward "PairwiseClosureConditions.barnardWeightsNonneg" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.barnardWeightsNonneg") : S1 := by
  intro α _ _ φ p_uc p_c h0 h1 huc hc a
  exact h φ p_uc p_c h0 h1 huc hc a

@[sa_backward "PairwiseClosureConditions.barnardWeightsNonneg"]
theorem bwd (s1 : S1) : sa_impl% "PairwiseClosureConditions.barnardWeightsNonneg" := by
  intro α _ _ φ p_uc p_c h0 h1 huc hc a
  exact s1 φ p_uc p_c h0 h1 huc hc a

end Alignment.Shadows.PairwiseClosureConditions.barnardWeightsNonneg

/-! ## `PairwiseClosureConditions.barnardStyleClosureSafe` -/
namespace Alignment.Shadows.PairwiseClosureConditions.barnardStyleClosureSafe

sa_claim "PairwiseClosureConditions.barnardStyleClosureSafe" group "PairwiseClosureConditions"
  required
  text "Barnard-style closures are safe whenever both constituent probability models are normalized and nonnegative."
  impl PairwiseClosureConditions.barnard_style_closure_safe

/-- The impl orders the hypotheses `0 ≤ base, 0 ≤ φ, φ ≤ 1, p_uc ≥ 0, p_c ≥ 0, ∑ p_uc = 1,
∑ p_c = 1`; the shadows interleave normalization and sign per model. -/
@[sa_forward "PairwiseClosureConditions.barnardStyleClosureSafe" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.barnardStyleClosureSafe") : S1 := by
  intro α _ _ base φ p_uc p_c hb h0 h1 hn1 hs1 hn2 hs2
  exact (h base φ p_uc p_c hb h0 h1 hs1 hs2 hn1 hn2).1

@[sa_forward "PairwiseClosureConditions.barnardStyleClosureSafe" 2]
theorem fwd2 (h : sa_impl% "PairwiseClosureConditions.barnardStyleClosureSafe") : S2 := by
  intro α _ _ base φ p_uc p_c hb h0 h1 hn1 hs1 hn2 hs2
  exact (h base φ p_uc p_c hb h0 h1 hs1 hs2 hn1 hn2).2

@[sa_backward "PairwiseClosureConditions.barnardStyleClosureSafe"]
theorem bwd (s1 : S1) (s2 : S2) :
    sa_impl% "PairwiseClosureConditions.barnardStyleClosureSafe" := by
  intro α _ _ base φ p_uc p_c hb h0 h1 hs1 hs2 hn1 hn2
  exact ⟨s1 base φ p_uc p_c hb h0 h1 hn1 hs1 hn2 hs2, s2 base φ p_uc p_c hb h0 h1 hn1 hs1 hn2 hs2⟩

end Alignment.Shadows.PairwiseClosureConditions.barnardStyleClosureSafe

/-! ## `PairwiseClosureConditions.keelingFactorNonneg` -/
namespace Alignment.Shadows.PairwiseClosureConditions.keelingFactorNonneg

sa_claim "PairwiseClosureConditions.keelingFactorNonneg" group "PairwiseClosureConditions" required
  text "If the Keeling correlation correction stays nonnegative, then the Keeling weight factor is nonnegative."
  impl PairwiseClosureConditions.keelingFactor_nonneg

@[sa_forward "PairwiseClosureConditions.keelingFactorNonneg" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.keelingFactorNonneg") : S1 := by
  intro φ corr h0 h1 hc
  exact h φ corr h0 h1 hc

sa_fail_forward "PairwiseClosureConditions.keelingFactorNonneg" 2 "SHADOW?: impl keelingFactor_nonneg assumes 0 ≤ φ ≤ 1 (hφ0, hφ1); S2 drops the φ range and quantifies over every φ ∈ ℚ. S2 is false, so no implementation could prove it: keelingFactor φ corr = (1 - φ) + φ·corr, and φ = 2, corr = 0 give keelingFactor 2 0 = -1 < 0 with 0 ≤ corr. The text 'If the Keeling correlation correction stays nonnegative, then the Keeling weight factor is nonnegative' concerns 'the Keeling weight factor', i.e. Keeling's clustered closure, whose φ is the clustering coefficient (DataTypes: 'Keeling-style multiplicative clustering factor'; 'The mixing parameter φ is the clustering weight'), with domain [0,1]. The literal all-φ reading makes the text false; φ ∈ [0,1] is its implicit domain, which is exactly S1 (proved)."

@[sa_backward "PairwiseClosureConditions.keelingFactorNonneg"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "PairwiseClosureConditions.keelingFactorNonneg" := by
  intro φ corr h0 h1 hc
  exact s1 φ corr h0 h1 hc

end Alignment.Shadows.PairwiseClosureConditions.keelingFactorNonneg

/-! ## `PairwiseClosureConditions.keelingWeightsNonneg` -/
namespace Alignment.Shadows.PairwiseClosureConditions.keelingWeightsNonneg

sa_claim "PairwiseClosureConditions.keelingWeightsNonneg" group "PairwiseClosureConditions"
  required
  text "If the baseline weights and the correlation correction are both nonnegative, then the Keeling-reweighted weights are nonnegative."
  impl PairwiseClosureConditions.keelingWeights_nonneg

@[sa_forward "PairwiseClosureConditions.keelingWeightsNonneg" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.keelingWeightsNonneg") : S1 := by
  intro α _ _ φ p corr h0 h1 hp hc a
  exact h φ p corr h0 h1 hp hc a

sa_fail_forward "PairwiseClosureConditions.keelingWeightsNonneg" 2 "SHADOW?: impl keelingWeights_nonneg assumes 0 ≤ φ ≤ 1 (hφ0, hφ1); S2 quantifies over every φ ∈ ℚ. S2 is false: keelingWeights φ p corr a = p a · ((1 - φ) + φ·corr a), and on α = Unit with p ≡ 1, corr ≡ 0 (both nonnegative) and φ = 2 the weight is 1·(-1) = -1 < 0. The text 'If the baseline weights and the correlation correction are both nonnegative, then the Keeling-reweighted weights are nonnegative' is about Keeling's clustered closure, whose φ is the clustering coefficient with domain [0,1] (DataTypes: 'The mixing parameter φ is the clustering weight'); the all-φ reading makes the text false. The implicit-domain reading is S1 (proved)."

@[sa_backward "PairwiseClosureConditions.keelingWeightsNonneg"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "PairwiseClosureConditions.keelingWeightsNonneg" := by
  intro α _ _ φ p corr h0 h1 hp hc a
  exact s1 φ p corr h0 h1 hp hc a

end Alignment.Shadows.PairwiseClosureConditions.keelingWeightsNonneg

/-! ## `PairwiseClosureConditions.keelingStyleClosureSafe.a` -/
namespace Alignment.Shadows.PairwiseClosureConditions.keelingStyleClosureSafe_a

sa_claim "PairwiseClosureConditions.keelingStyleClosureSafe.a" group "PairwiseClosureConditions"
  required
  text "Keeling-style closures are safe only after an *additional normalization theorem* is supplied."
  impl PairwiseClosureConditions.keeling_style_closure_safe

/-- The impl orders the hypotheses `0 ≤ base, 0 ≤ φ, φ ≤ 1, …`; S1/S2 put `φ` first. -/
@[sa_forward "PairwiseClosureConditions.keelingStyleClosureSafe.a" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.keelingStyleClosureSafe.a") : S1 := by
  intro α _ _ base φ p corr h0 h1 hb hp hc hn
  exact (h base φ p corr hb h0 h1 hp hc hn).1

@[sa_forward "PairwiseClosureConditions.keelingStyleClosureSafe.a" 2]
theorem fwd2 (h : sa_impl% "PairwiseClosureConditions.keelingStyleClosureSafe.a") : S2 := by
  intro α _ _ base φ p corr h0 h1 hb hp hc hn
  exact (h base φ p corr hb h0 h1 hp hc hn).2

sa_fail_forward "PairwiseClosureConditions.keelingStyleClosureSafe.a" 3 "SHADOW?: impl keeling_style_closure_safe assumes 0 ≤ φ ≤ 1 (hφ0, hφ1) and so gives conservation of the Keeling closure only for φ ∈ [0,1]; S3 requires it for every φ ∈ ℚ, and no hypothesis of S3 supplies 0 ≤ φ or φ ≤ 1, so S3 does not follow from h. S3 itself is true (conservation needs only the supplied normalization ∑ a, keelingWeights φ p corr a = 1), so if the all-φ reading were intended the remedy would be a trusted conservation theorem without hφ0/hφ1. But the text 'Keeling-style closures are safe only after an additional normalization theorem is supplied' is about Keeling's clustered closure, whose φ is the clustering coefficient with domain [0,1] (DataTypes: 'Keeling-style multiplicative clustering factor'; 'The mixing parameter φ is the clustering weight'), and under the all-φ reading the text's 'safe' is false (see S4). The in-domain reading is S1 (proved)."

sa_fail_forward "PairwiseClosureConditions.keelingStyleClosureSafe.a" 4 "SHADOW?: impl assumes 0 ≤ φ ≤ 1 (hφ0, hφ1); S4 (nonnegativity of the Keeling triple terms for every φ ∈ ℚ, given normalization, base ≥ 0, p ≥ 0, corr ≥ 0) is false: on α = Bool with φ = 2, corr = (0, 2), p ≡ 1/2 and base = 1 the Keeling factors are (1 - 2) + 2·0 = -1 and (1 - 2) + 2·2 = 3, the weights (-1/2, 3/2) sum to 1, and tripleTerm 1 w true = -1/2 < 0. The text is about Keeling's clustered closure, whose φ is the clustering coefficient in [0,1] (DataTypes: 'The mixing parameter φ is the clustering weight'); the all-φ reading makes 'Keeling-style closures are safe' false. The in-domain reading is S2 (proved)."

sa_fail_forward "PairwiseClosureConditions.keelingStyleClosureSafe.a" 5 "impl proves only sufficiency: under 0 ≤ base, 0 ≤ φ ≤ 1, p ≥ 0, corr ≥ 0 AND the supplied normalization ∑ a, keelingWeights φ p corr a = 1, the Keeling closure is safe (conservation ∧ pointwise nonnegativity). S5 is the necessity half of 'safe ONLY after an additional normalization theorem is supplied': ∃ α (Fintype), base, φ ∈ [0,1], p ≥ 0, corr ≥ 0 such that the closure is NOT safe. Every conclusion obtainable from h is a safety fact, never its negation, and h can only be applied to families that are already normalized; the failure of safety needs a witness violating normalization (e.g. Unit, φ = 1, p ≡ 1, corr ≡ 2, base = 1, total mass 2 ≠ 1), whose refutation 2 ≠ 1 is a closed computation independent of h. So any proof of S5 would be vacuous. The registry impl_note: 'The only after (necessity: without it conservation can fail) is not proved'."

/-- S1 and S2 are the impl's two conclusions with the hypotheses reordered. -/
@[sa_backward "PairwiseClosureConditions.keelingStyleClosureSafe.a"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) (_s4 : S4) (_s5 : S5) :
    sa_impl% "PairwiseClosureConditions.keelingStyleClosureSafe.a" := by
  intro α _ _ base φ p corr hb h0 h1 hp hc hn
  exact ⟨s1 base φ p corr h0 h1 hb hp hc hn, s2 base φ p corr h0 h1 hb hp hc hn⟩

end Alignment.Shadows.PairwiseClosureConditions.keelingStyleClosureSafe_a

/-! ## `PairwiseClosureConditions.keelingStyleClosureSafe.b` -/
namespace Alignment.Shadows.PairwiseClosureConditions.keelingStyleClosureSafe_b

sa_claim "PairwiseClosureConditions.keelingStyleClosureSafe.b" group "PairwiseClosureConditions"
  required
  text "Positivity follows from nonnegative baseline weights and nonnegative correlation corrections,"
  impl PairwiseClosureConditions.keelingWeights_nonneg PairwiseClosureConditions.triple_term_nonneg

/-- Compose the two conjuncts: `keelingWeights_nonneg` gives nonnegative Keeling weights, and
`triple_term_nonneg` (at the weight family `keelingWeights φ p corr`) the nonnegative triples. -/
@[sa_forward "PairwiseClosureConditions.keelingStyleClosureSafe.b" 1]
theorem fwd1 (h : sa_impl% "PairwiseClosureConditions.keelingStyleClosureSafe.b") : S1 := by
  intro α _ _ base φ p corr h0 h1 hb hp hc a
  exact h.2 base (PairwiseClosureConditions.keelingWeights φ p corr) a hb (h.1 φ p corr h0 h1 hp hc)

sa_fail_forward "PairwiseClosureConditions.keelingStyleClosureSafe.b" 2 "SHADOW?: impl's first conjunct keelingWeights_nonneg assumes 0 ≤ φ ≤ 1 (hφ0, hφ1); S2 requires nonnegative Keeling triple terms for every φ ∈ ℚ. S2 is false: on α = Unit with base = 1, p ≡ 1, corr ≡ 0 (all nonnegative) and φ = 2, tripleTerm 1 (keelingWeights 2 p corr) () = 1·(1·((1 - 2) + 2·0)) = -1 < 0. The text 'Positivity follows from nonnegative baseline weights and nonnegative correlation corrections' is about Keeling's clustered closure, whose φ is the clustering coefficient in [0,1] (DataTypes: 'The mixing parameter φ is the clustering weight'); the all-φ reading makes it false. The in-domain reading is S1 (proved)."

sa_fail_backward "PairwiseClosureConditions.keelingStyleClosureSafe.b" "impl is the conjunction of two general lemmas, each stronger than or different from the composite shadow S1 (nonnegativity of tripleTerm base (keelingWeights φ p corr) a for base ≥ 0, φ ∈ [0,1], p ≥ 0, corr ≥ 0). (1) keelingWeights_nonneg concludes 0 ≤ keelingWeights φ p corr a itself, with no base term; from S1 one only gets 0 ≤ tripleTerm base w a = base·w a, and recovering 0 ≤ w a (e.g. at base = 1) needs 1·x = x on ℚ (one_mul, not definitional for a variable x) and 0 ≤ 1. (2) triple_term_nonneg is about an ARBITRARY nonnegative weight family p, not only Keeling-reweighted ones; an arbitrary p is not definitionally keelingWeights φ p' corr for any φ, p', corr (p a·((1 - 0) + 0·c) = p a needs ring laws). So impl does not follow structurally from S1 (and S2, which is false)."

end Alignment.Shadows.PairwiseClosureConditions.keelingStyleClosureSafe_b

/-! ## `PairwiseClosureConditions.barnardWeightsNormalized.b` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.PairwiseClosureConditions.barnardWeightsNormalized_b

sa_claim "PairwiseClosureConditions.barnardWeightsNormalized.b" group "PairwiseClosureConditions"
  text "This is the key algebraic fact behind Barnard's improved closure: it mixes the unclustered weights (probability 1 − φ) with the normalised clustered weights (probability φ), which gives Σ_A [ASI] = (n − 1)[SI] (Barnard 2018, PhD thesis, University of Sussex, §4.3.2, \"Improved closure\")."
  impl

end Alignment.Shadows.PairwiseClosureConditions.barnardWeightsNormalized_b
