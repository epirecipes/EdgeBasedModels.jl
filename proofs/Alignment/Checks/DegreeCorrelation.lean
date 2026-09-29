import Alignment.Registry
import Alignment.Shadows.DegreeCorrelation

/-!
# Checkers: group `DegreeCorrelation`

Checker author (SA-PASS role 3, non-blind). For every claim of `EBCMCategory/DegreeCorrelation.lean`
with `status: implemented` this file holds the `sa_claim` registration (verbatim registry text,
registry `impl` list in registry order), the forward checkers `sa_impl% → Sᵢ`, the backward checker
`S₁ → … → Sₙ → sa_impl%`, and `sa_fail_*` records where a check cannot be proved structurally
because the implementation says something different from the shadow.

No bridges are declared: every passing check only needs definitional unfolding of the trusted
definitions (`q1`, `q2`, `excessDegree`, `secondFactorial`, `uncorrelated_R0`, …), and none of
the failing checks can be repaired by identifying a trusted definition with the text's notion.

Conventions of the proofs below (README "Writing structural proofs"): hypotheses, projections of
the conjunction `h`, `Eq.trans`, `show`, `rw [hyp]`, `rfl`, and (backward only) instantiation of a
shadow at a concrete `DegreeMomentData` built with `DegreeMomentData.mk` (the proof arguments of a
data term are skipped by the audit).
-/

/-! ## `DegreeCorrelation.R79-sec` -/

namespace Alignment.Shadows.DegreeCorrelation.R79_sec

sa_claim "DegreeCorrelation.R79-sec" group "DegreeCorrelation" required
  text "The excess-degree probability q_l = l·p_l/⟨k⟩ is a valid distribution."
  impl neutral_mixing_sums_to_one

sa_fail_forward "DegreeCorrelation.R79-sec" 1 "impl (neutral_mixing_sums_to_one) only states k1*p1/(k1*p1+k2*p2) + k2*p2/(k1*p1+k2*p2) = 1 for four free reals; S1 requires 0 ≤ l*p_l/m for every degree l of an arbitrary degree distribution p : ℕ → ℝ. The impl says nothing about non-negativity and nothing about general (ℕ-indexed, possibly infinite) degree distributions."

sa_fail_forward "DegreeCorrelation.R79-sec" 2 "impl (neutral_mixing_sums_to_one) is a two-term identity over free reals; S2 requires HasSum (fun l => l*p_l/m) 1 for an arbitrary degree distribution p : ℕ → ℝ with mean m > 0. The general (HasSum over ℕ) normalisation is not stated by the impl."

sa_fail_forward "DegreeCorrelation.R79-sec" 3 "S3 requires 0 ≤ q1 for every TwoDegreeData; impl (neutral_mixing_sums_to_one) states only the sum-to-one identity and contains no inequality, so non-negativity of q1 is not stated."

sa_fail_forward "DegreeCorrelation.R79-sec" 4 "S4 requires 0 ≤ q2 for every TwoDegreeData; impl (neutral_mixing_sums_to_one) states only the sum-to-one identity and contains no inequality, so non-negativity of q2 is not stated."

sa_fail_forward "DegreeCorrelation.R79-sec" 5 "free-scalar abstraction: impl is ∀ k1 k2 p1 p2 : ℝ, p1 + p2 = 1 → k1*p1 + k2*p2 > 0 → … = 1, not a statement about TwoDegreeData.q1/q2. Instantiating it at d.k1 d.k2 d.p1 d.p2 needs the proofs d.p_sum and 0 < d.k1*d.p1 + d.k2*d.p2 (the latter from d.k1_pos, d.p1_pos, d.k2_pos, d.p2_pos via mul_pos/add_pos): data invariants and library lemmas, which are not structural. (q_sum_one, which states S5 directly, is not in this claim's impl list.)"

sa_fail_backward "DegreeCorrelation.R79-sec" "impl quantifies over arbitrary reals k1 k2 p1 p2 (only p1 + p2 = 1 and k1*p1 + k2*p2 > 0 assumed; k_i, p_i may be negative or zero). S3-S5 speak only about TwoDegreeData (k_i > 0, p_i > 0, 0 ≤ r ≤ 1), and a TwoDegreeData cannot be built from the impl's hypotheses (0 < k1, 0 < p1, … are unavailable); S1/S2 speak only about ℕ-indexed distributions with HasSum, and turning the two-point case into HasSum facts needs library lemmas (hasSum_fintype, …). So the impl is not derivable from the shadows."

end Alignment.Shadows.DegreeCorrelation.R79_sec

/-! ## `DegreeCorrelation.R79b` -/

namespace Alignment.Shadows.DegreeCorrelation.R79b

sa_claim "DegreeCorrelation.R79b" group "DegreeCorrelation" required
  text "For a two-degree network with degrees k₁, k₂ and fractions p₁, p₂: the excess-degree probabilities q₁ = k₁·p₁/⟨k⟩ and q₂ = k₂·p₂/⟨k⟩ sum to 1 when ⟨k⟩ = k₁·p₁ + k₂·p₂."
  impl neutral_mixing_sums_to_one

sa_fail_forward "DegreeCorrelation.R79b" 1 "free-scalar abstraction: impl is ∀ k1 k2 p1 p2 : ℝ, p1 + p2 = 1 → k1*p1 + k2*p2 > 0 → k1*p1/(k1*p1+k2*p2) + k2*p2/(k1*p1+k2*p2) = 1, not a statement about TwoDegreeData.q1/q2. Using it for S1 (∀ d, d.q1 + d.q2 = 1) needs the hypothesis proofs d.p_sum and 0 < d.k1*d.p1 + d.k2*d.p2 (from the positivity fields via mul_pos/add_pos): data invariants and library lemmas, not structural."

sa_fail_forward "DegreeCorrelation.R79b" 2 "free-scalar abstraction: S2 is ∀ d : TwoDegreeData, ∀ m, m = k1*p1 + k2*p2 → k1*p1/m + k2*p2/m = 1. After rw [hm] the goal is the impl's conclusion at d.k1 d.k2 d.p1 d.p2, but the impl's extra hypotheses p1 + p2 = 1 (unused in its proof) and k1*p1 + k2*p2 > 0 can only be discharged from the TwoDegreeData invariants (d.p_sum, d.k1_pos, d.p1_pos, …) with mul_pos/add_pos, which is not structural."

sa_fail_backward "DegreeCorrelation.R79b" "impl quantifies over arbitrary reals k1 k2 p1 p2 with only p1 + p2 = 1 and k1*p1 + k2*p2 > 0; S1 and S2 quantify over TwoDegreeData (k_i > 0, p_i > 0, 0 ≤ r ≤ 1). A TwoDegreeData cannot be built from the impl's hypotheses (0 < k1, 0 < k2, 0 < p1, 0 < p2 are unavailable and false in general, e.g. k2 < 0), so the impl is not derivable from the shadows."

end Alignment.Shadows.DegreeCorrelation.R79b

/-! ## `DegreeCorrelation.R80-sec` -/

namespace Alignment.Shadows.DegreeCorrelation.R80_sec

sa_claim "DegreeCorrelation.R80-sec" group "DegreeCorrelation" required
  text "For neutral mixing, R₀ = T · ⟨k²-k⟩/⟨k⟩ = T · ψ''(1)/ψ'(1)."
  impl uncorrelated_R0_formula

sa_fail_forward "DegreeCorrelation.R80-sec" 1 "S1 (uncorrelated_R0 Tr ψ = Tr * ((⟨k²⟩ - ⟨k⟩) / ⟨k⟩)) is definitionally true: uncorrelated_R0 Tr ψ unfolds to Tr * excessDegree ψ = Tr * (secondFactorial ψ / mean ψ) = Tr * ((secondMoment - mean) / mean), so it holds by rfl without the impl. The impl states the left-associated form Tr * (secondMoment - mean) / mean = (Tr * (secondMoment - mean)) / mean; deriving S1 from it needs mul_div_assoc (library lemma), and no trusted definition can carry that step as a bridge. The only structural proof ignores the impl (vacuous). Note: the text 'T · ⟨k²-k⟩/⟨k⟩' read left-to-right, (T·⟨k²-k⟩)/⟨k⟩, would coincide with the impl."

sa_fail_forward "DegreeCorrelation.R80-sec" 2 "S2 (uncorrelated_R0 Tr ψ = Tr * (secondFactorial ψ / mean ψ)) is definitionally true (uncorrelated_R0 := T * excessDegree, excessDegree := secondFactorial / mean), so it holds by rfl without the impl. The impl states Tr * (secondMoment - mean) / mean = (Tr * (secondMoment - mean)) / mean; deriving S2 from it needs mul_div_assoc (library lemma). The only structural proof ignores the impl (vacuous). Note: the text 'T · ψ''(1)/ψ'(1)' read left-to-right, (T·ψ''(1))/ψ'(1), would coincide with the impl up to unfolding secondFactorial."

sa_fail_backward "DegreeCorrelation.R80-sec" "S1 and S2 are both definitional unfoldings of uncorrelated_R0 (Tr * ((⟨k²⟩ - ⟨k⟩)/⟨k⟩)), so they carry no information beyond rfl. The impl is the re-associated form uncorrelated_R0 T d = (T * (secondMoment - mean)) / mean; getting it from S1/S2 needs mul_div_assoc (library lemma), which is not structural."

end Alignment.Shadows.DegreeCorrelation.R80_sec

/-! ## `DegreeCorrelation.uncorrelatedR0Formula` -/

namespace Alignment.Shadows.DegreeCorrelation.uncorrelatedR0Formula

sa_claim "DegreeCorrelation.uncorrelatedR0Formula" group "DegreeCorrelation" required
  text "R₀ = T·(⟨k²⟩ - ⟨k⟩)/⟨k⟩ is the explicit formula."
  impl uncorrelated_R0_formula

@[sa_forward "DegreeCorrelation.uncorrelatedR0Formula" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.uncorrelatedR0Formula") : S1 :=
  fun Tr ψ => h Tr ψ

@[sa_backward "DegreeCorrelation.uncorrelatedR0Formula"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.uncorrelatedR0Formula" :=
  fun T d => s1 T d

end Alignment.Shadows.DegreeCorrelation.uncorrelatedR0Formula

/-! ## `DegreeCorrelation.meanDegPos` -/

namespace Alignment.Shadows.DegreeCorrelation.meanDegPos

sa_claim "DegreeCorrelation.meanDegPos" group "DegreeCorrelation" required
  text "Mean degree is positive."
  impl TwoDegreeData.meanDeg_pos

@[sa_forward "DegreeCorrelation.meanDegPos" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.meanDegPos") : S1 :=
  fun d => h d

@[sa_backward "DegreeCorrelation.meanDegPos"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.meanDegPos" :=
  fun d => s1 d

end Alignment.Shadows.DegreeCorrelation.meanDegPos

/-! ## `DegreeCorrelation.R83-sec` -/

namespace Alignment.Shadows.DegreeCorrelation.R83_sec

sa_claim "DegreeCorrelation.R83-sec" group "DegreeCorrelation" required
  text "Setting r = 0 in the mixing matrix gives C_{kl} = k·q_l = k·l·p_l/⟨k⟩, which is the neutral (uncorrelated) mixing matrix."
  impl neutral_C11 neutral_C12 neutral_C21 neutral_C22

@[sa_forward "DegreeCorrelation.R83-sec" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R83-sec") : S1 :=
  fun d hr => h.1 d hr

@[sa_forward "DegreeCorrelation.R83-sec" 2]
theorem fwd2 (h : sa_impl% "DegreeCorrelation.R83-sec") : S2 :=
  fun d hr => h.2.1 d hr

@[sa_forward "DegreeCorrelation.R83-sec" 3]
theorem fwd3 (h : sa_impl% "DegreeCorrelation.R83-sec") : S3 :=
  fun d hr => h.2.2.1 d hr

@[sa_forward "DegreeCorrelation.R83-sec" 4]
theorem fwd4 (h : sa_impl% "DegreeCorrelation.R83-sec") : S4 :=
  fun d hr => h.2.2.2 d hr

/-- `q1 d` unfolds definitionally to `d.k1 * d.p1 / d.meanDeg` (the text's `l·p_l/⟨k⟩`). -/
@[sa_forward "DegreeCorrelation.R83-sec" 5]
theorem fwd5 (h : sa_impl% "DegreeCorrelation.R83-sec") : S5 :=
  fun d hr => h.1 d hr

/-- `q2 d` unfolds definitionally to `d.k2 * d.p2 / d.meanDeg`. -/
@[sa_forward "DegreeCorrelation.R83-sec" 6]
theorem fwd6 (h : sa_impl% "DegreeCorrelation.R83-sec") : S6 :=
  fun d hr => h.2.1 d hr

@[sa_forward "DegreeCorrelation.R83-sec" 7]
theorem fwd7 (h : sa_impl% "DegreeCorrelation.R83-sec") : S7 :=
  fun d hr => h.2.2.1 d hr

@[sa_forward "DegreeCorrelation.R83-sec" 8]
theorem fwd8 (h : sa_impl% "DegreeCorrelation.R83-sec") : S8 :=
  fun d hr => h.2.2.2 d hr

@[sa_backward "DegreeCorrelation.R83-sec"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (_s5 : S5) (_s6 : S6) (_s7 : S7)
    (_s8 : S8) : sa_impl% "DegreeCorrelation.R83-sec" :=
  ⟨fun d hr => s1 d hr, fun d hr => s2 d hr, fun d hr => s3 d hr, fun d hr => s4 d hr⟩

end Alignment.Shadows.DegreeCorrelation.R83_sec

/-! ## `DegreeCorrelation.R83a` … `R83d` -/

namespace Alignment.Shadows.DegreeCorrelation.R83a

sa_claim "DegreeCorrelation.R83a" group "DegreeCorrelation" required
  text "**Result 83a.** When r=0, C₁₁ = k₁·q₁ (neutral mixing)."
  impl neutral_C11

@[sa_forward "DegreeCorrelation.R83a" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R83a") : S1 :=
  fun d hr => h d hr

@[sa_backward "DegreeCorrelation.R83a"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.R83a" :=
  fun d hr => s1 d hr

end Alignment.Shadows.DegreeCorrelation.R83a

namespace Alignment.Shadows.DegreeCorrelation.R83b

sa_claim "DegreeCorrelation.R83b" group "DegreeCorrelation" required
  text "**Result 83b.** When r=0, C₁₂ = k₁·q₂ (neutral mixing)."
  impl neutral_C12

@[sa_forward "DegreeCorrelation.R83b" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R83b") : S1 :=
  fun d hr => h d hr

@[sa_backward "DegreeCorrelation.R83b"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.R83b" :=
  fun d hr => s1 d hr

end Alignment.Shadows.DegreeCorrelation.R83b

namespace Alignment.Shadows.DegreeCorrelation.R83c

sa_claim "DegreeCorrelation.R83c" group "DegreeCorrelation" required
  text "**Result 83c.** When r=0, C₂₁ = k₂·q₁ (neutral mixing)."
  impl neutral_C21

@[sa_forward "DegreeCorrelation.R83c" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R83c") : S1 :=
  fun d hr => h d hr

@[sa_backward "DegreeCorrelation.R83c"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.R83c" :=
  fun d hr => s1 d hr

end Alignment.Shadows.DegreeCorrelation.R83c

namespace Alignment.Shadows.DegreeCorrelation.R83d

sa_claim "DegreeCorrelation.R83d" group "DegreeCorrelation" required
  text "**Result 83d.** When r=0, C₂₂ = k₂·q₂ (neutral mixing)."
  impl neutral_C22

@[sa_forward "DegreeCorrelation.R83d" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R83d") : S1 :=
  fun d hr => h d hr

@[sa_backward "DegreeCorrelation.R83d"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.R83d" :=
  fun d hr => s1 d hr

end Alignment.Shadows.DegreeCorrelation.R83d

/-! ## `DegreeCorrelation.R83e` -/

namespace Alignment.Shadows.DegreeCorrelation.R83e

sa_claim "DegreeCorrelation.R83e" group "DegreeCorrelation" required
  text "**Result 83e.** Under neutral mixing (r=0), the row sums of C equal the degree: C₁₁ + C₁₂ = k₁·(q₁ + q₂)."
  impl neutral_row_sum_type1

@[sa_forward "DegreeCorrelation.R83e" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R83e") : S1 :=
  fun d hr => h d hr

sa_fail_forward "DegreeCorrelation.R83e" 2 "impl (neutral_row_sum_type1) states only r = 0 → C11 + C12 = k1 * (q1 + q2); S2 requires the row sum to equal the degree, C11 + C12 = k1. That needs q1 + q2 = 1 (q_sum_one, not in this claim's impl list) and k1 * 1 = k1 (mul_one); the impl never states that the row sum equals the degree."

sa_fail_forward "DegreeCorrelation.R83e" 3 "impl (neutral_row_sum_type1) is about row 1 only (C11 + C12); S3 requires row 2 under r = 0, C21 + C22 = k2, which the impl does not mention (row2_sum_eq_degree, which covers it for every r, is not in this claim's impl list)."

@[sa_backward "DegreeCorrelation.R83e"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "DegreeCorrelation.R83e" :=
  fun d hr => s1 d hr

end Alignment.Shadows.DegreeCorrelation.R83e

/-! ## `DegreeCorrelation.R83f` -/

namespace Alignment.Shadows.DegreeCorrelation.R83f

sa_claim "DegreeCorrelation.R83f" group "DegreeCorrelation" required
  text "**Result 83f.** And q₁ + q₂ = 1, so the neutral row sum equals k₁."
  impl q_sum_one neutral_row_sum_type1

@[sa_forward "DegreeCorrelation.R83f" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R83f") : S1 :=
  fun d => h.1 d

sa_fail_forward "DegreeCorrelation.R83f" 2 "impl gives q1 + q2 = 1 and r = 0 → C11 + C12 = k1 * (q1 + q2), hence C11 + C12 = k1 * 1 after rw; the last step k1 * 1 = k1 is mul_one (a library lemma; real multiplication does not reduce definitionally), so 'the neutral row sum equals k1' is not stated by the impl and not structurally derivable from it. (row1_sum_eq_degree states C11 + C12 = k1 directly but is not in this claim's impl list.)"

sa_fail_backward "DegreeCorrelation.R83f" "the impl's second conjunct is r = 0 → C11 + C12 = k1 * (q1 + q2). From S2 (C11 + C12 = k1) and S1 (q1 + q2 = 1) the goal becomes k1 = k1 * 1 after rw [S1], which needs mul_one (library lemma); not structural."

end Alignment.Shadows.DegreeCorrelation.R83f

/-! ## `DegreeCorrelation.R84-sec` -/

namespace Alignment.Shadows.DegreeCorrelation.R84_sec

sa_claim "DegreeCorrelation.R84-sec" group "DegreeCorrelation" required
  text "For a Poisson degree distribution with mean κ, ⟨k²⟩ = κ² + κ, so ⟨k²-k⟩/⟨k⟩ = κ, and R₀ = T·κ under neutral mixing."
  impl poisson_excess_degree poisson_neutral_R0

sa_fail_forward "DegreeCorrelation.R84-sec" 1 "S1 requires the Poisson second moment, HasSum (fun k => k^2 * e^{-κ} κ^k / k!) (κ^2 + κ). The impl (poisson_excess_degree ∧ poisson_neutral_R0) substitutes ⟨k²⟩ = κ² + κ by hand ((κ^2 + κ - κ)/κ = κ and T * that = T * κ); it never mentions the Poisson pmf or derives its second moment."

/-- `excessDegree ψ` unfolds to `(ψ.secondMoment - ψ.mean) / ψ.mean`; rewriting with the moment
hypotheses gives exactly the conclusion of `poisson_excess_degree`. -/
@[sa_forward "DegreeCorrelation.R84-sec" 2]
theorem fwd2 (h : sa_impl% "DegreeCorrelation.R84-sec") : S2 := by
  intro κ hκ ψ hm hs
  show (ψ.secondMoment - ψ.mean) / ψ.mean = κ
  rw [hs, hm]
  exact h.1 κ hκ

/-- `uncorrelated_R0 Tr ψ` unfolds to `Tr * ((ψ.secondMoment - ψ.mean) / ψ.mean)`; rewriting with
the moment hypotheses gives exactly the conclusion of `poisson_neutral_R0`. -/
@[sa_forward "DegreeCorrelation.R84-sec" 3]
theorem fwd3 (h : sa_impl% "DegreeCorrelation.R84-sec") : S3 := by
  intro Tr κ hκ ψ hm hs
  show Tr * ((ψ.secondMoment - ψ.mean) / ψ.mean) = Tr * κ
  rw [hs, hm]
  exact h.2 Tr κ hκ

/-- Instantiate S2, S3 at the moment data with mean κ and second moment κ² + κ (the proof
arguments of the data term are skipped by the audit). -/
@[sa_backward "DegreeCorrelation.R84-sec"]
theorem bwd (_s1 : S1) (s2 : S2) (s3 : S3) : sa_impl% "DegreeCorrelation.R84-sec" :=
  ⟨fun κ hκ => s2 κ hκ ⟨κ, κ ^ 2 + κ, hκ, add_pos (pow_pos hκ 2) hκ⟩ rfl rfl,
   fun T κ hκ => s3 T κ hκ ⟨κ, κ ^ 2 + κ, hκ, add_pos (pow_pos hκ 2) hκ⟩ rfl rfl⟩

end Alignment.Shadows.DegreeCorrelation.R84_sec

/-! ## `DegreeCorrelation.R84` -/

namespace Alignment.Shadows.DegreeCorrelation.R84

sa_claim "DegreeCorrelation.R84" group "DegreeCorrelation" required
  text "**Result 84.** Poisson excess degree equals the mean."
  impl poisson_excess_degree

@[sa_forward "DegreeCorrelation.R84" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R84") : S1 := by
  intro κ hκ ψ hm hs
  show (ψ.secondMoment - ψ.mean) / ψ.mean = κ
  rw [hs, hm]
  exact h κ hκ

@[sa_backward "DegreeCorrelation.R84"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.R84" :=
  fun κ hκ => s1 κ hκ ⟨κ, κ ^ 2 + κ, hκ, add_pos (pow_pos hκ 2) hκ⟩ rfl rfl

end Alignment.Shadows.DegreeCorrelation.R84

/-! ## `DegreeCorrelation.R84b` -/

namespace Alignment.Shadows.DegreeCorrelation.R84b

sa_claim "DegreeCorrelation.R84b" group "DegreeCorrelation" required
  text "**Result 84b.** For Poisson, R₀ = T·κ."
  impl poisson_neutral_R0

@[sa_forward "DegreeCorrelation.R84b" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R84b") : S1 := by
  intro Tr κ hκ ψ hm hs
  show Tr * ((ψ.secondMoment - ψ.mean) / ψ.mean) = Tr * κ
  rw [hs, hm]
  exact h Tr κ hκ

@[sa_backward "DegreeCorrelation.R84b"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.R84b" :=
  fun T κ hκ => s1 T κ hκ ⟨κ, κ ^ 2 + κ, hκ, add_pos (pow_pos hκ 2) hκ⟩ rfl rfl

end Alignment.Shadows.DegreeCorrelation.R84b

/-! ## `DegreeCorrelation.R85-sec` -/

namespace Alignment.Shadows.DegreeCorrelation.R85_sec

sa_claim "DegreeCorrelation.R85-sec" group "DegreeCorrelation" required
  text "Any valid conditional degree distribution must satisfy: (a) Σ_l Q(l|k) = 1 for all k (normalization) (b) Σ_k k·p_k·Q(l|k) = l·p_l (detailed balance) We verify these for the 2×2 case."
  impl row1_sum_eq_degree row2_sum_eq_degree detailed_balance_col1 detailed_balance_col2

@[sa_forward "DegreeCorrelation.R85-sec" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R85-sec") : S1 :=
  fun d => h.1 d

@[sa_forward "DegreeCorrelation.R85-sec" 2]
theorem fwd2 (h : sa_impl% "DegreeCorrelation.R85-sec") : S2 :=
  fun d => h.2.1 d

@[sa_forward "DegreeCorrelation.R85-sec" 3]
theorem fwd3 (h : sa_impl% "DegreeCorrelation.R85-sec") : S3 :=
  fun d => h.2.2.1 d

@[sa_forward "DegreeCorrelation.R85-sec" 4]
theorem fwd4 (h : sa_impl% "DegreeCorrelation.R85-sec") : S4 :=
  fun d => h.2.2.2 d

@[sa_backward "DegreeCorrelation.R85-sec"]
theorem bwd (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : sa_impl% "DegreeCorrelation.R85-sec" :=
  ⟨fun d => s1 d, fun d => s2 d, fun d => s3 d, fun d => s4 d⟩

end Alignment.Shadows.DegreeCorrelation.R85_sec

/-! ## `DegreeCorrelation.R85a` … `R85d` -/

namespace Alignment.Shadows.DegreeCorrelation.R85a

sa_claim "DegreeCorrelation.R85a" group "DegreeCorrelation" required
  text "**Result 85a.** Row 1 of the mixing matrix sums to k₁ (normalization of Q(·|k₁)): C₁₁ + C₁₂ = k₁."
  impl row1_sum_eq_degree

@[sa_forward "DegreeCorrelation.R85a" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R85a") : S1 :=
  fun d => h d

@[sa_backward "DegreeCorrelation.R85a"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.R85a" :=
  fun d => s1 d

end Alignment.Shadows.DegreeCorrelation.R85a

namespace Alignment.Shadows.DegreeCorrelation.R85b

sa_claim "DegreeCorrelation.R85b" group "DegreeCorrelation" required
  text "**Result 85b.** Row 2 sums to k₂."
  impl row2_sum_eq_degree

@[sa_forward "DegreeCorrelation.R85b" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R85b") : S1 :=
  fun d => h d

@[sa_backward "DegreeCorrelation.R85b"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.R85b" :=
  fun d => s1 d

end Alignment.Shadows.DegreeCorrelation.R85b

namespace Alignment.Shadows.DegreeCorrelation.R85c

sa_claim "DegreeCorrelation.R85c" group "DegreeCorrelation" required
  text "**Result 85c.** Detailed balance column 1: k₁·p₁·Q(1|1) + k₂·p₂·Q(1|2) = k₁·p₁, i.e., p₁·C₁₁ + p₂·C₂₁ = k₁·p₁."
  impl detailed_balance_col1

@[sa_forward "DegreeCorrelation.R85c" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R85c") : S1 :=
  fun d => h d

@[sa_backward "DegreeCorrelation.R85c"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.R85c" :=
  fun d => s1 d

end Alignment.Shadows.DegreeCorrelation.R85c

namespace Alignment.Shadows.DegreeCorrelation.R85d

sa_claim "DegreeCorrelation.R85d" group "DegreeCorrelation" required
  text "**Result 85d.** Detailed balance column 2: p₁·C₁₂ + p₂·C₂₂ = k₂·p₂."
  impl detailed_balance_col2

@[sa_forward "DegreeCorrelation.R85d" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R85d") : S1 :=
  fun d => h d

@[sa_backward "DegreeCorrelation.R85d"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.R85d" :=
  fun d => s1 d

end Alignment.Shadows.DegreeCorrelation.R85d

/-! ## `DegreeCorrelation.R86a` -/

namespace Alignment.Shadows.DegreeCorrelation.R86a

sa_claim "DegreeCorrelation.R86a" group "DegreeCorrelation" required
  text "**Result 86a.** The trace of C decomposes as: tr(C) = k₁·r + k₂·r + (1-r)·(k₁·q₁ + k₂·q₂)."
  impl trace_decomposition

sa_fail_forward "DegreeCorrelation.R86a" 1 "impl (trace_decomposition) states trC = r * (k1 + k2) + (1 - r) * (k1*q1 + k2*q2); S1 (the text's displayed form) is trC = k1 * r + k2 * r + (1 - r) * (k1*q1 + k2*q2). The statements differ in the first summand: equating r * (k1 + k2) with k1 * r + k2 * r needs distributivity and commutativity (mul_add, mul_comm), which are library lemmas; no trusted definition is involved, so no bridge applies."

sa_fail_backward "DegreeCorrelation.R86a" "S1 gives trC = k1 * r + k2 * r + (1 - r) * (k1*q1 + k2*q2); the impl requires trC = r * (k1 + k2) + (1 - r) * (k1*q1 + k2*q2). Converting k1 * r + k2 * r into r * (k1 + k2) needs mul_add / mul_comm (library lemmas); not structural."

end Alignment.Shadows.DegreeCorrelation.R86a

/-! ## `DegreeCorrelation.R86b` -/

namespace Alignment.Shadows.DegreeCorrelation.R86b

sa_claim "DegreeCorrelation.R86b" group "DegreeCorrelation" required
  text "**Result 86b.** The sum k₁·q₁ + k₂·q₂ = ⟨k²⟩/⟨k⟩ (second moment over mean)."
  impl weighted_q_sum

@[sa_forward "DegreeCorrelation.R86b" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R86b") : S1 :=
  fun d => h d

@[sa_backward "DegreeCorrelation.R86b"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.R86b" :=
  fun d => s1 d

end Alignment.Shadows.DegreeCorrelation.R86b

/-! ## `DegreeCorrelation.R86c` -/

namespace Alignment.Shadows.DegreeCorrelation.R86c

sa_claim "DegreeCorrelation.R86c" group "DegreeCorrelation" required
  text "**Result 86c.** Under neutral mixing (r=0), the trace equals ⟨k²⟩/⟨k⟩."
  impl neutral_trace weighted_q_sum

/-- Chain `neutral_trace` (tr C = k₁q₁ + k₂q₂ at r = 0) with `weighted_q_sum`. -/
@[sa_forward "DegreeCorrelation.R86c" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R86c") : S1 :=
  fun d hr => (h.1 d hr).trans (h.2 d)

sa_fail_backward "DegreeCorrelation.R86c" "the impl is stronger than the text: it is neutral_trace (r = 0 → trC = k1*q1 + k2*q2) ∧ weighted_q_sum (k1*q1 + k2*q2 = secondMom/meanDeg for every r). The single shadow S1 (r = 0 → trC = secondMom/meanDeg) does not yield the intermediate form k1*q1 + k2*q2 (neither conjunct follows without weighted_q_sum itself or ring arithmetic on C11 + C22 at r = 0); the text of Result 86c asserts only the trace identity."

end Alignment.Shadows.DegreeCorrelation.R86c

/-! ## `DegreeCorrelation.R86d-1` -/

namespace Alignment.Shadows.DegreeCorrelation.R86d_1

sa_claim "DegreeCorrelation.R86d-1" group "DegreeCorrelation" required
  text "**Result 86d.** Under full assortativity (r=1), the trace equals k₁ + k₂."
  impl fully_assortative_trace

@[sa_forward "DegreeCorrelation.R86d-1" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R86d-1") : S1 :=
  fun d hr => h d hr

@[sa_backward "DegreeCorrelation.R86d-1"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.R86d-1" :=
  fun d hr => s1 d hr

end Alignment.Shadows.DegreeCorrelation.R86d_1

/-! ## `DegreeCorrelation.R86d-2` -/

namespace Alignment.Shadows.DegreeCorrelation.R86d_2

sa_claim "DegreeCorrelation.R86d-2" group "DegreeCorrelation" required
  text "This means each degree class only infects its own kind."
  impl fully_assortative_C12 fully_assortative_C21

@[sa_forward "DegreeCorrelation.R86d-2" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R86d-2") : S1 :=
  fun d hr => h.1 d hr

@[sa_forward "DegreeCorrelation.R86d-2" 2]
theorem fwd2 (h : sa_impl% "DegreeCorrelation.R86d-2") : S2 :=
  fun d hr => h.2 d hr

@[sa_backward "DegreeCorrelation.R86d-2"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "DegreeCorrelation.R86d-2" :=
  ⟨fun d hr => s1 d hr, fun d hr => s2 d hr⟩

end Alignment.Shadows.DegreeCorrelation.R86d_2

/-! ## `DegreeCorrelation.R86e` -/

namespace Alignment.Shadows.DegreeCorrelation.R86e

sa_claim "DegreeCorrelation.R86e" group "DegreeCorrelation" required
  text "**Result 86e.** Under full assortativity (r=1), the off-diagonal entries vanish."
  impl fully_assortative_C12 fully_assortative_C21

@[sa_forward "DegreeCorrelation.R86e" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R86e") : S1 :=
  fun d hr => h.1 d hr

@[sa_forward "DegreeCorrelation.R86e" 2]
theorem fwd2 (h : sa_impl% "DegreeCorrelation.R86e") : S2 :=
  fun d hr => h.2 d hr

@[sa_backward "DegreeCorrelation.R86e"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "DegreeCorrelation.R86e" :=
  ⟨fun d hr => s1 d hr, fun d hr => s2 d hr⟩

end Alignment.Shadows.DegreeCorrelation.R86e

/-! ## `DegreeCorrelation.R86f-1` -/

namespace Alignment.Shadows.DegreeCorrelation.R86f_1

sa_claim "DegreeCorrelation.R86f-1" group "DegreeCorrelation" required
  text "**Result 86f.** Under full assortativity, det(C) = k₁·k₂"
  impl fully_assortative_det

@[sa_forward "DegreeCorrelation.R86f-1" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R86f-1") : S1 :=
  fun d hr => h d hr

@[sa_backward "DegreeCorrelation.R86f-1"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.R86f-1" :=
  fun d hr => s1 d hr

end Alignment.Shadows.DegreeCorrelation.R86f_1

/-! ## `DegreeCorrelation.R86g-1` -/

namespace Alignment.Shadows.DegreeCorrelation.R86g_1

sa_claim "DegreeCorrelation.R86g-1" group "DegreeCorrelation" required
  text "**Result 86g.** Under neutral mixing (r=0), det(C) = 0."
  impl neutral_det_zero

@[sa_forward "DegreeCorrelation.R86g-1" 1]
theorem fwd1 (h : sa_impl% "DegreeCorrelation.R86g-1") : S1 :=
  fun d hr => h d hr

@[sa_backward "DegreeCorrelation.R86g-1"]
theorem bwd (s1 : S1) : sa_impl% "DegreeCorrelation.R86g-1" :=
  fun d hr => s1 d hr

end Alignment.Shadows.DegreeCorrelation.R86g_1

/-! ## `DegreeCorrelation.R86h-1` -/

namespace Alignment.Shadows.DegreeCorrelation.R86h_1

sa_claim "DegreeCorrelation.R86h-1" group "DegreeCorrelation" required
  text "**Result 86h.** Under neutral mixing (r=0), the largest eigenvalue of C equals tr(C) = k₁·q₁ + k₂·q₂ = ⟨k²⟩/⟨k⟩, since the other eigenvalue is 0 (det = 0)."
  impl neutral_largest_eigenvalue neutral_trace weighted_q_sum

sa_fail_forward "DegreeCorrelation.R86h-1" 1 "S1 requires trC to be an eigenvalue of C (Module.End.HasEigenvalue (Matrix.toLin' (Cmat d)) trC) at r = 0. The impl's eigenvalue part (neutral_largest_eigenvalue) only says: every real lam with lam^2 - trC*lam + detC = 0 is 0 or trC (the characteristic equation is a hypothesis). It never asserts that trC is a root, and it has no matrix or eigenvalue notion."

sa_fail_forward "DegreeCorrelation.R86h-1" 2 "S2 requires every eigenvalue of C to be ≤ trC ('largest'). The impl constrains only real roots lam of the scalar equation lam^2 - trC*lam + detC = 0 (to 0 or trC); linking HasEigenvalue of Matrix.toLin' (Cmat d) to that equation needs Mathlib linear-algebra lemmas, and even then the eigenvalue 0 is ≤ trC only if 0 ≤ trC, which the impl does not state (it would come from positivity of k_i, q_i)."

@[sa_forward "DegreeCorrelation.R86h-1" 3]
theorem fwd3 (h : sa_impl% "DegreeCorrelation.R86h-1") : S3 :=
  fun d hr => h.2.1 d hr

/-- Chain `neutral_trace` with `weighted_q_sum`. -/
@[sa_forward "DegreeCorrelation.R86h-1" 4]
theorem fwd4 (h : sa_impl% "DegreeCorrelation.R86h-1") : S4 :=
  fun d hr => (h.2.1 d hr).trans (h.2.2 d)

sa_fail_forward "DegreeCorrelation.R86h-1" 5 "S5 requires 0 to be an eigenvalue of C at r = 0. neutral_largest_eigenvalue only restricts which lam can solve lam^2 - trC*lam + detC = 0 (to 0 or trC); it does not assert that 0 solves it (that needs detC = 0, i.e. neutral_det_zero, not in the impl list) and has no matrix/eigenvalue notion."

sa_fail_forward "DegreeCorrelation.R86h-1" 6 "S6 requires every eigenvalue μ of Matrix.toLin' (Cmat d) to be trC or 0. The impl gives this only for real lam satisfying the scalar characteristic equation lam^2 - trC*lam + detC = 0, supplied as a hypothesis. Deriving that equation from HasEigenvalue (det(C - μI) = 0, the 2x2 characteristic polynomial, trC/detC vs Matrix.trace/det of Cmat d) needs Mathlib lemmas; not structural."

sa_fail_forward "DegreeCorrelation.R86h-1" 7 "S7 requires detC = 0 at r = 0. None of the impls (neutral_largest_eigenvalue, neutral_trace, weighted_q_sum) states it: neutral_det_zero is used inside the proof of neutral_largest_eigenvalue but is not part of its statement nor of the impl list, and 'every root of lam^2 - trC*lam + detC = 0 is 0 or trC' does not imply detC = 0 (it holds vacuously when there are no real roots)."

sa_fail_backward "DegreeCorrelation.R86h-1" "the impl's first conjunct is ∀ d, r = 0 → ∀ lam, lam^2 - trC*lam + detC = 0 → lam = 0 ∨ lam = trC. The shadows speak about Module.End.HasEigenvalue (Matrix.toLin' (Cmat d)) μ; turning the scalar characteristic equation into an eigenvalue of Cmat d (and trC/detC into Matrix.trace/det) needs Mathlib linear-algebra lemmas, so the first conjunct is not derivable structurally. (The other two conjuncts follow from S3, S4.)"

end Alignment.Shadows.DegreeCorrelation.R86h_1

/-! ## `DegreeCorrelation.R86h-2` -/

namespace Alignment.Shadows.DegreeCorrelation.R86h_2

sa_claim "DegreeCorrelation.R86h-2" group "DegreeCorrelation" required
  text "The eigenvalues of a 2×2 matrix with trace τ and det 0 are τ and 0."
  impl neutral_largest_eigenvalue

sa_fail_forward "DegreeCorrelation.R86h-2" 1 "S1 is a general fact about every real 2x2 matrix M with trace τ and det 0 (τ is an eigenvalue). The impl (neutral_largest_eigenvalue) is only about the particular mixing matrix of a TwoDegreeData at r = 0, has no Matrix or eigenvalue notion, and never asserts that τ = trC is a root of lam^2 - trC*lam + detC = 0."

sa_fail_forward "DegreeCorrelation.R86h-2" 2 "S2 (0 is an eigenvalue of every real 2x2 matrix with det 0) is not stated: the impl is only about TwoDegreeData's C at r = 0, has no Matrix/eigenvalue notion, and does not assert that 0 is a root of its characteristic equation."

sa_fail_forward "DegreeCorrelation.R86h-2" 3 "S3 (every eigenvalue of every real 2x2 matrix M with trace τ and det 0 is τ or 0) is more general than the impl, which only covers the mixing matrix of a TwoDegreeData at r = 0 and only real lam satisfying the scalar equation lam^2 - trC*lam + detC = 0 (given as a hypothesis). An arbitrary M is not of the form Cmat d, and linking HasEigenvalue to the characteristic equation needs Mathlib lemmas."

sa_fail_backward "DegreeCorrelation.R86h-2" "the impl is ∀ d, r = 0 → ∀ lam, lam^2 - trC*lam + detC = 0 → lam = 0 ∨ lam = trC. Using S3 at M = Cmat d would need Matrix.trace (Cmat d) = trC and Matrix.det (Cmat d) = 0 (Matrix.trace_fin_two, Matrix.det_fin_two, and neutral_det_zero) and HasEigenvalue from the scalar equation (Mathlib linear algebra); none of this is structural."

end Alignment.Shadows.DegreeCorrelation.R86h_2

/-! ## neutralDetK -/
namespace Alignment.Shadows.DegreeCorrelation.neutralDetK

sa_claim "DegreeCorrelation.neutralDetK" group "DegreeCorrelation" required
  text "Under neutral mixing (r = 0), det K = 0: K has rank one."
  impl neutral_detK

sa_fail_forward "DegreeCorrelation.neutralDetK" 1 "impl neutral_detK states K11·K22 - K12·K21 = 0 at r = 0. S1 states Matrix.det (Kq d) = 0, where det is the Leibniz sum over permutations of Fin 2. It equals the 2×2 formula only by the library lemma Matrix.det_fin_two, and K12 = (k₁-1)(1-r)q₂ differs from the shadow's entry (k₁-1)((1-r)q₂) by mul_assoc. Neither step is structural, and no bridge applies because Matrix.det is not a trusted definition. The mathematical content agrees."

sa_fail_forward "DegreeCorrelation.neutralDetK" 2 "impl gives only the determinant identity K11·K22 - K12·K21 = 0. S2 (Matrix.rank (Kq d) ≤ 1) needs the link between a zero determinant and rank (e.g. Matrix.rank_lt_card_iff_det_eq_zero-type lemmas), which impl does not state."

sa_fail_backward "DegreeCorrelation.neutralDetK" "S1 gives Matrix.det (Kq d) = 0, and impl needs K11·K22 - K12·K21 = 0. Going from one to the other needs Matrix.det_fin_two and mul_assoc (library lemmas, not structural), and there is no trusted definition to bridge."

end Alignment.Shadows.DegreeCorrelation.neutralDetK

/-! ## neutralTraceK -/
namespace Alignment.Shadows.DegreeCorrelation.neutralTraceK

sa_claim "DegreeCorrelation.neutralTraceK" group "DegreeCorrelation" required
  text "Under neutral mixing (r = 0), tr K = ⟨k(k−1)⟩/⟨k⟩."
  impl neutral_traceK

sa_fail_forward "DegreeCorrelation.neutralTraceK" 1 "impl neutral_traceK states K11 + K22 = (k₁(k₁-1)p₁ + k₂(k₂-1)p₂)/meanDeg at r = 0. S1 states Matrix.trace (Kq d) = (p₁k₁(k₁-1) + p₂k₂(k₂-1))/(p₁k₁ + p₂k₂). The trace unfolds to K11 + (K22 + 0), and the right-hand sides differ by the order of the factors (k₁·p₁ against p₁·k₁). Both gaps need add_zero / Matrix.trace_fin_two and mul_comm, which are not structural. Same mathematical content."

sa_fail_backward "DegreeCorrelation.neutralTraceK" "S1 gives the trace of Kq d as (p₁k₁(k₁-1) + p₂k₂(k₂-1))/(p₁k₁ + p₂k₂). impl needs K11 + K22 = (k₁(k₁-1)p₁ + k₂(k₂-1)p₂)/meanDeg. Moving between them needs Matrix.trace_fin_two (or add_zero) and mul_comm/mul_assoc, which are not structural."

end Alignment.Shadows.DegreeCorrelation.neutralTraceK

/-! ## neutralTraceCSubTraceK -/
namespace Alignment.Shadows.DegreeCorrelation.neutralTraceCSubTraceK

sa_claim "DegreeCorrelation.neutralTraceCSubTraceK" group "DegreeCorrelation" required
  text "Under neutral mixing (r = 0), tr C − tr K = 1: the mixing matrix C = k·Q overstates the largest eigenvalue of the next-generation matrix by one."
  impl neutral_traceC_sub_traceK

sa_fail_forward "DegreeCorrelation.neutralTraceCSubTraceK" 1 "impl neutral_traceC_sub_traceK states trC - (K11 + K22) = 1 at r = 0. S1 states trC - Matrix.trace (Kq d) = 1, where the trace unfolds to K11 + (K22 + 0) (with the shadow's K22 entry equal to impl's). x + 0 = x is not definitional in ℝ, so going from impl to S1 needs add_zero / Matrix.trace_fin_two, which is not structural. Same content."

sa_fail_forward "DegreeCorrelation.neutralTraceCSubTraceK" 2 "impl is a trace identity. It says nothing about eigenvalues: S2 (the largest real eigenvalue of C exceeds that of K by one, at r = 0, for k₁, k₂ ≥ 1) needs the rank-one structure of K and C and an eigenvalue argument, none of which impl states. The trace identity alone does not give the largest eigenvalues."

sa_fail_backward "DegreeCorrelation.neutralTraceCSubTraceK" "S1 gives trC - Matrix.trace (Kq d) = 1, and impl needs trC - (K11 + K22) = 1. The trace reduces to K11 + (K22 + 0), and removing + 0 needs add_zero (not structural); no trusted definition to bridge."

end Alignment.Shadows.DegreeCorrelation.neutralTraceCSubTraceK

/-! ## `DegreeCorrelation.R82` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.DegreeCorrelation.R82

sa_claim "DegreeCorrelation.R82" group "DegreeCorrelation"
  text "For a two-degree network with degrees k₁, k₂, degree fractions p₁, p₂, and assortative parameter r ∈ [0,1]: C = [[k₁·(r + (1-r)·q₁), k₁·(1-r)·q₂], [k₂·(1-r)·q₁, k₂·(r + (1-r)·q₂)]] where q_i = k_i·p_i/⟨k⟩ are the excess-degree probabilities. [...] **Result 82.** The four entries of the 2×2 mixing matrix C_{kl} = k·Q(l|k) (not the next-generation matrix; see `TwoDegreeData.K11`)."
  impl

end Alignment.Shadows.DegreeCorrelation.R82

/-! ## `DegreeCorrelation.R86-sec` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.DegreeCorrelation.R86_sec

sa_claim "DegreeCorrelation.R86-sec" group "DegreeCorrelation"
  text "For the 2×2 mixing matrix, the eigenvalues can be expressed via the trace and determinant. These identities concern the mixing matrix C; the spectral R₀ uses K_{kl} = (k-1)·Q(l|k) = C_{kl} - Q(l|k) instead (see the section on K below)."
  impl

end Alignment.Shadows.DegreeCorrelation.R86_sec
