import Alignment.Registry
import Alignment.Shadows.Hierarchy

/-!
# Checkers: group `Hierarchy`

Checker author (SA-PASS role 3, non-blind). For every claim of `EBCMCategory/Hierarchy.lean` with
`status: implemented`, this file holds the `sa_claim` registration (the registry text verbatim,
and the registry `impl` list in registry order), the forward checkers `sa_impl% → Sᵢ`, the backward
checker `S₁ → … → Sₙ → sa_impl%`, and `sa_fail_*` records where a check cannot honestly be proved.

The file declares no bridges. The blind shadows state every claim with the trusted operations
themselves (`levelDim`, `ModelLevel.*`, `PGFData.poisson`, `PGFData.excessDegree`, `PGFData.mean`,
`nodeModel`, `edgeModel`, `EpiModel.R0`). The genuine-PGF shadows (R25 S3, R27 S3, table.R27 S3)
use alignment-local helpers over `ℕ → ℝ`, which no trusted definition corresponds to. So no trusted
definition has to be identified with a differently phrased notion. Every check that holds needs
only the hypothesis, application, `Eq.symm`/`Eq.trans`, anonymous constructors and definitional
unfolding.

Summary:

* Results 23 and 24 (and table rows 23, 24 and the header chain) are faithful. The shadows are the
  implementation statements, up to the order of the header's two conjuncts.
* Result 26 (and row 26) is faithful up to the orientation of the R₀ equation (`Eq.symm`).
* Row 25 claims only "exact for Poisson networks", and the implementation states exactly that.
  Result 25 claims an "iff", but the implementation proves only the Poisson ⇒ exact direction
  (S1). Both converse shadows are recorded as failures.
* Result 27 (and row 27): the implementation assumes excess degree = κ and concludes
  `ψ.variance = κ`. That is neither existence (S1) nor uniqueness (S2, S3), and the conclusion
  `variance = κ` does not follow structurally from the shadows. Every check is recorded as a
  failure.
* Result 28 (and row 28): the implementation asserts only that a mean-κ `PGFData` exists (the
  Poisson one). The R₀ conjunct holds by definition for every ψ. There is no parameterisation or
  injectivity, so the forward check fails. The backward check holds, because the implementation
  is provable outright: witness `PGFData.poisson κ hκ` plus two `rfl`s.
-/

/-! ## header.pairGtEbcmGtMeanField -/
namespace Alignment.Shadows.Hierarchy.header_pairGtEbcmGtMeanField

sa_claim "Hierarchy.header.pairGtEbcmGtMeanField" group "Hierarchy" required
  text "Pair approximation (12N) > EBCM (4) > Mean-field SIR (3)"
  impl edgeBased_lt_pair meanField_lt_edgeBased

@[sa_forward "Hierarchy.header.pairGtEbcmGtMeanField" 1]
theorem fwd1 (h : sa_impl% "Hierarchy.header.pairGtEbcmGtMeanField") : S1 :=
  fun N hN => h.1 N hN

@[sa_forward "Hierarchy.header.pairGtEbcmGtMeanField" 2]
theorem fwd2 (h : sa_impl% "Hierarchy.header.pairGtEbcmGtMeanField") : S2 := fun N => h.2 N

sa_fail_forward "Hierarchy.header.pairGtEbcmGtMeanField" 3 "S3 (levelDim .pairApproximation N = 12N) is the defining clause of levelDim and holds by rfl. impl (edgeBased_lt_pair ∧ meanField_lt_edgeBased) states only the two strict inequalities, not the dimension values, so a checker could only prove S3 without h (vacuous)."

sa_fail_forward "Hierarchy.header.pairGtEbcmGtMeanField" 4 "S4 (levelDim .edgeBased N = 4) is the defining clause of levelDim (rfl). impl states only the inequalities, so a checker could only prove S4 without h (vacuous)."

sa_fail_forward "Hierarchy.header.pairGtEbcmGtMeanField" 5 "S5 (levelDim .meanField N = 3) is the defining clause of levelDim (rfl). impl states only the inequalities, so a checker could only prove S5 without h (vacuous)."

@[sa_backward "Hierarchy.header.pairGtEbcmGtMeanField"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) (_s4 : S4) (_s5 : S5) :
    sa_impl% "Hierarchy.header.pairGtEbcmGtMeanField" :=
  ⟨fun N hN => s1 N hN, fun N => s2 N⟩

end Alignment.Shadows.Hierarchy.header_pairGtEbcmGtMeanField

/-! ## `Hierarchy.table.R23` -/

namespace Alignment.Shadows.Hierarchy.table_R23

sa_claim "Hierarchy.table.R23" group "Hierarchy" required
  text "| 23 | Mean-field < EBCM |"
  impl meanField_lt_edgeBased

/-- S1 is the implementation's statement. -/
@[sa_forward "Hierarchy.table.R23" 1]
theorem fwd1 (h : sa_impl% "Hierarchy.table.R23") : S1 :=
  fun N => h N

@[sa_backward "Hierarchy.table.R23"]
theorem bwd (s1 : S1) : sa_impl% "Hierarchy.table.R23" :=
  fun N => s1 N

end Alignment.Shadows.Hierarchy.table_R23

/-! ## `Hierarchy.table.R24` -/

namespace Alignment.Shadows.Hierarchy.table_R24

sa_claim "Hierarchy.table.R24" group "Hierarchy" required
  text "| 24 | EBCM < Pair approximation (for N ≥ 1) |"
  impl edgeBased_lt_pair

/-- S1 is the implementation's statement. -/
@[sa_forward "Hierarchy.table.R24" 1]
theorem fwd1 (h : sa_impl% "Hierarchy.table.R24") : S1 :=
  fun N hN => h N hN

@[sa_backward "Hierarchy.table.R24"]
theorem bwd (s1 : S1) : sa_impl% "Hierarchy.table.R24" :=
  fun N hN => s1 N hN

end Alignment.Shadows.Hierarchy.table_R24

/-! ## `Hierarchy.table.R25` -/

namespace Alignment.Shadows.Hierarchy.table_R25

sa_claim "Hierarchy.table.R25" group "Hierarchy" required
  text "| 25 | EBCM → Mean-field is exact for Poisson networks |"
  impl ebcm_to_meanfield_exact_iff_poisson

/-- S1 is the implementation's statement. Row 25 claims only the Poisson ⇒ exact direction. -/
@[sa_forward "Hierarchy.table.R25" 1]
theorem fwd1 (h : sa_impl% "Hierarchy.table.R25") : S1 :=
  fun κ hκ => h κ hκ

@[sa_backward "Hierarchy.table.R25"]
theorem bwd (s1 : S1) : sa_impl% "Hierarchy.table.R25" :=
  fun κ hκ => s1 κ hκ

end Alignment.Shadows.Hierarchy.table_R25

/-! ## `Hierarchy.table.R26` -/

namespace Alignment.Shadows.Hierarchy.table_R26

sa_claim "Hierarchy.table.R26" group "Hierarchy" required
  text "| 26 | Every node model has a canonical Poisson lift |"
  impl node_lifts_to_edge

/-- The implementation states `(nodeModel p κ).R0 = (edgeModel p (poisson κ hκ)).R0`, and S1 is the
same equation reversed. -/
@[sa_forward "Hierarchy.table.R26" 1]
theorem fwd1 (h : sa_impl% "Hierarchy.table.R26") : S1 :=
  fun p κ hκ => (h p κ hκ).symm

@[sa_backward "Hierarchy.table.R26"]
theorem bwd (s1 : S1) : sa_impl% "Hierarchy.table.R26" :=
  fun p κ hκ => (s1 p κ hκ).symm

end Alignment.Shadows.Hierarchy.table_R26

/-! ## table.R27 -/
namespace Alignment.Shadows.Hierarchy.table_R27

sa_claim "Hierarchy.table.R27" group "Hierarchy" required
  text "| 27 | Excess = mean forces variance = mean (records only) |"
  impl poisson_unique_exact_lift

sa_fail_forward "Hierarchy.table.R27" 1 "impl poisson_unique_exact_lift takes an explicit hypothesis 0 < κ (unused in its proof). Instantiating κ := ψ.mean needs 0 < ψ.mean, which only the data invariant PGFData.mean_pos provides, and a structural checker may not project a proof out of a record. So S1 does not follow structurally from h. Mathematically it follows from impl plus mean_pos; remediation: drop the redundant hypothesis, or state the theorem for records."

@[sa_backward "Hierarchy.table.R27"]
theorem bwd (s1 : S1) : sa_impl% "Hierarchy.table.R27" :=
  fun _κ _hκ ψ hm he => (s1 ψ (he.trans hm.symm)).trans hm

end Alignment.Shadows.Hierarchy.table_R27

/-! ## table.R28

The implementation is existential; the backward checker uses the Poisson record of S1 as the
witness and S4 at `κ := ψ''(1)/ψ'(1)` for the R₀ equation (both sides unfold to
`T·excessDegree`). -/
namespace Alignment.Shadows.Hierarchy.table_R28

sa_claim "Hierarchy.table.R28" group "Hierarchy" required
  text "| 28 | A Poisson-record lift exists; R₀ kept iff excess = κ |"
  impl lift_space_parameterised

sa_fail_forward "Hierarchy.table.R28" 1 "S1 ((poisson κ).mean = κ) holds by rfl. impl lift_space_parameterised is existential (∃ ψ, ψ.mean = κ ∧ …) and does not name the Poisson record, so a checker could only prove S1 without h (vacuous)."

sa_fail_forward "Hierarchy.table.R28" 2 "impl gives, for some record ψ of mean κ, edge R₀ = T·excessDegree ψ. S2 says the Poisson record's edge R₀ equals the node R₀ T·κ, i.e. T·(κ²/κ) = T·κ. impl's existential does not identify ψ as the Poisson record, and κ²/κ = κ needs field cancellation, not structural. The text attributes the iff to edge_lift_R0_eq_iff, which is not in impl."

sa_fail_forward "Hierarchy.table.R28" 3 "S3 (edge R₀ = node R₀ at κ ⇒ excess = κ) is the forward direction of edge_lift_R0_eq_iff, which is not in this claim's impl list. impl lift_space_parameterised (∃ ψ with mean κ and edge R₀ = T·excess) does not state it; it needs cancellation of T > 0."

sa_fail_forward "Hierarchy.table.R28" 4 "S4 (excess = κ ⇒ edge R₀ = node R₀ at κ) is the reverse direction of edge_lift_R0_eq_iff, which is not in impl. It holds by rewriting with the hypothesis in the definitions (T·excess = T·κ), so a checker could only prove it without h (vacuous)."

@[sa_backward "Hierarchy.table.R28"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (s4 : S4) : sa_impl% "Hierarchy.table.R28" :=
  fun p κ hκ => ⟨PGFData.poisson κ hκ, s1 κ hκ,
    s4 p (PGFData.poisson κ hκ) (PGFData.poisson κ hκ).excessDegree rfl⟩

end Alignment.Shadows.Hierarchy.table_R28

/-! ## `Hierarchy.R23` -/

namespace Alignment.Shadows.Hierarchy.R23

sa_claim "Hierarchy.R23" group "Hierarchy" required
  text "**Result 23.** Mean-field has fewer variables than EBCM."
  impl meanField_lt_edgeBased

/-- S1 is the implementation's statement. -/
@[sa_forward "Hierarchy.R23" 1]
theorem fwd1 (h : sa_impl% "Hierarchy.R23") : S1 :=
  fun N => h N

@[sa_backward "Hierarchy.R23"]
theorem bwd (s1 : S1) : sa_impl% "Hierarchy.R23" :=
  fun N => s1 N

end Alignment.Shadows.Hierarchy.R23

/-! ## `Hierarchy.R24` -/

namespace Alignment.Shadows.Hierarchy.R24

sa_claim "Hierarchy.R24" group "Hierarchy" required
  text "**Result 24.** EBCM has fewer variables than pair approximation for N ≥ 1."
  impl edgeBased_lt_pair

/-- S1 is the implementation's statement. -/
@[sa_forward "Hierarchy.R24" 1]
theorem fwd1 (h : sa_impl% "Hierarchy.R24") : S1 :=
  fun N hN => h N hN

@[sa_backward "Hierarchy.R24"]
theorem bwd (s1 : S1) : sa_impl% "Hierarchy.R24" :=
  fun N hN => s1 N hN

end Alignment.Shadows.Hierarchy.R24

/-! ## `Hierarchy.R25` -/

namespace Alignment.Shadows.Hierarchy.R25

sa_claim "Hierarchy.R25" group "Hierarchy" required
  text "**Result 25.** The EBCM → Mean-field step is exact iff Poisson."
  impl ebcm_to_meanfield_exact_iff_poisson

/-- S1 (Poisson ⇒ exact) is the implementation's statement. -/
@[sa_forward "Hierarchy.R25" 1]
theorem fwd1 (h : sa_impl% "Hierarchy.R25") : S1 :=
  fun κ hκ => h κ hκ

sa_fail_forward "Hierarchy.R25" 2 "impl (ebcm_to_meanfield_exact_iff_poisson) is only ∀ κ hκ, (PGFData.poisson κ hκ).excessDegree = (PGFData.poisson κ hκ).mean, the Poisson ⇒ exact direction (a restatement of EpiCategory Result 1). Despite its name there is no converse and no biconditional. S2 (exact ⇒ Poisson over PGFData: ∀ ψ, ψ.excessDegree = ψ.mean → ψ = PGFData.poisson ψ.mean ψ.mean_pos) quantifies over arbitrary ψ, while impl speaks only of Poisson records. S2 is true within the two-moment record (ψ.secondFactorial / ψ.mean = ψ.mean ⇒ ψ.secondFactorial = ψ.mean²), but impl does not state it. Any proof would need field arithmetic and PGFData extensionality and would ignore h (vacuous). The 'iff' of the text is only half implemented."
sa_fail_forward "Hierarchy.R25" 3 "impl states only the Poisson ⇒ exact direction for PGFData.poisson records. S3 (exact ⇒ Poisson over genuine degree distributions p : ℕ → ℝ: excess degree = mean ⇒ p k = e^{-mean} mean^k / k!) is a converse over a different domain that impl never mentions. S3 is also mathematically FALSE under the static reading of 'exact' as excess degree = mean. Counterexample: p0 = 1/3, p1 = 1/2, p3 = 1/6 (mean 1, ψ''(1) = 1, excess degree 1 = mean, not Poisson). So no correct impl can meet it. This is not a shadow misreading: the shadow reads 'exact' as the condition that Result 27 calls 'the exactness condition' and keeps the text's unrestricted 'iff Poisson'. Under a dynamical reading (EBCM trajectories reduce to mean-field SIR), which the vocabulary cannot express, the converse would plausibly hold."

/-- The implementation is literally S1. -/
@[sa_backward "Hierarchy.R25"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "Hierarchy.R25" :=
  fun κ hκ => s1 κ hκ

end Alignment.Shadows.Hierarchy.R25

/-! ## `Hierarchy.R26` -/

namespace Alignment.Shadows.Hierarchy.R26

sa_claim "Hierarchy.R26" group "Hierarchy" required
  text "**Result 26.** Every node model lifts to an edge model via Poisson, preserving R₀."
  impl node_lifts_to_edge

/-- The implementation states `(nodeModel p κ).R0 = (edgeModel p (poisson κ hκ)).R0`, and S1 is the
same equation reversed. -/
@[sa_forward "Hierarchy.R26" 1]
theorem fwd1 (h : sa_impl% "Hierarchy.R26") : S1 :=
  fun p κ hκ => (h p κ hκ).symm

@[sa_backward "Hierarchy.R26"]
theorem bwd (s1 : S1) : sa_impl% "Hierarchy.R26" :=
  fun p κ hκ => (s1 p κ hκ).symm

end Alignment.Shadows.Hierarchy.R26

/-! ## R27 -/
namespace Alignment.Shadows.Hierarchy.R27

sa_claim "Hierarchy.R27" group "Hierarchy" required
  text "**Result 27.** For a two-moment record with mean κ, excess degree = mean forces variance = mean, so the record is the Poisson record `poisson κ` (`PGFData.dispersionIndex_eq_one_iff`). This does not make Poisson the unique degree distribution with excess degree = mean: ψ(u) = (1 + u²)/2 has ψ''(1)/ψ'(1) = 1 = ψ'(1) and is not Poisson."
  impl poisson_unique_exact_lift

sa_fail_forward "Hierarchy.R27" 1 "impl poisson_unique_exact_lift takes an explicit hypothesis 0 < κ (unused in its proof). Instantiating κ := ψ.mean needs 0 < ψ.mean, which only the data invariant PGFData.mean_pos provides, and a structural checker may not project a proof out of a record. So S1 does not follow structurally from h. Mathematically it follows from impl plus mean_pos."

sa_fail_forward "Hierarchy.R27" 2 "impl concludes only variance = κ. S2 (the record equals PGFData.poisson ψ.mean) needs ψ''(1) = ψ'(1)² from variance = mean (ring arithmetic) and record extensionality over PGFData, a structure with proof fields, whose eliminator a structural checker may not use. The text cites PGFData.dispersionIndex_eq_one_iff for this step, which is not in impl."

sa_fail_forward "Hierarchy.R27" 3 "impl is about two-moment records. It says nothing about the real PGF ψ(u) = (1 + u²)/2 or its derivatives (S3: ψ''(1)/ψ'(1) = 1)."

sa_fail_forward "Hierarchy.R27" 4 "impl says nothing about the real PGF ψ(u) = (1 + u²)/2 (S4: ψ'(1) = 1)."

sa_fail_forward "Hierarchy.R27" 5 "impl says nothing about the real PGF ψ(u) = (1 + u²)/2 being non-Poisson (S5: ψ ≠ exp(λ(u − 1)) for every λ). The text's caveat is not formalised in impl."

@[sa_backward "Hierarchy.R27"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) (_s5 : S5) : sa_impl% "Hierarchy.R27" :=
  fun _κ _hκ ψ hm he => (s1 ψ (he.trans hm.symm)).trans hm

end Alignment.Shadows.Hierarchy.R27

/-! ## R28 (the backward checker uses the Poisson record of S1/S2 as the existential witness) -/
namespace Alignment.Shadows.Hierarchy.R28

sa_claim "Hierarchy.R28" group "Hierarchy" required
  text "**Result 28.** Some PGF record with mean κ (the Poisson record) gives an edge model with R₀ = T·ψ''(1)/ψ'(1). Matching the mean does not preserve R₀: the edge model of a record ψ has the node model's R₀ T·κ iff ψ''(1)/ψ'(1) = κ (`edge_lift_R0_eq_iff`)."
  impl lift_space_parameterised

sa_fail_forward "Hierarchy.R28" 1 "S1 ((poisson κ).mean = κ) holds by rfl. impl lift_space_parameterised is existential and does not name the Poisson record, so a checker could only prove S1 without h (vacuous)."

sa_fail_forward "Hierarchy.R28" 2 "S2 (the Poisson record's edge R₀ is T·ψ''(1)/ψ'(1)) holds by unfolding edgeModel (rfl). impl's existential does not name the Poisson record, so a checker could only prove S2 without h (vacuous)."

sa_fail_forward "Hierarchy.R28" 3 "impl gives the existence of a record whose edge R₀ is T·excess. It does not give S3 (some p, ψ with edge R₀ ≠ node R₀ at ψ'(1)), which needs a non-Poisson record and the arithmetic T·e ≠ T·κ."

sa_fail_forward "Hierarchy.R28" 4 "S4 ((nodeModel p κ).R0 = T·κ) is the definition of nodeModel (rfl). impl does not state it, so a checker could only prove it without h (vacuous)."

sa_fail_forward "Hierarchy.R28" 5 "S5 (equal R₀ ⇒ ψ''(1)/ψ'(1) = κ) is the forward direction of edge_lift_R0_eq_iff, which is not in this claim's impl list. impl (an existential about the Poisson record) does not state it, and it needs cancellation of T > 0."

sa_fail_forward "Hierarchy.R28" 6 "S6 (ψ''(1)/ψ'(1) = κ ⇒ equal R₀) is the reverse direction of edge_lift_R0_eq_iff (not in impl). It holds by rewriting with the hypothesis in the definitions, so a checker could only prove it without h (vacuous)."

@[sa_backward "Hierarchy.R28"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) (_s4 : S4) (_s5 : S5) (_s6 : S6) :
    sa_impl% "Hierarchy.R28" :=
  fun p κ hκ => ⟨PGFData.poisson κ hκ, s1 κ hκ, s2 p κ hκ⟩

end Alignment.Shadows.Hierarchy.R28

/-! ## edgeLiftR0EqIff (`ψ.excessDegree` unfolds to `ψ''(1)/ψ'(1)`) -/
namespace Alignment.Shadows.Hierarchy.edgeLiftR0EqIff

sa_claim "Hierarchy.edgeLiftR0EqIff" group "Hierarchy" required
  text "The edge model of a record ψ has the R₀ of the node model with mean degree κ iff ψ''(1)/ψ'(1) = κ."
  impl edge_lift_R0_eq_iff

@[sa_forward "Hierarchy.edgeLiftR0EqIff" 1]
theorem fwd1 (h : sa_impl% "Hierarchy.edgeLiftR0EqIff") : S1 := fun p ψ κ => (h p κ ψ).mp

@[sa_forward "Hierarchy.edgeLiftR0EqIff" 2]
theorem fwd2 (h : sa_impl% "Hierarchy.edgeLiftR0EqIff") : S2 := fun p ψ κ => (h p κ ψ).mpr

@[sa_backward "Hierarchy.edgeLiftR0EqIff"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "Hierarchy.edgeLiftR0EqIff" :=
  fun p κ ψ => ⟨s1 p ψ κ, s2 p ψ κ⟩

end Alignment.Shadows.Hierarchy.edgeLiftR0EqIff

/-! ## pairLtFull -/
namespace Alignment.Shadows.Hierarchy.pairLtFull

sa_claim "Hierarchy.pairLtFull" group "Hierarchy" required
  text "The pair approximation has fewer variables than the full stochastic model for N ≥ 4: 12N < 3^N."
  impl pair_lt_full

@[sa_forward "Hierarchy.pairLtFull" 1]
theorem fwd1 (h : sa_impl% "Hierarchy.pairLtFull") : S1 := fun N hN => h N hN

sa_fail_forward "Hierarchy.pairLtFull" 2 "S2 (levelDim .pairApproximation N = 12N) is the defining clause of levelDim (rfl). impl pair_lt_full states only 12N < 3^N for N ≥ 4, so a checker could only prove S2 without h (vacuous)."

sa_fail_forward "Hierarchy.pairLtFull" 3 "S3 (levelDim .fullStochastic N = 3^N) is the defining clause of levelDim (rfl). impl states only the inequality, so a checker could only prove S3 without h (vacuous)."

@[sa_backward "Hierarchy.pairLtFull"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "Hierarchy.pairLtFull" :=
  fun N hN => s1 N hN

end Alignment.Shadows.Hierarchy.pairLtFull

/-! ## fullLtPairThree -/
namespace Alignment.Shadows.Hierarchy.fullLtPairThree

sa_claim "Hierarchy.fullLtPairThree" group "Hierarchy" required
  text "For N = 3 the full stochastic model has fewer variables than the pair approximation: 3³ = 27 < 36 = 12·3."
  impl full_lt_pair_three

@[sa_forward "Hierarchy.fullLtPairThree" 1]
theorem fwd1 (h : sa_impl% "Hierarchy.fullLtPairThree") : S1 := h

sa_fail_forward "Hierarchy.fullLtPairThree" 2 "S2 (levelDim .fullStochastic 3 = 27) holds by rfl (3³ evaluates to 27). impl full_lt_pair_three states only the inequality, so a checker could only prove S2 without h (vacuous)."

sa_fail_forward "Hierarchy.fullLtPairThree" 3 "S3 (levelDim .pairApproximation 3 = 36) holds by rfl (12·3 evaluates to 36). impl states only the inequality, so a checker could only prove S3 without h (vacuous)."

@[sa_backward "Hierarchy.fullLtPairThree"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "Hierarchy.fullLtPairThree" := s1

end Alignment.Shadows.Hierarchy.fullLtPairThree

/-! ## `Hierarchy.header.fullGtPair` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Hierarchy.header_fullGtPair

sa_claim "Hierarchy.header.fullGtPair" group "Hierarchy"
  text "Epidemic models are compared here by the state-space dimension of an N-node SIR network model (`levelDim`): Full stochastic (3^N) > Pair approximation (12N) [...] The first inequality holds only for N ≥ 4 (`pair_lt_full`); for N = 3, 3³ = 27 < 36 = 12·3 (`full_lt_pair_three`)."
  impl

end Alignment.Shadows.Hierarchy.header_fullGtPair
