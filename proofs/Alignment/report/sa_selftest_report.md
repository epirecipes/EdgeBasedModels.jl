# SA-PASS report (self-test)

Generated 2026-09-26 18:44 from `Alignment/report/sa_pass_audit.json` (Lean 4.29.0-rc4) and `Alignment/Example/claims_example.yaml`, `Alignment/Example/claims_selftest.yaml`.

Trusted modules loaded by the audit: `EBCMCategory.CategoricalComposition`, `EBCMCategory.ClosureTheorem`, `EBCMCategory.ClusteringExtension`, `EBCMCategory.CoarseGrain`, `EBCMCategory.ConvergenceTheorems`, `EBCMCategory.DegreeCorrelation`, `EBCMCategory.DynamicLimits`, `EBCMCategory.EpiCategory`, `EBCMCategory.GaloisPair`, `EBCMCategory.Hierarchy`, `EBCMCategory.InvariantRegion`, `EBCMCategory.MarginalisationCharacterization`, `EBCMCategory.MarginalisationDynamicalGap`, `EBCMCategory.MarginalisationFunctor`, `EBCMCategory.MessagePassingBridge`, `EBCMCategory.MethodOfStages`, `EBCMCategory.Obstructions`, `EBCMCategory.PairwiseClosureConditions`, `EBCMCategory.SEIREquations`, `EBCMCategory.SurvivalBridge`, `EBCMCategory.VolzMeyersEquations`

Tool sanity: 3/3 worked-example claims (`EXAMPLE.*`) pass every check (run `bash scripts/sa_pass.sh --self-test` for the full self-test).

## Summary

| quantity | value |
|---|---|
| claims in registry | 53 |
| claims registered in Lean | 54 |
| registry claims not registered in Lean | 0 |
| required claims (status implemented) | 52 |
| SA-PASS = 1 (all / required) | 5 / 5 |
| mean SA-PASS_soft (registered claims) | 0.1343 |
| required failures | 47 |
| check statuses | audit_violation: 15, fail: 2, missing: 54, pass: 29, sorry: 1, vacuous: 11 |
| bridges | invalid: 4, rejected: 1, reviewed: 1, stale: 1, unreviewed: 2 |
| hints (not scored) | backward_unused_shadows: 2, witness_missing: 2 |
| trusted-free shadows (by review status) | reviewed: 1, stale: 1, unreviewed: 2 |
| tautological shadows (by review status) | unreviewed: 1 |
| claims with a refuted implementation hypothesis | 1 |

## Per group

| group | registry | registered | required | SA-PASS=1 | mean soft | forward pass | backward pass | required failures |
|---|---|---|---|---|---|---|---|---|
| Example | 3 | 3 | 3 | 3 | 1.0 | 5/5 | 3/3 | 0 |
| Other | 1 | 1 | 1 | 0 | 0.0 | 0/1 | 0/1 | 1 |
| SelfTest | 49 | 50 | 48 | 2 | 0.085 | 12/52 | 9/50 | 46 |

## Claims

| id | req | n | forward | backward | SA-PASS | soft | flags |
|---|---|---|---|---|---|---|---|
| `EXAMPLE.poissonVariance` | yes | 2 | pass pass | pass | 1 | 1.0 |  (hints: backward_unused_shadows) |
| `EXAMPLE.trajectoryGapZero` | yes | 1 | pass | pass | 1 | 1.0 |  |
| `EXAMPLE.transmissibilityRange` | yes | 2 | pass pass | pass | 1 | 1.0 |  |
| `SELFTEST.groupMismatch` | yes | 1 | missing | missing | 0 | 0.0 | group_mismatch |
| `SELFTEST.automationOmega` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.automationRing` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.automationSimp` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.backwardBudget` | yes | 1 | pass | audit_violation | 0 | 0.5 |  |
| `SELFTEST.backwardVacuous` | yes | 1 | pass | vacuous | 0 | 0.5 |  |
| `SELFTEST.backwardVacuousEval` | yes | 1 | pass | vacuous | 0 | 0.5 |  |
| `SELFTEST.bad id!` | yes | 1 | missing | missing | 0 | 0.0 | invalid_id |
| `SELFTEST.decideCheck` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.duplicate` | yes | 1 | missing | missing | 0 | 0.0 | duplicate |
| `SELFTEST.forgedReview` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.gap` | no | 1 | missing | missing | 0 | 0.0 | gap |
| `SELFTEST.helperAutomation` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.implInBackward` | yes | 1 | missing | audit_violation | 0 | 0.0 |  |
| `SELFTEST.implMismatch` | yes | 1 | missing | missing | 0 | 0.0 | impl_mismatch |
| `SELFTEST.implUnsound` | yes | 1 | missing | missing | 0 | 0.0 | impl_unsound, impl_untrusted |
| `SELFTEST.implUntrusted` | yes | 1 | missing | missing | 0 | 0.0 | impl_untrusted |
| `SELFTEST.impossibilityImpl` | yes | 1 | pass | pass | 0 | 0.0 | impl_untrusted (identical to impl: [0, 1]) |
| `SELFTEST.incompleteShadows` | yes | 1 | pass | pass | 0 | 0.0 | incomplete |
| `SELFTEST.invalidBridges` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.launderingBridge` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.mismatch` | yes | 1 | fail | missing | 0 | 0.0 |  |
| `SELFTEST.missingCheck` | yes | 2 | pass missing | pass | 0 | 0.75 |  (hints: backward_unused_shadows) |
| `SELFTEST.outOfScopeBridge` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.proofField` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.recordedFail` | yes | 1 | fail | missing | 0 | 0.0 |  |
| `SELFTEST.refutedHypothesis` | yes | 1 | pass | pass | 0 | 0.0 | hypothesis_refuted |
| `SELFTEST.rejectedBridge` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.requiredMismatch` | no | 1 | missing | missing | 0 | 0.0 | required_mismatch |
| `SELFTEST.shadowReuse` | yes | 2 | missing missing | missing | 0 | 0.0 | shadow_mismatch |
| `SELFTEST.sorryCheck` | yes | 1 | sorry | missing | 0 | 0.0 |  (identical to impl: [0, 1]) |
| `SELFTEST.staleBridge` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.tautologyShadow` | yes | 1 | missing | missing | 0 | 0.0 | shadow_tautology |
| `SELFTEST.textMismatch` | yes | 1 | missing | missing | 0 | 0.0 | text_mismatch |
| `SELFTEST.trustedFreeReviewed` | yes | 1 | pass | pass | 1 | 1.0 |  (identical to impl: [0, 1]) |
| `SELFTEST.trustedFreeShadow` | yes | 1 | pass | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [0, 1]) |
| `SELFTEST.trustedFreeStale` | yes | 1 | pass | pass | 0 | 0.0 | shadow_trusted_free (identical to impl: [0, 1]) |
| `SELFTEST.unlisted` | yes | 1 | missing | missing | 0 | 0.0 | unlisted |
| `SELFTEST.unreviewedBridge` | yes | 1 | audit_violation | missing | 0 | 0.0 |  |
| `SELFTEST.unusedBinderShadow` | yes | 1 | missing | missing | 0 | 0.0 | shadow_trusted_free |
| `SELFTEST.vacuousAndLeft` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousAuxLemma` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousBeta` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousConst` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousDataArg` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousEval` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousExistsElim` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousIgnore` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.vacuousMatch` | yes | 1 | vacuous | missing | 0 | 0.0 |  |
| `SELFTEST.witnessInvalid` | yes | 1 | pass | pass | 0 | 0.0 | witness_invalid (hints: witness_missing) |
| `SELFTEST.witnessMissing` | yes | 1 | pass | pass | 1 | 1.0 |  (hints: witness_missing) |

## Required failures

* `SELFTEST.vacuousIgnore`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousBeta`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousAndLeft`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousAuxLemma`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousEval`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousConst`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousMatch`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousExistsElim`: forward 1: vacuous; backward: missing
* `SELFTEST.vacuousDataArg`: forward 1: vacuous; backward: missing
* `SELFTEST.automationSimp`: forward 1: audit_violation; backward: missing
* `SELFTEST.automationRing`: forward 1: audit_violation; backward: missing
* `SELFTEST.automationOmega`: forward 1: audit_violation; backward: missing
* `SELFTEST.helperAutomation`: forward 1: audit_violation; backward: missing
* `SELFTEST.proofField`: forward 1: audit_violation; backward: missing
* `SELFTEST.decideCheck`: forward 1: audit_violation; backward: missing
* `SELFTEST.implInBackward`: forward 1: missing; backward: audit_violation
* `SELFTEST.unreviewedBridge`: forward 1: audit_violation; backward: missing
* `SELFTEST.staleBridge`: forward 1: audit_violation; backward: missing
* `SELFTEST.launderingBridge`: forward 1: audit_violation; backward: missing
* `SELFTEST.rejectedBridge`: forward 1: audit_violation; backward: missing
* `SELFTEST.forgedReview`: forward 1: audit_violation; backward: missing
* `SELFTEST.outOfScopeBridge`: forward 1: audit_violation; backward: missing
* `SELFTEST.invalidBridges`: forward 1: audit_violation; backward: missing
* `SELFTEST.mismatch`: forward 1: fail; backward: missing
* `SELFTEST.sorryCheck`: forward 1: sorry; backward: missing
* `SELFTEST.missingCheck`: forward 2: missing
* `SELFTEST.incompleteShadows`: incomplete: no sa_complete
* `SELFTEST.recordedFail`: forward 1: fail; backward: missing
* `SELFTEST.trustedFreeShadow`: shadow_trusted_free: S1 (Alignment.Example.SelfTest.TrustedFreeShadow.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 5540191272585265229; review: unreviewed)
* `SELFTEST.trustedFreeStale`: shadow_trusted_free: S1 (Alignment.Example.SelfTest.TrustedFreeStale.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 16278705499424709584; review: stale)
* `SELFTEST.unusedBinderShadow`: shadow_trusted_free: S1 (Alignment.Example.SelfTest.UnusedBinderShadow.S1) mentions no trusted-library constant after inlining alignment helpers, except in the domains of unused binders (content hash 11480590810223777499; review: unreviewed); forward 1: missing; backward: missing
* `SELFTEST.tautologyShadow`: shadow_tautology: S1 (Alignment.Example.SelfTest.TautologyShadow.S1) holds by reflexivity or assumption at reducible transparency after inlining alignment helpers (content hash 15835174516839732522; review: unreviewed); forward 1: missing; backward: missing
* `SELFTEST.refutedHypothesis`: hypothesis_refuted: EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_rate_two_at_witness: hypothesis h₃ : EBCMCategory.Marginalisation.IsFlow EBCMCategory.MarginalisationDynamicalGap.F3Kℝ φ₃ refuted by EBCMCategory.MarginalisationDynamicalGap.no_flow_F3Kℝ (trusted); EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_rate_two_at_witness: hypothesis h₃ : EBCMCategory.Marginalisation.IsFlow EBCMCategory.MarginalisationDynamicalGap.F3Kℝ φ₃ refuted by Alignment.Example.SelfTest.AlignmentRefuter.refuter (alignment)
* `SELFTEST.witnessInvalid`: witness_invalid: Alignment.Example.SelfTest.WitnessInvalid.witness: statement is not `∃ x₁ … xₖ, True` over the binders of EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_at_zero up to its last hypothesis
* `SELFTEST.impossibilityImpl`: impl_untrusted: Alignment.Example.SelfTest.ImpossibilityImpl.noFlow is declared in Alignment.Example.SelfTest, not in the trusted library
* `SELFTEST.backwardVacuous`: backward: vacuous
* `SELFTEST.backwardVacuousEval`: backward: vacuous
* `SELFTEST.backwardBudget`: backward: audit_violation
* `SELFTEST.implUntrusted`: impl_untrusted: Nat.le_refl is declared in Init.Prelude, not in the trusted library; forward 1: missing; backward: missing
* `SELFTEST.implUnsound`: impl_untrusted: Alignment.Example.SelfTest.ImplUnsound.unsoundImpl is declared in Alignment.Example.SelfTest, not in the trusted library; impl_unsound: Alignment.Example.SelfTest.ImplUnsound.unsoundImpl depends on [sorryAx]; forward 1: missing; backward: missing
* `SELFTEST.duplicate`: duplicate: sa_claim registered 2 times; forward 1: missing; backward: missing
* `SELFTEST.bad id!`: invalid_id: "SELFTEST.bad id!" does not match [A-Za-z0-9._-]+; registry id does not match [A-Za-z0-9._-]+; forward 1: missing; backward: missing
* `SELFTEST.unlisted`: unlisted: not in the claims registry; forward 1: missing; backward: missing
* `SELFTEST.textMismatch`: text_mismatch: sa_claim text differs from the registry text; forward 1: missing; backward: missing
* `SELFTEST.groupMismatch`: group_mismatch: registry `Other` vs Lean `SelfTest`; forward 1: missing; backward: missing
* `SELFTEST.implMismatch`: impl_mismatch: registry ['PGFData.poisson_excess_eq_mean'] vs Lean ['PGFData.poisson_variance_eq_mean']; forward 1: missing; backward: missing
* `SELFTEST.shadowReuse`: shadow_mismatch: Alignment.Example.SelfTest.ShadowReuse.S is registered more than once as a shadow/reference; Alignment.Example.SelfTest.ShadowReuse.S is registered more than once as a shadow/reference; forward 1: missing; forward 2: missing; backward: missing

## Bridges

| bridge | claims | status | hash | statement | notes |
|---|---|---|---|---|---|
| `Alignment.Example.SelfTest.InvalidBridges.closedConj` | SELFTEST.invalidBridges | invalid | `16262042253474658934` | `∀ (s : EBCMCategory.Marginalisation.MotifShape), s.isOrder3 ↔ s.order = 3 ∧ 1 = 1` | closed conjunct on the right-hand side |
| `Alignment.Example.SelfTest.InvalidBridges.closedRhs` | SELFTEST.invalidBridges | invalid | `8616183590909859395` | `PGFData.excessDegree = PGFData.excessDegree` | closed right-hand side (mentions no bound variable) |
| `Alignment.Example.SelfTest.InvalidBridges.natHead` | SELFTEST.invalidBridges | invalid | `6039523524133956966` | `∀ (n : ℕ), n.succ = n + 1` | left-hand side head Nat.succ is not a definition of the trusted library |
| `Alignment.Example.SelfTest.LaunderingBridge.bridge` | SELFTEST.launderingBridge | invalid | `16481377043707351972` | `∀ (ψ : PGFData), ψ.variance = ψ.secondFactorial + ψ.mean * (1 - ψ.mean)` | depends on implementation theorem PGFData.poisson_variance_eq_mean (via Alignment.Example.SelfTest.LaunderingBridge.bridge → PGFData.poisson_variance_eq_mean) |
| `Alignment.Example.SelfTest.RejectedBridge.bridge` | SELFTEST.rejectedBridge | rejected | `16481377043707351972` | `∀ (ψ : PGFData), ψ.variance = ψ.secondFactorial + ψ.mean * (1 - ψ.mean)` | SELFTEST: rejected bridge |
| `Alignment.Example.PoissonVariance.bridge_variance` | EXAMPLE.poissonVariance | reviewed | `16481377043707351972` | `∀ (ψ : PGFData), ψ.variance = ψ.secondFactorial + ψ.mean * (1 - ψ.mean)` | EpiCategory.lean (PGFData.variance docstring): Var(k) = ψ''(1) + ψ'(1) − (ψ'(1))²; the RHS   ψ''(1) + ψ'(1)(1 − ψ'(1)) is the same polynomial in the PGF data, with no side condition |
| `Alignment.Example.SelfTest.StaleBridge.bridge` | SELFTEST.staleBridge | stale | `16481377043707351972` | `∀ (ψ : PGFData), ψ.variance = ψ.secondFactorial + ψ.mean * (1 - ψ.mean)` | review hash 0 does not match 16481377043707351972 |
| `Alignment.Example.SelfTest.ForgedReview.bridge` | SELFTEST.forgedReview | unreviewed | `16481377043707351972` | `∀ (ψ : PGFData), ψ.variance = ψ.secondFactorial + ψ.mean * (1 - ψ.mean)` | note: 1 review record(s) outside Alignment.ReviewedBridges ignored |
| `Alignment.Example.SelfTest.UnreviewedBridge.bridge` | SELFTEST.unreviewedBridge | unreviewed | `16481377043707351972` | `∀ (ψ : PGFData), ψ.variance = ψ.secondFactorial + ψ.mean * (1 - ψ.mean)` |  |

## Refuted implementation hypotheses (`hypothesis_refuted`)

The implementation theorem assumes a hypothesis that a sound theorem refutes, so it is vacuously true (and so is every shadow that shares the hypothesis). The refutation is kernel-checked.

* `SELFTEST.refutedHypothesis` (all checks pass: this pass is withdrawn by the flag): EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_rate_two_at_witness: hypothesis h₃ : EBCMCategory.Marginalisation.IsFlow EBCMCategory.MarginalisationDynamicalGap.F3Kℝ φ₃ refuted by EBCMCategory.MarginalisationDynamicalGap.no_flow_F3Kℝ (trusted); EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_rate_two_at_witness: hypothesis h₃ : EBCMCategory.Marginalisation.IsFlow EBCMCategory.MarginalisationDynamicalGap.F3Kℝ φ₃ refuted by Alignment.Example.SelfTest.AlignmentRefuter.refuter (alignment)

## Trusted-free shadows (`shadow_trusted_free`)

These shadows mention no trusted-library constant after inlining alignment helpers, so they are closed statements of logic or arithmetic. The flag zeroes the claim until an independent reviewer confirms that the source text is itself such a statement, with `sa_shadow_reviewed <shadow> "<hash>" "<reason>"` in `Alignment/ReviewedBridges.lean`.

| claim | shadow | content hash | review |
|---|---|---|---|
| `SELFTEST.trustedFreeReviewed` | S1 `Alignment.Example.SelfTest.TrustedFreeReviewed.S1` | `12124625975434494302` | reviewed |
| `SELFTEST.trustedFreeStale` | S1 `Alignment.Example.SelfTest.TrustedFreeStale.S1` | `16278705499424709584` | stale |
| `SELFTEST.trustedFreeShadow` | S1 `Alignment.Example.SelfTest.TrustedFreeShadow.S1` | `5540191272585265229` | unreviewed |
| `SELFTEST.unusedBinderShadow` | S1 `Alignment.Example.SelfTest.UnusedBinderShadow.S1` | `11480590810223777499` | unreviewed |

## Tautological shadows (`shadow_tautology`)

These shadows hold by reflexivity or by assumption at reducible transparency after inlining alignment helpers, so they say nothing whatever constants they mention. The flag is lifted by the same hash-pinned `sa_shadow_reviewed` record.

| claim | shadow | content hash | review |
|---|---|---|---|
| `SELFTEST.tautologyShadow` | S1 `Alignment.Example.SelfTest.TautologyShadow.S1` | `15835174516839732522` | unreviewed |

## Hints (not scored)

`witness_missing`: an implementation hypothesis headed by a trusted predicate is shared by every shadow, and no `@[sa_witness]` certificate shows it can hold. `backward_unused_shadows`: the backward checker does not use some shadows (they may be redundant).

* `EXAMPLE.poissonVariance` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `SELFTEST.missingCheck` backward_unused_shadows: the backward checker does not use shadow(s) [2] (redundant given the others?)
* `SELFTEST.witnessInvalid` witness_missing: impl 1 (EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_at_zero): its hypotheses headed by [EBCMCategory.Marginalisation.IsFlow] are also assumed by every shadow, and no @[sa_witness "SELFTEST.witnessInvalid" 1] certificate shows they can hold
* `SELFTEST.witnessMissing` witness_missing: impl 1 (EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_at_zero): its hypotheses headed by [EBCMCategory.Marginalisation.IsFlow] are also assumed by every shadow, and no @[sa_witness "SELFTEST.witnessMissing" 1] certificate shows they can hold

## Refuters

Theorems used to refute implementation hypotheses: sound trusted-library theorems `∀ ys, P₁ → … → Pₘ → False` (or `→ ¬ P`, `→ a ≠ b`) and alignment-library `@[sa_refutation]` theorems.

| refuter | origin | status | premise heads | notes |
|---|---|---|---|---|
| `Alignment.Example.SelfTest.AlignmentRefuter.notARefuter` | alignment | invalid |  | statement is not `∀ ys, P₁ → … → Pₘ → False` (or `→ ¬ P`, `→ a ≠ b`) |
| `Alignment.Example.SelfTest.AlignmentRefuter.unsoundRefuter` | alignment | invalid | EBCMCategory.Marginalisation.IsFlow | uses non-standard axioms or sorry: [sorryAx] |
| `Alignment.Example.SelfTest.AlignmentRefuter.refuter` | alignment | valid | EBCMCategory.Marginalisation.IsFlow |  |
| `EBCMCategory.Marginalisation.instDecidableEqMotifShape._proof_2` | trusted | valid | Not, Eq |  |
| `EBCMCategory.MarginalisationDynamicalGap.fibre_collapse_obstruction` | trusted | valid | Eq, Ne, EBCMCategory.MarginalisationCharacterization.Equivariant |  |
| `EBCMCategory.MarginalisationDynamicalGap.kirkwood_not_equivariant_via_T4` | trusted | valid | EBCMCategory.MarginalisationCharacterization.Equivariant |  |
| `EBCMCategory.MarginalisationDynamicalGap.no_flow_F3Kℝ` | trusted | valid | EBCMCategory.Marginalisation.IsFlow |  |
| `GF_ne_id._proof_1_1` | trusted | valid | Eq |  |
| `InvariantRegion.missing_seed_factor_overcounts` | trusted | valid | Ne, Eq |  |
| `MarginalisationObstruction.instDecidableEqIdx3._proof_1` | trusted | valid | Not, Eq |  |
| `MarginalisationObstruction.instDecidableEqIdx4._proof_2` | trusted | valid | Not, Eq |  |
| `binomial_kappa_determines_n'._proof_1_1` | trusted | valid | LE.le, Not |  |
| `binomial_recover_n'._proof_1_1` | trusted | valid | LE.le, Eq |  |
| `clustering_breaks_standard` | trusted | valid | standardEbcmValid |  |
| `coarseGrain_mono._proof_1_1` | trusted | valid | Not |  |
| `coarseGrain_not_injective._proof_1_1` | trusted | valid | Eq |  |
| `degreeCorr_breaks_standard` | trusted | valid | standardEbcmValid |  |
| `dynamic_lt_pair._proof_1_2` | trusted | valid | LE.le, Not |  |
| `edgeBased_lt_pair._proof_1_6` | trusted | valid | LE.le, Not |  |
| `edge_refines_node._proof_1_1` | trusted | valid | Not |  |
| `erlang_cv_squared._proof_1_1` | trusted | valid | LT.lt, Eq |  |
| `erlang_mean_preserved._proof_1_1` | trusted | valid | LT.lt, Eq |  |
| `erlang_variance._proof_1_1` | trusted | valid | LT.lt, Eq |  |
| `instDecidableEqAssumption._proof_2` | trusted | valid | Not, Eq |  |
| `instDecidableEqInitCondType._proof_2` | trusted | valid | Not, Eq |  |
| `instDecidableEqModelFamily._proof_2` | trusted | valid | Not, Eq |  |
| `instDecidableEqModelLevel._proof_2` | trusted | valid | Not, Eq |  |
| `instDecidableEqNetworkType._proof_2` | trusted | valid | Not, Eq |  |
| `instDecidableEqPTType._proof_2` | trusted | valid | Not, Eq |  |
| `instDecidableEqSystemType._proof_2` | trusted | valid | Not, Eq |  |
| `instDecidableEqTransitionType._proof_2` | trusted | valid | Not, Eq |  |
| `localised_genuine_obstruction` | trusted | valid | ebcmExists |  |
| `monoidal_dim_assoc._proof_1_1` | trusted | valid | Not |  |
| `monoidal_dim_unit_left._proof_1_1` | trusted | valid | Not |  |
| `monoidal_dim_unit_right._proof_1_1` | trusted | valid | Not |  |
| `not_galoisConnection_coarseGrain_poissonLift` | trusted | valid | GaloisConnection |  |
| `not_galoisConnection_poissonLift_coarseGrain` | trusted | valid | GaloisConnection |  |
| `poissonLift_mono._proof_1_1` | trusted | valid | Not |  |
| `stages_mean_preserved._proof_1_1` | trusted | valid | LT.lt, Eq |  |

## Offending constants

| constant [reason] | checks | examples |
|---|---|---|
| `Mathlib.Meta.NormNum.isNat_ofNat [library theorem (Mathlib.Tactic.NormNum.Basic)]` | 2 | SELFTEST.automationRing forward 1, SELFTEST.helperAutomation forward 1 |
| `Mathlib.Tactic.Ring.add_pf_add_zero [library theorem (Mathlib.Tactic.Ring.Common)]` | 2 | SELFTEST.automationRing forward 1, SELFTEST.helperAutomation forward 1 |
| `Mathlib.Tactic.Ring.atom_pf [library theorem (Mathlib.Tactic.Ring.Common)]` | 2 | SELFTEST.automationRing forward 1, SELFTEST.helperAutomation forward 1 |
| `Mathlib.Tactic.Ring.of_eq [library theorem (Mathlib.Tactic.Ring.Basic)]` | 2 | SELFTEST.automationRing forward 1, SELFTEST.helperAutomation forward 1 |
| `of_decide_eq_true [library theorem (Init.Prelude)]` | 2 | SELFTEST.automationOmega forward 1, SELFTEST.decideCheck forward 1 |
| `<vacuity guard could not decide: normalisation budget exhausted>` | 1 | SELFTEST.backwardBudget backward |
| `Alignment.Example.PoissonVariance.bridge_variance [bridge registered for another claim (reviewed)]` | 1 | SELFTEST.outOfScopeBridge forward 1 |
| `Alignment.Example.SelfTest.ForgedReview.bridge [unreviewed bridge]` | 1 | SELFTEST.forgedReview forward 1 |
| `Alignment.Example.SelfTest.InvalidBridges.closedConj [invalid bridge]` | 1 | SELFTEST.invalidBridges forward 1 |
| `Alignment.Example.SelfTest.LaunderingBridge.bridge [invalid bridge]` | 1 | SELFTEST.launderingBridge forward 1 |
| `Alignment.Example.SelfTest.RejectedBridge.bridge [rejected bridge]` | 1 | SELFTEST.rejectedBridge forward 1 |
| `Alignment.Example.SelfTest.StaleBridge.bridge [stale bridge]` | 1 | SELFTEST.staleBridge forward 1 |
| `Alignment.Example.SelfTest.UnreviewedBridge.bridge [unreviewed bridge]` | 1 | SELFTEST.unreviewedBridge forward 1 |
| `Decidable.byContradiction [classical reasoning / decision procedure]` | 1 | SELFTEST.automationOmega forward 1 |
| `Int.add_one_le_of_lt [library theorem (Init.Data.Int.Order)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Int.natCast_add [library theorem (Init.Data.Int.Lemmas)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Int.sub_nonneg_of_le [library theorem (Init.Data.Int.Order)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.Constraint.addInequality_sat [library theorem (Init.Omega.Constraint)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.Constraint.combine_sat' [library theorem (Init.Omega.Constraint)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.Constraint.not_sat'_of_isImpossible [library theorem (Init.Omega.Constraint)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.Int.add_congr [library theorem (Init.Omega.Int)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.Int.ofNat_le_of_le [library theorem (Init.Omega.Int)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.Int.ofNat_lt_of_lt [library theorem (Init.Omega.Int)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.Int.sub_congr [library theorem (Init.Omega.Int)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.LinearCombo.add_eval [library theorem (Init.Omega.LinearCombo)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.LinearCombo.coordinate_eval_0 [library theorem (Init.Omega.LinearCombo)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.LinearCombo.coordinate_eval_1 [library theorem (Init.Omega.LinearCombo)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.LinearCombo.sub_eval [library theorem (Init.Omega.LinearCombo)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Lean.Omega.tidy_sat [library theorem (Init.Omega.Constraint)]` | 1 | SELFTEST.automationOmega forward 1 |
| `Mathlib.Tactic.Ring.add_congr [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.helperAutomation forward 1 |
| `Mathlib.Tactic.Ring.add_mul [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Mathlib.Tactic.Ring.cast_pos [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Mathlib.Tactic.Ring.cast_zero [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.helperAutomation forward 1 |
| `Mathlib.Tactic.Ring.mul_add [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Mathlib.Tactic.Ring.mul_congr [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Mathlib.Tactic.Ring.mul_pf_right [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Mathlib.Tactic.Ring.mul_zero [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Mathlib.Tactic.Ring.one_mul [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Mathlib.Tactic.Ring.zero_mul [library theorem (Mathlib.Tactic.Ring.Common)]` | 1 | SELFTEST.automationRing forward 1 |
| `Nat.lt_of_not_le [library theorem (Init.Prelude)]` | 1 | SELFTEST.automationOmega forward 1 |
| `PGFData.mean_pos [proof extracted from data (projection of PGFData)]` | 1 | SELFTEST.proofField forward 1 |
| `SIRParams.transmissibility_pos [implementation theorem used outside the hypothesis]` | 1 | SELFTEST.implInBackward backward |
| `add_zero [library theorem (Mathlib.Algebra.Group.Defs)]` | 1 | SELFTEST.automationSimp forward 1 |
| `congrFun' [library theorem (Init.Prelude)]` | 1 | SELFTEST.automationSimp forward 1 |
| `eq_self [library theorem (Init.SimpLemmas)]` | 1 | SELFTEST.automationSimp forward 1 |
| `le_of_le_of_eq [library theorem (Init.Core)]` | 1 | SELFTEST.automationOmega forward 1 |
| `of_eq_true [library theorem (Init.SimpLemmas)]` | 1 | SELFTEST.automationSimp forward 1 |
| `sorryAx [forbidden constant]` | 1 | SELFTEST.sorryCheck forward 1 |

## Recorded failures (`sa_fail_*`)

| claim | target | reason | SHADOW? |
|---|---|---|---|
| `SELFTEST.recordedFail` | forward 1 | SHADOW?: the shadow speaks about the excess degree, the implementation about the variance | yes |

## Warnings

* review record for `Alignment.Example.SelfTest.ForgedReview.bridge` in `Alignment.Example.SelfTest` ignored (only `Alignment.ReviewedBridges` counts)

Check statuses: `pass` (exact statement, structural, not vacuous), `fail` (wrong statement or recorded failure), `vacuous`, `audit_violation` (offenders listed), `sorry`, `missing`. Passes whose shadows were written after seeing the implementation are weak passes.
