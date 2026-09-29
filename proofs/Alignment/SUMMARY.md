# SA-PASS summary: EdgeBasedModels.jl Lean proofs (EBCMCategory)

**Status of the tree.** Legacy; not cited. The genuine library is `NetworkEpiCore.jl/proofs`.

**Source.** The numbers come from `Alignment/report/sa_pass_report.{md,json}` (Lean 4.29.0-rc4). The latest run is 2026-09-26 18:44, after WP4b and the independent shadow review (last column below; details in "After WP4/WP4b remediation (2026-09-26)" at the end). The "after WP4" column is the 11:43 run, regenerated after WP4. WP4 deleted the six axioms, proved `no_flow_F3Kℝ` and hardened the audit (below). The "before" column is the 05:11 run that the triage and the adversarial spot check examined. The triage data (`TRIAGE.md`) refer to that run. The procedure is `SA-PASS_SKILL.md` as adapted in `Alignment/README.md`.

**What SA-PASS measures.** SA-PASS checks whether each Lean statement says what its text says. It does not check whether the text is true, so this summary reports both.

## Numbers

| quantity | before (05:11) | after WP4 (11:43) | after WP4b + review (18:44) |
|---|---|---|---|
| claims in registry | 665 | 672 | 711 |
| registered in Lean | 429 | 425 | 557 (467 implemented, 71 missing, 19 informal) |
| required (status implemented) | 429 | 428 (3 of them not yet registered: their blind shadows are owed) | 467 (all registered) |
| not registered: missing / informal / implemented / axiomatized | 168 / 59 / 0 / 9 | 175 / 69 / 3 / 0 | 104 / 50 / 0 / 0 |
| **SA-PASS = 1** | **171 of 429 required (39.9%)** | **157 of 428 required (36.7%)** | **182 of 467 required (39.0%)** |
| mean SA-PASS_soft (registered) | 0.599 | 0.520 | 0.467 |
| required failures | 258 | 271 | 285 |
| check statuses | pass 702, fail 610, missing 2 | pass 674, fail 604, vacuous 21, missing 2 | pass 768, fail 667, vacuous 10, missing 351 (the missing checks belong to the 90 registered `gap` claims) |
| `shadow_trusted_free` (scores 0 until reviewed) | – | 65 claims (117 shadows), none reviewed | 78 claims (142 shadows) unreviewed; 16 shadows of 11 claims reviewed |
| `shadow_tautology` (scores 0 until reviewed) | – | 0 claims (the flag is new; only the self-test mock trips it) | 0 claims |
| `hypothesis_refuted` (scores 0) | – | 3 claims | 3 claims |
| hints (not scored) | – | backward_unused_shadows 123, witness_missing 14 | backward_unused_shadows 150, witness_missing 8 |
| refuters (valid) | – | 34: 7 named theorems, 27 compiler-generated auxiliaries (`…._proof_1`) | 36: 9 named theorems, 27 auxiliaries |
| bridges | 2 reviewed | 2 reviewed | 2 reviewed (no unreviewed bridge exists) |

The drop from 171 to 157 passes comes from the new checks and one retired claim (see "Withdrawn passes"). No claim gained a pass in WP4. For the rise to 182, see the final section.

**Per group** (SA-PASS = 1 / registered, required failures in brackets). The registered denominators grew in WP4b because missing and informal claims were registered with blind shadows:

| group | before | after WP4 | after WP4b + review |
|---|---|---|---|
| CategoricalComposition | 15/32 (17) | 9/32 (23) | 14/49 (21) |
| ClosureTheorem | 5/26 (21) | 4/26 (22) | 4/26 (22) |
| ClusteringExtension | 4/13 (9) | 3/13 (10) | 3/16 (10) |
| CoarseGrain | 7/9 (2) | 7/9 (2) | 7/9 (2) |
| ConvergenceTheorems | 11/23 (12) | 11/23 (12) | 13/33 (14) |
| DegreeCorrelation | 20/30 (10) | 20/30 (10) | 20/35 (13) |
| Docs | 12/29 (17) | 10/25 (15) | 10/43 (15) |
| DynamicLimits | 11/28 (17) | 11/28 (17) | 11/38 (21) |
| EpiCategory | 6/6 (0) | 6/6 (0) | 7/9 (0) |
| GaloisPair | 16/19 (3) | 16/19 (3) | 17/24 (5) |
| Hierarchy | 8/13 (5) | 8/13 (5) | 8/17 (8) |
| InvariantRegion | 5/28 (23) | 5/28 (23) | 6/41 (25) |
| MarginalisationCharacterization | 2/14 (12) | 2/14 (12) | 5/21 (12) |
| MarginalisationDynamicalGap | 7/13 (6) | 5/13 (11) | 7/26 (17) |
| MarginalisationFunctor | 3/7 (4) | 3/7 (4) | 4/9 (4) |
| MessagePassingBridge | 6/24 (18) | 6/24 (18) | 8/25 (16) |
| MethodOfStages | 0/8 (8) | 0/8 (8) | 1/11 (9) |
| Obstructions | 10/32 (22) | 10/32 (22) | 13/37 (19) |
| PairwiseClosureConditions | 10/18 (8) | 8/18 (10) | 10/19 (8) |
| SEIREquations | 3/14 (11) | 3/14 (11) | 3/14 (11) |
| SurvivalBridge | 3/23 (20) | 3/23 (20) | 3/31 (21) |
| VolzMeyersEquations | 7/20 (13) | 7/20 (13) | 8/24 (12) |

## What WP4 changed

- **Soundness.** The trusted library declares no `axiom`. The inconsistent `tree_pair_exactness` (instances ⟨True⟩ and ⟨1⟩ on `Unit` proved 1 = 0) and the five content-free axioms (x = x, ≤-transitivity, True, T·ρ = T·ρ, True) were deleted. Their results are now cited prose with corrected citations, and their claims were re-registered as missing or informal. `bash scripts/axiom_gate.sh` enforces two conditions: there is no `axiom` in `EBCMCategory/`, and every declaration's axioms lie within propext, Quot.sound and Classical.choice. CI runs the gate and the audit self-test (`.github/workflows/lean.yml`).
- **Vacuity on record.** `no_flow_F3Kℝ : ∀ φ, ¬ IsFlow F3Kℝ φ` is a trusted theorem: v′ = v²/4 has no global solution from v(0) = 4, because the solution 4/(1 − t) blows up at t = 1. The docstring of `trajectoryGap_rate_two_at_witness`, the only trusted theorem that assumes such a flow, now says that it holds vacuously.
- **Audit bypasses closed.** The three bypasses found by the spot check are closed, and so are the weaknesses found in review of the first fixes. Each is ported as a mock into `Alignment/Example/SelfTest.lean`, and the self-test passes (54 example and mock claims, every expectation met):
  1. `shadow_trusted_free`: a shadow with no trusted constant after inlining alignment helpers. Constants that occur only as the type of an unused binder do not count. A new flag, `shadow_tautology`, marks shadows that hold by reflexivity or assumption at reducible transparency. Either flag is lifted only by a hash-pinned `sa_shadow_reviewed` record. Mocks: `SELFTEST.trustedFreeShadow`, `.trustedFreeReviewed`, `.trustedFreeStale`, `.unusedBinderShadow`, `.tautologyShadow`.
  2. `hypothesis_refuted`: an implementation hypothesis refuted by a sound trusted or `@[sa_refutation]` theorem, kernel-checked. `witness_invalid` is a flag and `witness_missing` a hint, for shared hypotheses without an `@[sa_witness]` certificate. Impossibility theorems (conclusion `False`) are not refuted by their own content. Self-test refuters apply only to self-test claims. Mocks: `SELFTEST.refutedHypothesis`, `.witnessMissing`, `.witnessInvalid`, `.impossibilityImpl`.
  3. Backward vacuity guard: the shadow binders must be used relevantly, and the proof must not type-check with the shadows replaced by arbitrary propositions. The guard now fails closed. If the normaliser exhausts its budget, the check is `audit_violation`. It used to fall back to the unnormalised proof. The normaliser now memoises, so the two checkers that used to exhaust the budget (`MarginalisationCharacterization.kkrNecessaryNotSufficient.formal` and `.kirkwoodFormNotEquivariant`) are decided on their normal forms. The first passes, and its backward checker uses both shadows. Mocks: `SELFTEST.backwardVacuous`, `.backwardVacuousEval`, `.backwardBudget`.

## Withdrawn passes

14 of the 171 passes are withdrawn: 4 bogus passes caught by the new checks, 9 other passes whose shadows are closed arithmetic (spot-check verdict: 8 weak, 1 strong), and 1 retired claim.

| claim | spot-check verdict | withdrawn by |
|---|---|---|
| `CategoricalComposition.R100a` | weak | `shadow_trusted_free` |
| `CategoricalComposition.R100b` | weak | `shadow_trusted_free` |
| `CategoricalComposition.R100c` | weak | `shadow_trusted_free` |
| `CategoricalComposition.R100d` | weak | `shadow_trusted_free` |
| `CategoricalComposition.R100e` | weak | `shadow_trusted_free` |
| `CategoricalComposition.R96a` | weak | `shadow_trusted_free` |
| `ClosureTheorem.table.R59` | bogus | `shadow_trusted_free` |
| `ClusteringExtension.R73` | weak | `shadow_trusted_free` |
| `Docs.ms.T5-rateTwo` | bogus | `hypothesis_refuted` |
| `Docs.readme.r0RewiringIndependence` | weak | retired: the README sentence it quoted was deleted in P2.1, so the claim is no longer registered |
| `MarginalisationDynamicalGap.fibreCollapseObstruction` | bogus | backward check `vacuous` |
| `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a` | bogus | `hypothesis_refuted` |
| `PairwiseClosureConditions.header.safeRegime` | strong | `shadow_trusted_free` |
| `PairwiseClosureConditions.weightInUnitInterval` | weak | `shadow_trusted_free` |

The trusted-free passes are withdrawn pending review, not refuted. 9 claims (12 shadows) have every check passing and are zeroed only by `shadow_trusted_free`/`shadow_tautology`, excluding the bogus `ClosureTheorem.table.R59`. They need an independent reviewer to decide whether each source text is itself arithmetic, and to record `sa_shadow_reviewed` for those that are.

## The passes are weak evidence

- 99 of the 157 passes have at least one shadow or reference literally identical to the implementation, and 65 have both.
- The 157 passes cover only 122 distinct implementation theorems, because table rows, Results and Docs claims repeat one another. By the same count the spot check's 171 passes covered 133.
- Most passes are rfl-level facts.
- Passing claims whose text is false, corrected in P2 by a later work package:
  - `DynamicLimits.R33a`
  - `DynamicLimits.table.R33`
  - `DynamicLimits.R36a`
  - `DynamicLimits.table.R36`
  - `CategoricalComposition.R96f`
  - `Docs.readme.r0RewiringIndependence` no longer passes (retired: the README sentence it quoted was deleted in P2.1, so the claim is no longer registered).
  - `ClosureTheorem.table.R59` no longer passes (`shadow_trusted_free`).
  - `CategoricalComposition.R96g` is true only of the additive quantity.
- The witness results `Docs.ms.T5-rateTwo` and `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a` held only because their hypothesis is unsatisfiable. They are now flagged `hypothesis_refuted`, and so is `MarginalisationDynamicalGap.header.overview`.

## Triage of the 494 non-passing claims (05:11 run)

**Primary category:**

| category | claims |
|---|---|
| forward fail | 97 |
| backward fail | 33 |
| forward and backward fail | 118 |
| incomplete or SHADOW? only | 9 |
| vacuous shadow | 1 |
| bridge rejected | 0 |
| gap | 168 |
| informal | 59 |
| axiomatized | 9 |

**Flags:** false or misleading text 108, genuine ambiguity 24, tautological or vacuous implementation 23, audit limitation only 31, Lean definition differs from the text 38.

**Is the text true?** yes 280, partly 77, **no 83**, ill-posed 31, unverified 17, depends on reading 6.

## Headline findings

1. **The environment is sound now** (was: unsound). The inconsistent `axiom tree_pair_exactness` is deleted, the library declares no axiom, and the axiom gate keeps it that way (P1.1, done).
2. **The five tautological axioms are deleted** (P1.2, done). Their docstrings had presented them as functoriality, naturality, a spectral R₀ and a CLT. Their claims are now missing or informal.
3. **No theorem is about solutions of the EBCM that the Julia package integrates.**
   - PGFs are free numbers, not functions.
   - Vector fields are scalar expressions.
   - There is no invariance, final-size or threshold theorem for the ODE, and no category theory.
   - The README's former claims ("conservation laws, R₀ independence of rewiring, PGF identities, VM invariants") were not supported. The paragraph has been replaced (P2.1).
4. **False mathematics in docstrings, specs and code** (corrections in P2; not part of WP4):
   - R₀ independent of rewiring, and fast-rewiring R₀ = T·κ.
   - Additive multiplex R₀. This error is also in Julia `multiplex_R0`.
   - Degree-correlated NGM k·Q, which is off by one.
   - "Erlang staging preserves R₀ and final size".
   - The clustering-coefficient formula.
   - The φ_I equation (ψ′/θ where it should be ψ″).
   - The Volz ↔ DSA variables (missing θ).
   - The VM incidence and VM initial condition (S+I+R = 1+sf, also in the Julia VM builder).
   - "R₀_MA = T_MA(κ−1) asymptotically" (in fact R₀_MA equals R₀_EBCM exactly).
   - A Galois connection that is false in the model.
   - Universal Kirkwood obstructions, which are false for the Lean predicate.
   - "Poisson is the unique PGF with excess = mean".
   - The unconditional CLT is already corrected: Result 111 now states the three regimes of Ball (2021), Theorems 2.1–2.3.
5. **The marginalisation certificates are vacuous, and this is now a theorem.** `no_flow_F3Kℝ` proves that no global flow of v²/4 exists (blow-up at t = 1). The "formal bridge" to the Gillespie error of 0.32 therefore carries no information. The audit flags the claims that use it. T1, T4, T5 and T7 are genuine general lemmas. P1.4's restatement of the T1/T5/T7 witness applications with local solutions is not done: `MARGINALISATION_SPEC.md` and `MarginalisationDynamicalGap.header.overview` still present the vacuous witness result.
6. **Genuine content** is in PairwiseClosureConditions, T1, T4, T5 and T7 (general form), the DegreeCorrelation 2×2 algebra, PolyPGF R113–R115 and the moment identities. Most of these pass.
7. **Highest-value work** (P3) moves to `NetworkEpiCore.jl/proofs`:
   - Define a genuine PGF and EBCM vector field.
   - Prove the invariant region along solutions.
   - Prove the final-size relation and the R₀ threshold.
   - Prove the Rempała conjugacy.
   - Prove the spectral-radius R₀ for degree-correlated and multiplex networks.
   - Prove the KKR characterisation and the EBCM → pairwise semiconjugacy.

## Spot check of the 171 passes (05:11 run; adversarial reviewer, all 171 examined)

| verdict | claims |
|---|---|
| strong: text, shadows and implementation state the same non-definitional fact about the object the text names | 27 |
| weak: holds by unfolding, `rfl`, a tautology or one-step arithmetic, or concerns a free-scalar stand-in for the real object | 140 |
| bogus: the pass relies on a defect the audit should catch | 4 |

The 171 passes covered only 133 distinct implementation theorems.

**Bogus passes and the bypasses they exposed.** All four are withdrawn by the regenerated audit.

- `ClosureTheorem.table.R59`: The text 'PT classification is exhaustive for kappa > 0' claims that every kappa > 0 falls in a Binomial, Poisson or NegBin family. **Bypass:** Content-free shadow. **Status:** closed by `shadow_trusted_free` (mock `SELFTEST.trustedFreeShadow`; the evasions `SELFTEST.unusedBinderShadow` and `SELFTEST.tautologyShadow` are caught too); now withdrawn.
- `Docs.ms.T5-rateTwo`: The impl trajectoryGap_rate_two_at_witness assumes IsFlow F3Kℝ φ₃. **Bypass:** Vacuous shared hypothesis. **Status:** closed by `hypothesis_refuted` with the new `no_flow_F3Kℝ` as refuter (mock `SELFTEST.refutedHypothesis`), plus the `witness_missing` hint and `@[sa_witness]` certificates (`SELFTEST.witnessMissing`, `SELFTEST.witnessInvalid`); now withdrawn.
- `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a`: Same impl as Docs.ms.T5-rateTwo and the same defect. **Bypass:** Same as Docs.ms.T5-rateTwo: there is no satisfiability or witness check for the hypotheses shared by the shadows and T̂. **Status:** closed as for `Docs.ms.T5-rateTwo`; now withdrawn.
- `MarginalisationDynamicalGap.fibreCollapseObstruction`: The backward checker `bwd (_s1 : S1)` never uses its shadow. **Bypass:** Backward checks are not vacuity-guarded. **Status:** closed by the backward vacuity guard, which now fails closed (mocks `SELFTEST.backwardVacuous`, `SELFTEST.backwardVacuousEval`, `SELFTEST.backwardBudget`); now withdrawn.

**Honest headline.** SA-PASS = 1 holds for 157/428 required claims. By the spot-check verdicts, 26 of these are strong and 131 weak. No bogus pass survives. So about **26 of 428 required claims (6.1%) are substantive statements that the Lean library proves as stated.**

## Owed work (not done in WP4)

- **Blind re-shadowing.** Three required claims have no `sa_claim` yet and count as required failures: `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b`, `MarginalisationDynamicalGap.noGlobalSolutionSqDivFour`, `MarginalisationDynamicalGap.noFlowF3Real`. Their shadows must be written blind (SA-PASS_SKILL.md §2) by someone who has not seen the implementation. The WP4 implementer did not write them.
- **Review of trusted-free and tautological shadows.** The 9 claims (12 shadows) under "Withdrawn passes" other than the bogus `ClosureTheorem.table.R59`. A reviewer independent of the shadow authors must record `sa_shadow_reviewed`.
- **P1.4 (rest).** Restate the T1/T5/T7 witness applications with local solutions. Relabel the vacuous or tautological implementations listed in TRIAGE.md P1.4.
- **P2.** Correct the false docstrings, followed by blind re-shadowing of the changed claims.
- **CI.** `lean.yml` parses but has not yet run on GitHub.

## Reproduce
```sh
cd EdgeBasedModels.jl/proofs
perl -e 'alarm 1800; exec @ARGV' bash scripts/axiom_gate.sh
perl -e 'alarm 1800; exec @ARGV' bash scripts/sa_pass.sh
perl -e 'alarm 900; exec @ARGV' bash scripts/sa_pass.sh --no-build --self-test
perl -e 'alarm 900; exec @ARGV' bash scripts/sa_pass.sh --no-build --strict   # exits 1: 285 required failures (18:44 run; 271 after WP4)
```
Per-claim cause, fix, truth verdict and action: `TRIAGE.md` in this directory.

## After WP4/WP4b remediation (2026-09-26)

**Runs.**
- 18:11 audit: after the WP4b remediator, the blind shadow authors and the checker author, but before the independent review.
- 18:44 audit: after the review. The review changed only `Alignment/ReviewedBridges.lean`. A first post-review run at 18:34 gave identical numbers; the final run followed a comment-only edit.
- On the 18:44 audit, `bash scripts/sa_pass.sh --self-test` passed: 54 claim, 9 bridge and 4 refuter expectations met.
- `bash scripts/sa_pass.sh --check-sources` also passed: every claim text matches its cited lines.

| quantity | after WP4 (11:43) | WP4b, before review (18:11) | after review (18:44) |
|---|---|---|---|
| claims in registry / registered / required | 672 / 425 / 428 | 711 / 557 / 467 | 711 / 557 / 467 |
| **SA-PASS = 1** (required) | **157 (36.7%)** | **171 (36.6%)** | **182 (39.0%)** |
| mean SA-PASS_soft (registered) | 0.520 | 0.4476 | 0.4674 |
| required failures | 271 | 296 | 285 |
| `shadow_trusted_free` claims (unreviewed shadows) | 65 (117) | 89 (158) | 78 (142) |
| claims whose checks all pass but that are zeroed only by `shadow_trusted_free` | 9 | 13 | 2 (both rejected in review) |
| reviewed shadows / reviewed bridges | 0 / 2 | 0 / 2 | 16 / 2 |

The mean soft score fell between 11:43 and 18:11 because 132 more claims are registered. 90 of them are `gap` claims (status missing or informal), and each scores 0.

**What WP4b changed** (from the registry notes and the reports):
- 275 claims carry a WP4b registry note. 39 of them are new, corrected trusted theorems, all registered and required; 14 of those pass. The other notes record corrected texts, each with its previous wording.
- The registry grew from 672 to 711 claims.
- Every required claim is now registered. This includes the three claims whose blind shadows were owed: `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b`, `.noGlobalSolutionSqDivFour` and `.noFlowF3Real`. None of the three passes: each has failing forward checks.
- 90 missing or informal claims are registered with blind shadows, so they now appear as `gap`.
- Five claims listed above as passing with false text no longer pass after their texts were corrected: `DynamicLimits.R33a`, `.table.R33`, `.R36a`, `.table.R36` and `CategoricalComposition.R96f`. Each now has a failing forward check. `CategoricalComposition.R96g` still passes.
- Vacuous checks fell from 21 to 10.

**Independent review (WP4b role 4).** The reviewer wrote none of the shadows, checkers or trusted theorems.
- *Bridges.* There was no unreviewed bridge. The only bridges are the two `SurvivalBridge.R46c` bridges, reviewed earlier.
- *Candidates.* The 13 claims whose checks all pass and that the flag alone zeroed: the 9 WP4 claims, plus `CategoricalComposition.R100f.1` (text corrected in WP4b) and three new WP4b claims (`ConvergenceTheorems.dfeDerivativeAbsLeOneIff`, `InvariantRegion.phiILeTheta`, `MarginalisationCharacterization.existsEquivariantIffFibrewise`).
- *Acceptance rule* (stated in `ReviewedBridges.lean`): the claim's own text must itself state the arithmetic or logical fact, and the shadow must state exactly that fact, or something more general.
- *Accepted: 11 claims, 16 hash-pinned `sa_shadow_reviewed` records.* `CategoricalComposition.R96a` (S1, S2), `.R100a`, `.R100b`, `.R100c`, `.R100d`, `.R100e` (S1, S2); `ConvergenceTheorems.dfeDerivativeAbsLeOneIff` (S1, S2); `InvariantRegion.phiILeTheta`; `MarginalisationCharacterization.existsEquivariantIffFibrewise` (S1, S2); `PairwiseClosureConditions.header.safeRegime` (S3, S4); `PairwiseClosureConditions.weightInUnitInterval`. All 16 show as `reviewed` in the 18:44 report. None is stale.
- *Rejected: 2 claims.* No record was written for either, and the reasons are in `ReviewedBridges.lean`.
  - `CategoricalComposition.R100f.1`: the text does not say which real-number identities the pentagon and triangle 'would reduce to'. The shadows adopt one partial reading.
  - `ClusteringExtension.R73`: the text is about R₀, and `clustered_R0` exists. The inequality T(1+T)/2 ≤ T comes from other claims' passages, and 'less' is strict.
- *Not reviewed.* The other 76 flagged claims (142 shadows). Each has a failing or missing check, so a record could not change its score. They should be reviewed once their checks are remediated.

**How strong the 11 new passes are.** The spot-check scale above rates only 2 of the 11 as strong:
- `PairwiseClosureConditions.header.safeRegime`: rated strong in the spot check.
- `existsEquivariantIffFibrewise`: the factorisation lemma, which is elementary but not definitional.

The other 9 hold by one step of arithmetic or logic (1·S = S, ℕ associativity, |x| ≤ 1 ↔ x ≤ 1 for x ≥ 0, and so on), so they are weak. The spot-check verdicts in the earlier section apply to the 05:11 passes. The 182 current passes have not been spot-checked again as a set. Of the 182:
- 113 have a shadow or the reference literally identical to the implementation, and 75 have both.
- They cover 147 distinct implementation theorems.

**Still owed.**
- `CategoricalComposition.R100f.1`: state the identities in the docstring, then re-register, re-shadow blind and review.
- `ClusteringExtension.R73`: needs a blind shadow in terms of `clustered_R0`, and the text's 'less' must be settled against `≤`.
- `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a` passes every check but is correctly zeroed by `hypothesis_refuted`.
- The registry notes of the 39 new WP4b claims still say 'NEEDS BLIND SHADOWS (no sa_claim yet)'. All 39 are now registered, so the notes are stale.
- P1.4 (the rest) and the other items under "Owed work (not done in WP4)" remain as stated there, except the three owed blind shadows, which now exist.
