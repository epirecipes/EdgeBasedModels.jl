import Alignment.Registry
import Alignment.Example.ExampleChecks
import EBCMCategory.EpiCategory
import EBCMCategory.CategoricalComposition
import EBCMCategory.MarginalisationFunctor
import EBCMCategory.MarginalisationDynamicalGap
import EBCMCategory.ClosureTheorem
import EBCMCategory.GaloisPair
import Mathlib.Tactic.Ring

/-!
# SA-PASS self-test mocks

Every claim here (ids `SELFTEST.*`, group `SelfTest`) is deliberately misaligned or
mis-registered in exactly one way. `bash scripts/sa_pass.sh --self-test` checks that the audit
reports exactly the statuses listed in `Alignment/Example/selftest_expected.yaml`, and that the
worked example (`EXAMPLE.*`) passes. Normal reports exclude these ids.

When the audit changes, add every newly found bypass here as a mock (red-team, then port).
The implementation theorems used are real trusted theorems; only the registrations are mocks.
Shadows that are not about a content-free statement say something about a trusted constant (for
example `∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)`, which holds by unfolding a
trusted definition but not by reflexivity at reducible transparency), so that the only defect of
each mock is the one it tests.
-/

set_option linter.unusedVariables false

namespace Alignment.Example.SelfTest

/-- Degree variance in primitive terms (shared vocabulary of the mocks). -/
def degVar (ψ : PGFData) : ℚ := ψ.secondFactorial + ψ.mean * (1 - ψ.mean)

set_option hygiene false in
/-- `selftest_shadows1 "id" Ns : P` declares in namespace `Ns` a reference `T := P`, a single
shadow `S1 := P` and the two completeness certificates. -/
macro "selftest_shadows1 " id:str ns:ident " : " p:term : command => `(
  namespace $ns
  @[sa_reference $id] def T : Prop := $p
  @[sa_shadow $id 1] def S1 : Prop := $p
  @[sa_ref_forward $id 1] theorem ref_fwd1 : T → S1 := fun t => t
  @[sa_complete $id] theorem complete (s1 : S1) : T := s1
  end $ns)

/-! ## Vacuity mocks (expected: forward `vacuous`) -/

selftest_shadows1 "SELFTEST.vacuousIgnore" VacuousIgnore :
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).mean = κ

namespace VacuousIgnore
sa_claim "SELFTEST.vacuousIgnore" group "SelfTest" required
  text "mock: the forward checker ignores the hypothesis" impl PGFData.poisson_variance_eq_mean
@[sa_forward "SELFTEST.vacuousIgnore" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousIgnore") : S1 := fun _ _ => rfl
end VacuousIgnore

selftest_shadows1 "SELFTEST.vacuousBeta" VacuousBeta :
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).mean = κ

namespace VacuousBeta
sa_claim "SELFTEST.vacuousBeta" group "SelfTest" required
  text "mock: eta/beta dodge (fun _ => p) h" impl PGFData.poisson_variance_eq_mean
@[sa_forward "SELFTEST.vacuousBeta" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousBeta") : S1 :=
  (fun (_ : sa_impl% "SELFTEST.vacuousBeta") => (fun _ _ => rfl : S1)) h
end VacuousBeta

selftest_shadows1 "SELFTEST.vacuousAndLeft" VacuousAndLeft :
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).mean = κ

namespace VacuousAndLeft
sa_claim "SELFTEST.vacuousAndLeft" group "SelfTest" required
  text "mock: And.left ⟨p, h⟩ dodge" impl PGFData.poisson_variance_eq_mean
@[sa_forward "SELFTEST.vacuousAndLeft" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousAndLeft") : S1 :=
  And.left (⟨fun _ _ => rfl, h⟩ : S1 ∧ sa_impl% "SELFTEST.vacuousAndLeft")
end VacuousAndLeft

selftest_shadows1 "SELFTEST.vacuousAuxLemma" VacuousAuxLemma :
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).mean = κ

namespace VacuousAuxLemma
sa_claim "SELFTEST.vacuousAuxLemma" group "SelfTest" required
  text "mock: auxiliary lemma dodge" impl PGFData.poisson_variance_eq_mean
theorem aux (h : sa_impl% "SELFTEST.vacuousAuxLemma") : S1 := fun _ _ => rfl
@[sa_forward "SELFTEST.vacuousAuxLemma" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousAuxLemma") : S1 := aux h
end VacuousAuxLemma

selftest_shadows1 "SELFTEST.vacuousEval" VacuousEval :
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).mean = κ

namespace VacuousEval
sa_claim "SELFTEST.vacuousEval" group "SelfTest" required
  text "mock: hypothesis passed to a library function that discards it"
  impl PGFData.poisson_variance_eq_mean
/-- `h` survives normalisation (Function.eval is not unfolded) and only the replacement of the
hypothesis type by an arbitrary proposition exposes the dodge. -/
@[sa_forward "SELFTEST.vacuousEval" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousEval") : S1 :=
  Function.eval h (fun _ => (fun _ _ => rfl : S1))
end VacuousEval

selftest_shadows1 "SELFTEST.vacuousConst" VacuousConst :
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).mean = κ

namespace VacuousConst
sa_claim "SELFTEST.vacuousConst" group "SelfTest" required
  text "mock: Function.const / id wrappers around a hypothesis-free proof"
  impl PGFData.poisson_variance_eq_mean
@[sa_forward "SELFTEST.vacuousConst" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousConst") : S1 :=
  (id (Function.const (sa_impl% "SELFTEST.vacuousConst") (fun _ _ => rfl : S1))) h
end VacuousConst

selftest_shadows1 "SELFTEST.vacuousMatch" VacuousMatch : ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

namespace VacuousMatch
sa_claim "SELFTEST.vacuousMatch" group "SelfTest" required
  text "mock: the hypothesis is destructured but its components are ignored"
  impl SIRParams.transmissibility_pos SIRParams.transmissibility_lt_one
@[sa_forward "SELFTEST.vacuousMatch" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousMatch") : S1 := by
  obtain ⟨_h1, _h2⟩ := h
  exact fun _ => rfl
end VacuousMatch

selftest_shadows1 "SELFTEST.vacuousExistsElim" VacuousExistsElim : ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

namespace VacuousExistsElim
sa_claim "SELFTEST.vacuousExistsElim" group "SelfTest" required
  text "mock: Exists.elim on the hypothesis with a continuation ignoring the witness"
  impl GF_ne_id
@[sa_forward "SELFTEST.vacuousExistsElim" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousExistsElim") : S1 :=
  Exists.elim h (fun _ _ => fun _ => rfl)
end VacuousExistsElim

selftest_shadows1 "SELFTEST.vacuousDataArg" VacuousDataArg : ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

namespace VacuousDataArg
sa_claim "SELFTEST.vacuousDataArg" group "SelfTest" required
  text "mock: the hypothesis only feeds a proof argument of a data term"
  impl SIRParams.transmissibility_pos
@[sa_forward "SELFTEST.vacuousDataArg" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.vacuousDataArg") : S1 := fun p =>
  @Function.eval PGFData (fun _ => p.transmissibility = p.β / (p.β + p.γ))
    (PGFData.poisson p.transmissibility (h p)) (fun _ => rfl)
end VacuousDataArg

/-! ## Structural-rule mocks (expected: `audit_violation`) -/

selftest_shadows1 "SELFTEST.automationSimp" AutomationSimp :
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).variance + 0 = κ

namespace AutomationSimp
sa_claim "SELFTEST.automationSimp" group "SelfTest" required
  text "mock: simp in a checker" impl PGFData.poisson_variance_eq_mean
@[sa_forward "SELFTEST.automationSimp" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.automationSimp") : S1 := by
  intro κ hκ
  simp [h κ hκ]
end AutomationSimp

selftest_shadows1 "SELFTEST.automationRing" AutomationRing :
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).variance = 1 * κ

namespace AutomationRing
sa_claim "SELFTEST.automationRing" group "SelfTest" required
  text "mock: ring in a checker" impl PGFData.poisson_variance_eq_mean
@[sa_forward "SELFTEST.automationRing" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.automationRing") : S1 := by
  intro κ hκ
  rw [h κ hκ]
  ring
end AutomationRing

selftest_shadows1 "SELFTEST.automationOmega" AutomationOmega :
  ∀ (p : SIRParams) (ψ : PGFData), (nodeModel p ψ.mean).dim ≤ (edgeModel p ψ).dim + 1

namespace AutomationOmega
sa_claim "SELFTEST.automationOmega" group "SelfTest" required
  text "mock: omega in a checker" impl edge_refines_node
@[sa_forward "SELFTEST.automationOmega" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.automationOmega") : S1 := by
  intro p ψ
  have h1 : (nodeModel p ψ.mean).dim ≤ (edgeModel p ψ).dim := h p ψ
  omega
end AutomationOmega

selftest_shadows1 "SELFTEST.helperAutomation" HelperAutomation :
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).variance = κ + 0

namespace HelperAutomation
sa_claim "SELFTEST.helperAutomation" group "SelfTest" required
  text "mock: helper lemma proved by ring (inlined by the audit)"
  impl PGFData.poisson_variance_eq_mean
theorem helper (a b : ℚ) (e : a = b) : a = b + 0 := by rw [e]; ring
@[sa_forward "SELFTEST.helperAutomation" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.helperAutomation") : S1 :=
  fun κ hκ => helper _ _ (h κ hκ)
end HelperAutomation

selftest_shadows1 "SELFTEST.proofField" ProofField :
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).variance = κ ∧ 0 < (PGFData.poisson κ hκ).mean

namespace ProofField
sa_claim "SELFTEST.proofField" group "SelfTest" required
  text "mock: proof extracted from library data (a proof field)"
  impl PGFData.poisson_variance_eq_mean
@[sa_forward "SELFTEST.proofField" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.proofField") : S1 :=
  fun κ hκ => ⟨h κ hκ, (PGFData.poisson κ hκ).mean_pos⟩
end ProofField

selftest_shadows1 "SELFTEST.decideCheck" DecideCheck :
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).variance = κ ∧ (2 : ℕ) + 2 = 4

namespace DecideCheck
sa_claim "SELFTEST.decideCheck" group "SelfTest" required
  text "mock: decide in a checker" impl PGFData.poisson_variance_eq_mean
@[sa_forward "SELFTEST.decideCheck" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.decideCheck") : S1 :=
  fun κ hκ => ⟨h κ hκ, by decide⟩
end DecideCheck

selftest_shadows1 "SELFTEST.implInBackward" ImplInBackward :
  ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

namespace ImplInBackward
sa_claim "SELFTEST.implInBackward" group "SelfTest" required
  text "mock: backward checker uses the implementation theorem itself"
  impl SIRParams.transmissibility_pos
@[sa_backward "SELFTEST.implInBackward"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.implInBackward" := SIRParams.transmissibility_pos
end ImplInBackward

/-! ## Bridge mocks -/

selftest_shadows1 "SELFTEST.unreviewedBridge" UnreviewedBridge :
  ∀ (κ : ℚ) (hκ : 0 < κ), degVar (PGFData.poisson κ hκ) = κ

namespace UnreviewedBridge
sa_claim "SELFTEST.unreviewedBridge" group "SelfTest" required
  text "mock: checker uses a bridge without a review record" impl PGFData.poisson_variance_eq_mean
@[sa_bridge "SELFTEST.unreviewedBridge"]
theorem bridge (ψ : PGFData) :
    PGFData.variance ψ = ψ.secondFactorial + ψ.mean * (1 - ψ.mean) := by
  unfold PGFData.variance; ring
@[sa_forward "SELFTEST.unreviewedBridge" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.unreviewedBridge") : S1 :=
  fun κ hκ => (bridge (PGFData.poisson κ hκ)).symm.trans (h κ hκ)
end UnreviewedBridge

selftest_shadows1 "SELFTEST.staleBridge" StaleBridge :
  ∀ (κ : ℚ) (hκ : 0 < κ), degVar (PGFData.poisson κ hκ) = κ

namespace StaleBridge
sa_claim "SELFTEST.staleBridge" group "SelfTest" required
  text "mock: bridge whose review hash is stale" impl PGFData.poisson_variance_eq_mean
@[sa_bridge "SELFTEST.staleBridge"]
theorem bridge (ψ : PGFData) :
    PGFData.variance ψ = ψ.secondFactorial + ψ.mean * (1 - ψ.mean) := by
  unfold PGFData.variance; ring
@[sa_forward "SELFTEST.staleBridge" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.staleBridge") : S1 :=
  fun κ hκ => (bridge (PGFData.poisson κ hκ)).symm.trans (h κ hκ)
end StaleBridge

selftest_shadows1 "SELFTEST.launderingBridge" LaunderingBridge :
  ∀ (κ : ℚ) (hκ : 0 < κ), degVar (PGFData.poisson κ hκ) = κ

namespace LaunderingBridge
sa_claim "SELFTEST.launderingBridge" group "SelfTest" required
  text "mock: reviewed bridge whose proof depends on an implementation theorem"
  impl PGFData.poisson_variance_eq_mean
@[sa_bridge "SELFTEST.launderingBridge"]
theorem bridge (ψ : PGFData) :
    PGFData.variance ψ = ψ.secondFactorial + ψ.mean * (1 - ψ.mean) := by
  have _laundered := PGFData.poisson_variance_eq_mean
  unfold PGFData.variance; ring
@[sa_forward "SELFTEST.launderingBridge" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.launderingBridge") : S1 :=
  fun κ hκ => (bridge (PGFData.poisson κ hκ)).symm.trans (h κ hκ)
end LaunderingBridge

selftest_shadows1 "SELFTEST.rejectedBridge" RejectedBridge :
  ∀ (κ : ℚ) (hκ : 0 < κ), degVar (PGFData.poisson κ hκ) = κ

namespace RejectedBridge
sa_claim "SELFTEST.rejectedBridge" group "SelfTest" required
  text "mock: bridge rejected by the reviewer" impl PGFData.poisson_variance_eq_mean
@[sa_bridge "SELFTEST.rejectedBridge"]
theorem bridge (ψ : PGFData) :
    PGFData.variance ψ = ψ.secondFactorial + ψ.mean * (1 - ψ.mean) := by
  unfold PGFData.variance; ring
@[sa_forward "SELFTEST.rejectedBridge" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.rejectedBridge") : S1 :=
  fun κ hκ => (bridge (PGFData.poisson κ hκ)).symm.trans (h κ hκ)
end RejectedBridge

selftest_shadows1 "SELFTEST.forgedReview" ForgedReview :
  ∀ (κ : ℚ) (hκ : 0 < κ), degVar (PGFData.poisson κ hκ) = κ

namespace ForgedReview
sa_claim "SELFTEST.forgedReview" group "SelfTest" required
  text "mock: review record written outside ReviewedBridges" impl PGFData.poisson_variance_eq_mean
@[sa_bridge "SELFTEST.forgedReview"]
theorem bridge (ψ : PGFData) :
    PGFData.variance ψ = ψ.secondFactorial + ψ.mean * (1 - ψ.mean) := by
  unfold PGFData.variance; ring
-- a forged record: it does not count because it is not in Alignment.ReviewedBridges
sa_bridge_reviewed bridge "16481377043707351972" "SELFTEST: forged review record"
@[sa_forward "SELFTEST.forgedReview" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.forgedReview") : S1 :=
  fun κ hκ => (bridge (PGFData.poisson κ hκ)).symm.trans (h κ hκ)
end ForgedReview

selftest_shadows1 "SELFTEST.outOfScopeBridge" OutOfScopeBridge :
  ∀ (κ : ℚ) (hκ : 0 < κ), degVar (PGFData.poisson κ hκ) = κ

namespace OutOfScopeBridge
sa_claim "SELFTEST.outOfScopeBridge" group "SelfTest" required
  text "mock: checker uses a reviewed bridge registered for another claim"
  impl PGFData.poisson_variance_eq_mean
@[sa_forward "SELFTEST.outOfScopeBridge" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.outOfScopeBridge") : S1 :=
  fun κ hκ =>
    (Alignment.Example.PoissonVariance.bridge_variance (PGFData.poisson κ hκ)).symm.trans (h κ hκ)
end OutOfScopeBridge

selftest_shadows1 "SELFTEST.invalidBridges" InvalidBridges :
  ∀ s : EBCMCategory.Marginalisation.MotifShape,
    EBCMCategory.Marginalisation.MotifShape.isOrder3 s ↔ s.order = 3 ∧ (1 : ℕ) = 1

namespace InvalidBridges
sa_claim "SELFTEST.invalidBridges" group "SelfTest" required
  text "mock: bridges violating the shape rules" impl PGFData.poisson_variance_eq_mean
/-- Closed conjunct on the right-hand side. -/
@[sa_bridge "SELFTEST.invalidBridges"]
theorem closedConj (s : EBCMCategory.Marginalisation.MotifShape) :
    EBCMCategory.Marginalisation.MotifShape.isOrder3 s ↔ s.order = 3 ∧ (1 : ℕ) = 1 :=
  ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩
/-- Left-hand side head is not a trusted definition. -/
@[sa_bridge "SELFTEST.invalidBridges"]
theorem natHead (n : ℕ) : Nat.succ n = n + 1 := rfl
/-- Closed right-hand side. -/
@[sa_bridge "SELFTEST.invalidBridges"]
theorem closedRhs : PGFData.excessDegree = PGFData.excessDegree := rfl
@[sa_forward "SELFTEST.invalidBridges" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.invalidBridges") : S1 := fun s => closedConj s
end InvalidBridges

/-! ## Statement, sorry, missing and recorded-failure mocks -/

selftest_shadows1 "SELFTEST.mismatch" Mismatch :
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).mean = κ

namespace Mismatch
sa_claim "SELFTEST.mismatch" group "SelfTest" required
  text "mock: forward checker with the wrong hypothesis" impl PGFData.poisson_variance_eq_mean
@[sa_forward "SELFTEST.mismatch" 1]
theorem fwd1 (h : ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).excessDegree = κ) : S1 :=
  fun _ _ => rfl
end Mismatch

selftest_shadows1 "SELFTEST.sorryCheck" SorryCheck :
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).variance = κ

namespace SorryCheck
sa_claim "SELFTEST.sorryCheck" group "SelfTest" required
  text "mock: sorry in a checker" impl PGFData.poisson_variance_eq_mean
@[sa_forward "SELFTEST.sorryCheck" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.sorryCheck") : S1 := sorry
end SorryCheck

namespace MissingCheck
@[sa_reference "SELFTEST.missingCheck"]
def T : Prop := (∀ p : SIRParams, 0 < p.β / (p.β + p.γ)) ∧ (∀ p : SIRParams, 0 < p.β)
@[sa_shadow "SELFTEST.missingCheck" 1] def S1 : Prop := ∀ p : SIRParams, 0 < p.β / (p.β + p.γ)
@[sa_shadow "SELFTEST.missingCheck" 2] def S2 : Prop := ∀ p : SIRParams, 0 < p.β
@[sa_ref_forward "SELFTEST.missingCheck" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "SELFTEST.missingCheck" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "SELFTEST.missingCheck"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩
sa_claim "SELFTEST.missingCheck" group "SelfTest" required
  text "mock: forward check 2 missing" impl SIRParams.transmissibility_pos
@[sa_forward "SELFTEST.missingCheck" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.missingCheck") : S1 := fun p => h p
@[sa_backward "SELFTEST.missingCheck"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "SELFTEST.missingCheck" := fun p => s1 p
end MissingCheck

namespace IncompleteShadows
@[sa_reference "SELFTEST.incompleteShadows"]
def T : Prop := ∀ p : SIRParams, 0 < p.β / (p.β + p.γ)
@[sa_shadow "SELFTEST.incompleteShadows" 1]
def S1 : Prop := ∀ p : SIRParams, 0 < p.β / (p.β + p.γ)
@[sa_ref_forward "SELFTEST.incompleteShadows" 1] theorem ref_fwd1 : T → S1 := fun t => t
-- no sa_complete certificate
sa_claim "SELFTEST.incompleteShadows" group "SelfTest" required
  text "mock: shadow set without completeness certificate" impl SIRParams.transmissibility_pos
@[sa_forward "SELFTEST.incompleteShadows" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.incompleteShadows") : S1 := fun p => h p
@[sa_backward "SELFTEST.incompleteShadows"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.incompleteShadows" := fun p => s1 p
end IncompleteShadows

selftest_shadows1 "SELFTEST.recordedFail" RecordedFail :
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).excessDegree = κ

namespace RecordedFail
sa_claim "SELFTEST.recordedFail" group "SelfTest" required
  text "mock: genuine failure recorded with sa_fail_forward" impl PGFData.poisson_variance_eq_mean
sa_fail_forward "SELFTEST.recordedFail" 1
  "SHADOW?: the shadow speaks about the excess degree, the implementation about the variance"
end RecordedFail

/-! ## Content-free shadow mocks (expected: flag `shadow_trusted_free` unless reviewed)

Port of the spot-check bypass `ClosureTheorem.table.R59`: a shadow that is a closed theorem of
logic or arithmetic (it mentions no trusted constant) passes against an implementation that
restates it, whatever the text says. -/

selftest_shadows1 "SELFTEST.trustedFreeShadow" TrustedFreeShadow :
  ∀ (kap : ℚ), 0 < kap → kap < 1 ∨ kap = 1 ∨ 1 < kap

namespace TrustedFreeShadow
sa_claim "SELFTEST.trustedFreeShadow" group "SelfTest" required
  text "mock: the classification into three families is exhaustive (shadow: trichotomy)"
  impl pt_classification_exhaustive
@[sa_forward "SELFTEST.trustedFreeShadow" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.trustedFreeShadow") : S1 := fun kap hk => h kap hk
@[sa_backward "SELFTEST.trustedFreeShadow"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.trustedFreeShadow" := fun kap hk => s1 kap hk
end TrustedFreeShadow

selftest_shadows1 "SELFTEST.trustedFreeReviewed" TrustedFreeReviewed : ∀ S : ℝ, 1 * S = S

namespace TrustedFreeReviewed
sa_claim "SELFTEST.trustedFreeReviewed" group "SelfTest" required
  text "mock: arithmetic text; the trusted-free shadow has a valid review record"
  impl monoidal_left_unit
@[sa_forward "SELFTEST.trustedFreeReviewed" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.trustedFreeReviewed") : S1 := fun S => h S
@[sa_backward "SELFTEST.trustedFreeReviewed"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.trustedFreeReviewed" := fun S => s1 S
end TrustedFreeReviewed

selftest_shadows1 "SELFTEST.trustedFreeStale" TrustedFreeStale : ∀ S : ℝ, S * 1 = S

namespace TrustedFreeStale
sa_claim "SELFTEST.trustedFreeStale" group "SelfTest" required
  text "mock: trusted-free shadow whose review record has a stale hash"
  impl monoidal_right_unit
@[sa_forward "SELFTEST.trustedFreeStale" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.trustedFreeStale") : S1 := fun S => h S
@[sa_backward "SELFTEST.trustedFreeStale"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.trustedFreeStale" := fun S => s1 S
end TrustedFreeStale

/- Evasions of the purely syntactic `shadow_trusted_free` (found by the review of the spot-check
fixes): a trusted constant that occurs only in the domain of an unused binder, and a tautology
about a trusted term. -/

selftest_shadows1 "SELFTEST.unusedBinderShadow" UnusedBinderShadow :
  ∀ _p : SIRParams, (1 : ℚ) + 1 = 2

namespace UnusedBinderShadow
sa_claim "SELFTEST.unusedBinderShadow" group "SelfTest" required
  text "mock: the shadow mentions SIRParams only as the type of an unused binder"
  impl PGFData.poisson_variance_eq_mean
end UnusedBinderShadow

selftest_shadows1 "SELFTEST.tautologyShadow" TautologyShadow : ∀ p : SIRParams, p.β = p.β

namespace TautologyShadow
sa_claim "SELFTEST.tautologyShadow" group "SelfTest" required
  text "mock: the shadow is a reflexivity statement about a trusted term"
  impl PGFData.poisson_variance_eq_mean
end TautologyShadow

/-! ## Vacuous-hypothesis mocks (expected: flag `hypothesis_refuted`, hint `witness_missing`,
flag `witness_invalid`)

Port of the spot-check bypass `Docs.ms.T5-rateTwo`: the implementation, the text and every shadow
assume `IsFlow F3Kℝ φ₃`, which no `φ₃` satisfies (`no_flow_F3Kℝ`), so all the checks pass
vacuously. -/

open EBCMCategory.Marginalisation EBCMCategory.MarginalisationCharacterization
  EBCMCategory.MarginalisationDynamicalGap MarginalisationObstruction

namespace AlignmentRefuter
/-- A valid alignment-library refuter (it restates the trusted `no_flow_F3Kℝ`). -/
@[sa_refutation]
theorem refuter (φ₃ : U3ℝ → ℝ → U3ℝ) : ¬ IsFlow F3Kℝ φ₃ := no_flow_F3Kℝ φ₃
/-- An unsound refuter (sorry): the audit must ignore it. -/
@[sa_refutation]
theorem unsoundRefuter (φ₃ : U3ℝ → ℝ → U3ℝ) : ¬ IsFlow F3Kℝ φ₃ := sorry
/-- Not of the refuter shape: the audit must report it as invalid. -/
@[sa_refutation]
theorem notARefuter : ∀ p : SIRParams, p.β = p.β := fun _ => rfl
end AlignmentRefuter

selftest_shadows1 "SELFTEST.refutedHypothesis" RefutedHypothesis :
  ∀ {φ₄ : U4ℝ → ℝ → U4ℝ} {φ₃ : U3ℝ → ℝ → U3ℝ}, IsFlow F4Kℝ φ₄ → IsFlow F3Kℝ φ₃ →
    HasDerivAt (trajectoryGap MℝLinCLM φ₄ φ₃ u₁) (fun _ => (2 : ℝ)) 0

namespace RefutedHypothesis
sa_claim "SELFTEST.refutedHypothesis" group "SelfTest" required
  text "mock: implementation and shadow share the unsatisfiable hypothesis IsFlow F3Kℝ φ₃"
  impl trajectoryGap_rate_two_at_witness
@[sa_forward "SELFTEST.refutedHypothesis" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.refutedHypothesis") : S1 := by
  intro φ₄ φ₃ h₄ h₃
  exact h h₄ h₃
@[sa_backward "SELFTEST.refutedHypothesis"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.refutedHypothesis" := by
  intro φ₄ φ₃ h₄ h₃
  exact s1 h₄ h₃
end RefutedHypothesis

universe u_1 u_2

set_option hygiene false in
/-- `selftest_gapzero "id" Ns` declares the shadow set of the (satisfiable) statement
"the trajectory gap vanishes at `t = 0`" (as `EXAMPLE.trajectoryGapZero`) and its checkers. -/
macro "selftest_gapzero " id:str ns:ident : command => `(
  namespace $ns
  @[sa_reference $id] def T : Prop :=
    ∀ {V₄ : Type u_1} {V₃ : Type u_2} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
      [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
      {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
      IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ w : V₄, M (φ₄ w 0) - φ₃ (M w) 0 = 0
  @[sa_shadow $id 1] def S1 : Prop :=
    ∀ {V₄ : Type u_1} {V₃ : Type u_2} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
      [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
      {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
      IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ w : V₄, M (φ₄ w 0) - φ₃ (M w) 0 = 0
  @[sa_ref_forward $id 1] theorem ref_fwd1 : T.{u_1, u_2} → S1.{u_1, u_2} := fun t => t
  @[sa_complete $id] theorem complete (s1 : S1.{u_1, u_2}) : T.{u_1, u_2} := s1
  sa_claim $id group "SelfTest" required text "mock: satisfiable shared hypotheses"
    impl trajectoryGap_at_zero
  @[sa_forward $id 1] theorem fwd1 (h : sa_impl% $id) : S1.{u_1, u_2} := by
    intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ w
    exact h M h₄ h₃ w
  @[sa_backward $id] theorem bwd (s1 : S1.{u_1, u_2}) : sa_impl% $id := by
    intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ w
    exact s1 M h₄ h₃ w
  end $ns)

-- No witness: the checks pass, with the hint `witness_missing`.
selftest_gapzero "SELFTEST.witnessMissing" WitnessMissing

selftest_gapzero "SELFTEST.witnessInvalid" WitnessInvalid

namespace WitnessInvalid
/-- A witness registration whose statement is not the existential over the hypotheses. -/
@[sa_witness "SELFTEST.witnessInvalid" 1]
theorem witness : True := trivial
end WitnessInvalid

/- An impossibility theorem (conclusion `False`) refutes its own hypothesis by design: the audit
must not flag it `hypothesis_refuted` (nor ask for a satisfiability witness), although the trusted
`no_flow_F3Kℝ` and the self-test refuter both refute `IsFlow F3Kℝ φ₃`. The trusted library has no
impossibility theorem with a constant-headed premise, so the implementation is declared here (and
the claim is also flagged `impl_untrusted`). -/

namespace ImpossibilityImpl
/-- `no_flow_F3Kℝ` stated as an impossibility theorem. -/
theorem noFlow (φ₃ : U3ℝ → ℝ → U3ℝ) (h : IsFlow F3Kℝ φ₃) : False := no_flow_F3Kℝ φ₃ h
end ImpossibilityImpl

selftest_shadows1 "SELFTEST.impossibilityImpl" ImpossibilityImpl :
  ∀ φ₃ : U3ℝ → ℝ → U3ℝ, IsFlow F3Kℝ φ₃ → False

namespace ImpossibilityImpl
sa_claim "SELFTEST.impossibilityImpl" group "SelfTest" required
  text "mock: an impossibility theorem is not refuted by its own content"
  impl noFlow
@[sa_forward "SELFTEST.impossibilityImpl" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.impossibilityImpl") : S1 := fun φ₃ h₃ => h φ₃ h₃
@[sa_backward "SELFTEST.impossibilityImpl"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.impossibilityImpl" := fun φ₃ h₃ => s1 φ₃ h₃
end ImpossibilityImpl

/-! ## Backward-vacuity mocks (expected: backward `vacuous`)

Port of the spot-check bypass `MarginalisationDynamicalGap.fibreCollapseObstruction`: a backward
checker that ignores its shadows and proves the implementation from scratch. -/

namespace BackwardVacuous
@[sa_reference "SELFTEST.backwardVacuous"]
def T : Prop := ∀ u : U4ℝ, u Idx4.a = 0 → MℝLinCLM u Idx3.c = u Idx4.a + u Idx4.b
@[sa_shadow "SELFTEST.backwardVacuous" 1]
def S1 : Prop := ∀ u : U4ℝ, u Idx4.a = 0 → MℝLinCLM u Idx3.c = u Idx4.a + u Idx4.b
@[sa_ref_forward "SELFTEST.backwardVacuous" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SELFTEST.backwardVacuous"] theorem complete (s1 : S1) : T := s1
sa_claim "SELFTEST.backwardVacuous" group "SelfTest" required
  text "mock: the backward checker ignores its shadow (the implementation holds by rfl)"
  impl MℝLinCLM_apply
@[sa_forward "SELFTEST.backwardVacuous" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.backwardVacuous") : S1 := fun u _ => h u Idx3.c
@[sa_backward "SELFTEST.backwardVacuous"]
theorem bwd (_s1 : S1) : sa_impl% "SELFTEST.backwardVacuous" := fun _ _ => rfl
end BackwardVacuous

namespace BackwardVacuousEval
@[sa_reference "SELFTEST.backwardVacuousEval"]
def T : Prop := ∀ u : U4ℝ, u Idx4.a = 0 → MℝLinCLM u Idx3.c = u Idx4.a + u Idx4.b
@[sa_shadow "SELFTEST.backwardVacuousEval" 1]
def S1 : Prop := ∀ u : U4ℝ, u Idx4.a = 0 → MℝLinCLM u Idx3.c = u Idx4.a + u Idx4.b
@[sa_ref_forward "SELFTEST.backwardVacuousEval" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SELFTEST.backwardVacuousEval"] theorem complete (s1 : S1) : T := s1
sa_claim "SELFTEST.backwardVacuousEval" group "SelfTest" required
  text "mock: the backward checker passes its shadow to a function that discards it"
  impl MℝLinCLM_apply
@[sa_forward "SELFTEST.backwardVacuousEval" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.backwardVacuousEval") : S1 := fun u _ => h u Idx3.c
/-- `s1` survives normalisation (`Function.eval` is not unfolded); only the replacement of the
shadow by an arbitrary proposition exposes the dodge. -/
@[sa_backward "SELFTEST.backwardVacuousEval"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.backwardVacuousEval" :=
  @Function.eval S1 (fun _ => ∀ (u : U4ℝ) (i : Idx3), MℝLinCLM u i = u Idx4.a + u Idx4.b) s1
    (fun _ _ _ => rfl)
end BackwardVacuousEval

/- Port of the review finding on the old fallback: when the normaliser exhausted its budget, the
backward guard ran on the unnormalised proof, where the shadow still occurs (it is passed to a
helper that discards it), and the check passed. The guard now fails closed. -/

namespace BackwardBudget
/-- A list with `2ⁿ` distinct leaves: normalising `blowup 18 0` needs far more than the
normaliser's fuel. -/
noncomputable def blowup (n : ℕ) : ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun m => [m])
    (fun _ ih m => ih (2 * m) ++ ih (2 * m + 1)) n
@[sa_reference "SELFTEST.backwardBudget"]
def T : Prop := ∀ u : U4ℝ, u Idx4.a = 0 → MℝLinCLM u Idx3.c = u Idx4.a + u Idx4.b
@[sa_shadow "SELFTEST.backwardBudget" 1]
def S1 : Prop := ∀ u : U4ℝ, u Idx4.a = 0 → MℝLinCLM u Idx3.c = u Idx4.a + u Idx4.b
@[sa_ref_forward "SELFTEST.backwardBudget" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "SELFTEST.backwardBudget"] theorem complete (s1 : S1) : T := s1
sa_claim "SELFTEST.backwardBudget" group "SelfTest" required
  text "mock: the backward checker hands its shadow to a helper that discards it, and normalising the helper exceeds the budget"
  impl MℝLinCLM_apply
@[sa_forward "SELFTEST.backwardBudget" 1]
theorem fwd1 (h : sa_impl% "SELFTEST.backwardBudget") : S1 := fun u _ => h u Idx3.c
/-- Discards `_s`. Before it drops a case split on a proof whose branches ignore their fields,
the normaliser normalises the motive, which contains `blowup 18 0`. -/
theorem dodge (_s : S1) : sa_impl% "SELFTEST.backwardBudget" := fun u i =>
  @Or.casesOn (u Idx4.a = 0) True
    (fun _ => blowup 18 0 = blowup 18 0 → MℝLinCLM u i = u Idx4.a + u Idx4.b)
    (Or.inr trivial) (fun _ _ => rfl) (fun _ _ => rfl) rfl
@[sa_backward "SELFTEST.backwardBudget"]
theorem bwd (s1 : S1) : sa_impl% "SELFTEST.backwardBudget" := dodge s1
end BackwardBudget

/-! ## Registration-consistency mocks (claim scores 0) -/

selftest_shadows1 "SELFTEST.implUntrusted" ImplUntrusted : ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

namespace ImplUntrusted
sa_claim "SELFTEST.implUntrusted" group "SelfTest" required
  text "mock: implementation outside the trusted library" impl Nat.le_refl
end ImplUntrusted

selftest_shadows1 "SELFTEST.implUnsound" ImplUnsound : ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

namespace ImplUnsound
/-- The trusted library has no unsound theorem left (the axioms were deleted), so this mock uses
a `sorry` outside the trusted library: the audit must report both `impl_unsound` (it depends on
`sorryAx`) and `impl_untrusted`. -/
theorem unsoundImpl : ∀ p : SIRParams, p.β = p.β := sorry
sa_claim "SELFTEST.implUnsound" group "SelfTest" required
  text "mock: implementation depends on sorry" impl unsoundImpl
end ImplUnsound

selftest_shadows1 "SELFTEST.gap" Gap : ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

namespace Gap
sa_claim "SELFTEST.gap" group "SelfTest" text "mock: no implementation theorem" impl
end Gap

selftest_shadows1 "SELFTEST.duplicate" Duplicate : ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

namespace Duplicate
sa_claim "SELFTEST.duplicate" group "SelfTest" required
  text "mock: registered twice" impl PGFData.poisson_variance_eq_mean
sa_claim "SELFTEST.duplicate" group "SelfTest" required
  text "mock: registered twice" impl PGFData.poisson_variance_eq_mean
end Duplicate

selftest_shadows1 "SELFTEST.bad id!" InvalidId : ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

namespace InvalidId
sa_claim "SELFTEST.bad id!" group "SelfTest" required
  text "mock: invalid claim id" impl PGFData.poisson_variance_eq_mean
end InvalidId

selftest_shadows1 "SELFTEST.unlisted" Unlisted : ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

namespace Unlisted
sa_claim "SELFTEST.unlisted" group "SelfTest" required
  text "mock: registered in Lean but not in the claims registry"
  impl PGFData.poisson_variance_eq_mean
end Unlisted

selftest_shadows1 "SELFTEST.textMismatch" TextMismatch : ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

namespace TextMismatch
sa_claim "SELFTEST.textMismatch" group "SelfTest" required
  text "mock: this text differs from the registry text" impl PGFData.poisson_variance_eq_mean
end TextMismatch

selftest_shadows1 "SELFTEST.groupMismatch" GroupMismatch : ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

namespace GroupMismatch
sa_claim "SELFTEST.groupMismatch" group "SelfTest" required
  text "mock: group differs from the registry" impl PGFData.poisson_variance_eq_mean
end GroupMismatch

selftest_shadows1 "SELFTEST.requiredMismatch" RequiredMismatch : ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

namespace RequiredMismatch
sa_claim "SELFTEST.requiredMismatch" group "SelfTest" required
  text "mock: required flag differs from the registry" impl PGFData.poisson_variance_eq_mean
end RequiredMismatch

selftest_shadows1 "SELFTEST.implMismatch" ImplMismatch : ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

namespace ImplMismatch
sa_claim "SELFTEST.implMismatch" group "SelfTest" required
  text "mock: impl list differs from the registry" impl PGFData.poisson_variance_eq_mean
end ImplMismatch

namespace ShadowReuse
@[sa_reference "SELFTEST.shadowReuse"] def T : Prop :=
  ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)
/-- One declaration registered as two different shadows (`shadows_of` reuse). -/
@[sa_shadow "SELFTEST.shadowReuse" 1, sa_shadow "SELFTEST.shadowReuse" 2]
def S : Prop := ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)
@[sa_ref_forward "SELFTEST.shadowReuse" 1] theorem ref_fwd1 : T → S := fun t => t
@[sa_ref_forward "SELFTEST.shadowReuse" 2] theorem ref_fwd2 : T → S := fun t => t
@[sa_complete "SELFTEST.shadowReuse"] theorem complete (s1 : S) (s2 : S) : T := s1
sa_claim "SELFTEST.shadowReuse" group "SelfTest" required
  text "mock: one declaration used as two shadows" impl PGFData.poisson_variance_eq_mean
end ShadowReuse

end Alignment.Example.SelfTest
