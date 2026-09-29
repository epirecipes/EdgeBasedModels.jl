import Alignment.Registry
import Alignment.Example.ExampleShadows
import Mathlib.Tactic.Ring

/-!
# Worked example: claim registration, bridge and checkers (template for `Checks/<Group>.lean`)

The checker author may read everything. For each claim:

1. `sa_claim` with the verbatim `claims.yaml` text and the `impl` list;
2. bridges (`@[sa_bridge "c"]`, any tactics, must not use implementation theorems) where the
   text's notion is not definitionally our definition;
3. forward checkers `(h : sa_impl% "c") : Sᵢ` and one backward checker
   `(s₁ : S₁) … (sₙ : Sₙ) : sa_impl% "c"`, with structural proofs: hypotheses, the logic glue of
   `coreLogicWhitelist`, definitional unfolding (`show`, `change`, `unfold`, `rfl`), and reviewed
   bridges for the claim. No library lemmas, no `simp`/`ring`/`omega`/`decide`/`linarith`.
4. If a check is genuinely false, record `sa_fail_forward "c" i "<reason>"` (or
   `sa_fail_backward`) instead of forcing it.

Checkers must live in the module that runs `sa_claim`. Do not write review records here: an
independent reviewer adds them to `Alignment/ReviewedBridges.lean`.
-/

namespace Alignment.Example.PoissonVariance

sa_claim "EXAMPLE.poissonVariance" group "Example" required
  text "**Result 2.** For Poisson, the variance equals the mean (equidispersion)."
  impl PGFData.poisson_variance_eq_mean

/-- Bridge: our `PGFData.variance` is the text's degree variance ψ''(1) + ψ'(1)(1 − ψ'(1)).
The right-hand side is not definitionally `variance`, so the checkers need this bridge. -/
@[sa_bridge "EXAMPLE.poissonVariance"]
theorem bridge_variance (ψ : PGFData) :
    PGFData.variance ψ = ψ.secondFactorial + ψ.mean * (1 - ψ.mean) := by
  unfold PGFData.variance
  ring

/-- Forward 1: `degVar P` unfolds to the bridge's right-hand side. -/
@[sa_forward "EXAMPLE.poissonVariance" 1]
theorem fwd1 (h : sa_impl% "EXAMPLE.poissonVariance") : S1 :=
  fun κ hκ => (bridge_variance (PGFData.poisson κ hκ)).symm.trans (h κ hκ)

/-- Forward 2: the Poisson PGF's mean is κ by definition, so the same term proves `S2`. -/
@[sa_forward "EXAMPLE.poissonVariance" 2]
theorem fwd2 (h : sa_impl% "EXAMPLE.poissonVariance") : S2 :=
  fun κ hκ => (bridge_variance (PGFData.poisson κ hκ)).symm.trans (h κ hκ)

@[sa_backward "EXAMPLE.poissonVariance"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "EXAMPLE.poissonVariance" :=
  fun κ hκ => (bridge_variance (PGFData.poisson κ hκ)).trans (s1 κ hκ)

end Alignment.Example.PoissonVariance

namespace Alignment.Example.Transmissibility

sa_claim "EXAMPLE.transmissibilityRange" group "Example" required
  text "Transmissibility is positive. [...] Transmissibility is less than 1."
  impl SIRParams.transmissibility_pos SIRParams.transmissibility_lt_one

/-- `SIRParams.transmissibility p` unfolds definitionally to `p.β / (p.β + p.γ)`: no bridge. -/
@[sa_forward "EXAMPLE.transmissibilityRange" 1]
theorem fwd1 (h : sa_impl% "EXAMPLE.transmissibilityRange") : S1 := fun p => h.1 p

@[sa_forward "EXAMPLE.transmissibilityRange" 2]
theorem fwd2 (h : sa_impl% "EXAMPLE.transmissibilityRange") : S2 := fun p => h.2 p

@[sa_backward "EXAMPLE.transmissibilityRange"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "EXAMPLE.transmissibilityRange" :=
  ⟨fun p => s1 p, fun p => s2 p⟩

end Alignment.Example.Transmissibility

namespace Alignment.Example.TrajectoryGap

open EBCMCategory.Marginalisation EBCMCategory.MarginalisationDynamicalGap

sa_claim "EXAMPLE.trajectoryGapZero" group "Example" required
  text "The trajectory gap vanishes at `t = 0`." impl trajectoryGap_at_zero

/-! The implementation's universe parameters are named `u_1 u_2` (from `Type _`); a checker
declares the same names so that `sa_impl%` and the shadow instance `S1.{u_1, u_2}` agree. -/
universe u_1 u_2

@[sa_forward "EXAMPLE.trajectoryGapZero" 1]
theorem fwd1 (h : sa_impl% "EXAMPLE.trajectoryGapZero") : S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ w
  exact h M h₄ h₃ w

@[sa_backward "EXAMPLE.trajectoryGapZero"]
theorem bwd (s1 : S1.{u_1, u_2}) : sa_impl% "EXAMPLE.trajectoryGapZero" := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ w
  exact s1 M h₄ h₃ w

/-- Satisfiability witness for the hypotheses `IsFlow F₄ φ₄` and `IsFlow F₃ φ₃`, which the
implementation and the shadow share: the zero vector field on `ULift ℝ` has the constant flow.
The statement is `∃ x₁ … xₖ, True` over the implementation's binders up to its last hypothesis
(with the implementation's universe names); any tactic may be used. Without it the claim gets
the hint `witness_missing`. -/
@[sa_witness "EXAMPLE.trajectoryGapZero" 1]
theorem witness :
    ∃ (V₄ : Type u_1) (V₃ : Type u_2) (_ : NormedAddCommGroup V₄) (_ : NormedSpace ℝ V₄)
      (_ : NormedAddCommGroup V₃) (_ : NormedSpace ℝ V₃) (_ : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄)
      (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃) (_ : IsFlow F₄ φ₄)
      (_ : IsFlow F₃ φ₃), True :=
  ⟨ULift ℝ, ULift ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0,
    fun _ => 0, fun _ => 0, fun v _ => v, fun v _ => v,
    ⟨fun _ => rfl, fun v t => hasDerivAt_const t v⟩,
    ⟨fun _ => rfl, fun v t => hasDerivAt_const t v⟩, trivial⟩

end Alignment.Example.TrajectoryGap
