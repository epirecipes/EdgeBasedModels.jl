import Alignment.Registry
import Alignment.Shadows.MarginalisationFunctor

/-!
# Checkers: group `MarginalisationFunctor`

Registrations, checkers and failure records for the implemented claims of
`EBCMCategory/MarginalisationFunctor.lean` (see `Alignment/claims/MarginalisationFunctor.yaml`).

No bridges are needed: the shadows use the trusted `IsFlow`, `IsSolution`, `UniqueFlow` and
`ClosedSystem` directly. The only notational difference between shadows and implementations is
function-level (`⇑M ∘ F₄ = F₃ ∘ ⇑M`) versus pointwise (`∀ u, M (F₄ u) = F₃ (M u)`) commutation,
which `funext` / `congrFun` translate (and `Function.comp` unfolds definitionally).

The trusted theorems are universe-polymorphic in `u_1 u_2` (from `Type _`), with
`V₄ : Type u_1`, `V₃ : Type u_2`. The checkers therefore declare `universe u_1 u_2` and use
`Sᵢ.{u_1, u_2}`.
-/

open EBCMCategory.Marginalisation

/-! ## `MarginalisationFunctor.header.closedNeedNotCommute` -/

namespace Alignment.Shadows.MarginalisationFunctor.header_closedNeedNotCommute

open MarginalisationObstruction

sa_claim "MarginalisationFunctor.header.closedNeedNotCommute" group "MarginalisationFunctor"
  required
  text "For the **closed** dynamics (e.g., Kirkwood at order 4 vs order 3), the diagram [...] need not commute,"
  impl MarginalisationObstruction.kirkwood_marginalisation_obstruction

sa_fail_forward "MarginalisationFunctor.header.closedNeedNotCommute" 1 "impl kirkwood_marginalisation_obstruction is ∃ u : U4, M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u), a statement about the ℚ-valued surrogate U4 = Idx4 → ℚ, U3 = Idx3 → ℚ, where M_witness is a plain function (not a continuous linear map) and F4_Kirkwood/F3_Kirkwood are not ClosedSystem fields over real normed spaces. S1 is ¬ ∀ (V₄ V₃ : Type) real normed spaces, M : V₄ →L[ℝ] V₃, C₄ C₃ : ClosedSystem, ⇑M ∘ C₄.F = C₃.F ∘ ⇑M. The ℚ surrogate is not an instance of that universal (U4, U3 carry no real normed-space structure), so the impl supplies no counterexample to it; refuting the universal needs a separate real-valued counterexample (e.g. M = 0, C₃.F constant 1) and library facts such as (0 : ℝ) ≠ 1, which the impl does not provide."
sa_fail_forward "MarginalisationFunctor.header.closedNeedNotCommute" 2 "impl kirkwood_marginalisation_obstruction is an algebraic (right-hand-side) non-commutation ∃ u : U4, M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u) on the ℚ-valued surrogate; it has no flows at all. S2 is the trajectory-level non-commutation ¬ ∀ (V₄ V₃ : Type) real normed spaces, M : V₄ →L[ℝ] V₃, closed systems with flows φ₄ φ₃ (IsFlow), ∀ w t, M (φ₄ w t) = φ₃ (M w) t. The ℚ surrogate is not an instance (no real normed structure, no IsFlow), and the impl states nothing about trajectories, so S2 does not follow from it."

/-- Forward 3: the impl's witness `u` refutes the function equality at `u` (`congrFun`, with
`Function.comp` unfolding definitionally). -/
@[sa_forward "MarginalisationFunctor.header.closedNeedNotCommute" 3]
theorem fwd3 (h : sa_impl% "MarginalisationFunctor.header.closedNeedNotCommute") : S3 :=
  fun heq => Exists.elim h (fun u hu => hu (congrFun heq u))

sa_fail_backward "MarginalisationFunctor.header.closedNeedNotCommute" "impl is the constructive existential ∃ u : U4, M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u). The only shadow about the Kirkwood surrogate is S3 : ¬ (M_witness ∘ F4_Kirkwood = F3_Kirkwood ∘ M_witness); S1 and S2 concern real normed spaces and say nothing about U4/U3. S3 ⇒ impl is classically valid (funext plus ¬∀ ⇒ ∃¬), but ¬∀ ⇒ ∃¬ needs Classical (not_forall / by_contra), which structural proofs forbid. The only other route is to re-prove the impl from scratch with the concrete witness u = (1, 3), which would not use the shadows. Same situation as Obstructions.header.kirkwoodHierarchyInconsistent."

end Alignment.Shadows.MarginalisationFunctor.header_closedNeedNotCommute

/-! ## header.T1 (the shadows state the two directions in the text's order) -/
namespace Alignment.Shadows.MarginalisationFunctor.header_T1

universe u_1 u_2

sa_claim "MarginalisationFunctor.header.T1" group "MarginalisationFunctor" required
  text "we prove (Theorem T1) the precise dynamical characterisation, for systems with global flows `φ₄`, `φ₃` and unique solutions of `F₃`: *Trajectory-level marginalisation* `M ∘ φ₄(·,t) = φ₃(M·, t)` for all `(u, t)` is **equivalent** to *infinitesimal* marginalisation `M ∘ F₄ = F₃ ∘ M`."
  impl EBCMCategory.Marginalisation.dynamic_marginalisation_iff_equivariance

@[sa_forward "MarginalisationFunctor.header.T1" 1]
theorem fwd1 (h : sa_impl% "MarginalisationFunctor.header.T1") : S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hu
  exact (h M F₄ F₃ h₄ h₃ hu).mpr

@[sa_forward "MarginalisationFunctor.header.T1" 2]
theorem fwd2 (h : sa_impl% "MarginalisationFunctor.header.T1") : S2.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hu
  exact (h M F₄ F₃ h₄ h₃ hu).mp

@[sa_backward "MarginalisationFunctor.header.T1"]
theorem bwd (s1 : S1.{u_1, u_2}) (s2 : S2.{u_1, u_2}) :
    sa_impl% "MarginalisationFunctor.header.T1" := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hu
  exact ⟨s2 M F₄ F₃ φ₄ φ₃ h₄ h₃ hu, s1 M F₄ F₃ φ₄ φ₃ h₄ h₃ hu⟩

/-- Satisfiability witness for the shared hypotheses `IsFlow F₄ φ₄`, `IsFlow F₃ φ₃` and
`UniqueFlow F₃`: the zero fields on `ULift ℝ` and on `PUnit` with constant flows; uniqueness on
`PUnit` holds because all curves into a subsingleton are equal. -/
@[sa_witness "MarginalisationFunctor.header.T1" 1]
theorem witness :
    ∃ (V₄ : Type u_1) (V₃ : Type u_2) (_ : NormedAddCommGroup V₄) (_ : NormedSpace ℝ V₄)
      (_ : NormedAddCommGroup V₃) (_ : NormedSpace ℝ V₃) (_ : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄)
      (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃) (_ : IsFlow F₄ φ₄)
      (_ : IsFlow F₃ φ₃) (_ : UniqueFlow F₃), True :=
  ⟨ULift ℝ, PUnit, inferInstance, inferInstance, inferInstance, inferInstance, 0,
    fun _ => 0, fun _ => 0, fun v _ => v, fun v _ => v,
    ⟨fun _ => rfl, fun v t => hasDerivAt_const t v⟩,
    ⟨fun _ => rfl, fun v t => hasDerivAt_const t v⟩,
    fun _ _ _ _ _ => funext fun _ => Subsingleton.elim _ _, trivial⟩

end Alignment.Shadows.MarginalisationFunctor.header_T1

/-! ## RM1

S2 follows from the implementation and the uniqueness hypothesis: `UniqueFlow F₃` applied to the
given solution and to the pushforward solution of `h`. -/
namespace Alignment.Shadows.MarginalisationFunctor.RM1

universe u_1 u_2

sa_claim "MarginalisationFunctor.RM1" group "MarginalisationFunctor" required
  text "**Result M1.** Pushing a flow of `F₄` through a continuous linear `M` gives a solution of `F₃` through `M u` whenever the RHS commute. It is *the* solution only if solutions of `F₃` are unique."
  impl EBCMCategory.Marginalisation.pushforward_isSolution

@[sa_forward "MarginalisationFunctor.RM1" 1]
theorem fwd1 (h : sa_impl% "MarginalisationFunctor.RM1") : S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ h₄ hc w
  exact h M F₄ F₃ hc h₄ w

@[sa_forward "MarginalisationFunctor.RM1" 2]
theorem fwd2 (h : sa_impl% "MarginalisationFunctor.RM1") : S2.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ h₄ hc hu w ψ hψ
  exact hu (M w) ψ (fun t => M (φ₄ w t)) hψ (h M F₄ F₃ hc h₄ w)

sa_fail_forward "MarginalisationFunctor.RM1" 3 "impl pushforward_isSolution states only that the pushforward is a solution. It does not exhibit a system without uniqueness in which another solution of F₃ through M w exists (S3, the text's 'It is the solution only if solutions of F₃ are unique'). A witness needs a non-Lipschitz field and real analysis that impl does not provide."

@[sa_backward "MarginalisationFunctor.RM1"]
theorem bwd (s1 : S1.{u_1, u_2}) (_s2 : S2.{u_1, u_2}) (_s3 : S3) :
    sa_impl% "MarginalisationFunctor.RM1" := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ hc φ₄ h₄ u
  exact s1 M F₄ F₃ φ₄ h₄ hc u

/-- Satisfiability witness for the hypotheses of `pushforward_isSolution` (commuting right-hand
sides and `IsFlow F₄ φ₄`): zero fields on `ULift ℝ`, `M = 0`, constant flow. -/
@[sa_witness "MarginalisationFunctor.RM1" 1]
theorem witness :
    ∃ (V₄ : Type u_1) (V₃ : Type u_2) (_ : NormedAddCommGroup V₄) (_ : NormedSpace ℝ V₄)
      (_ : NormedAddCommGroup V₃) (_ : NormedSpace ℝ V₃) (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄)
      (F₃ : V₃ → V₃) (_ : ∀ u, M (F₄ u) = F₃ (M u)) (φ₄ : V₄ → ℝ → V₄) (_ : IsFlow F₄ φ₄), True :=
  ⟨ULift ℝ, ULift ℝ, inferInstance, inferInstance, inferInstance, inferInstance, 0,
    fun _ => 0, fun _ => 0, fun _ => rfl, fun v _ => v,
    ⟨fun _ => rfl, fun v t => hasDerivAt_const t v⟩, trivial⟩

end Alignment.Shadows.MarginalisationFunctor.RM1

/-! ## `MarginalisationFunctor.RM2` -/

namespace Alignment.Shadows.MarginalisationFunctor.RM2

universe u_1 u_2

sa_claim "MarginalisationFunctor.RM2" group "MarginalisationFunctor" required
  text "**Result M2 (→).** Infinitesimal commutation `M ∘ F₄ = F₃ ∘ M` and a unique flow for `F₃` imply trajectory commutation."
  impl EBCMCategory.Marginalisation.traj_commute_of_rhs_commute

@[sa_forward "MarginalisationFunctor.RM2" 1]
theorem fwd1 (h : sa_impl% "MarginalisationFunctor.RM2") : S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ hc h₃ hu
  exact h M F₄ F₃ h₄ h₃ hu (fun w => congrFun hc w)

@[sa_backward "MarginalisationFunctor.RM2"]
theorem bwd (s1 : S1.{u_1, u_2}) : sa_impl% "MarginalisationFunctor.RM2" := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hu hc
  exact s1 M h₄ (funext hc) h₃ hu

end Alignment.Shadows.MarginalisationFunctor.RM2

/-! ## `MarginalisationFunctor.RM3` -/

namespace Alignment.Shadows.MarginalisationFunctor.RM3

universe u_1 u_2

sa_claim "MarginalisationFunctor.RM3" group "MarginalisationFunctor" required
  text "**Result M3 (←).** Trajectory commutation implies infinitesimal commutation, by differentiating at `t = 0`."
  impl EBCMCategory.Marginalisation.rhs_commute_of_traj_commute

@[sa_forward "MarginalisationFunctor.RM3" 1]
theorem fwd1 (h : sa_impl% "MarginalisationFunctor.RM3") : S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ htr
  exact funext (fun w => h M F₄ F₃ h₄ h₃ htr w)

@[sa_backward "MarginalisationFunctor.RM3"]
theorem bwd (s1 : S1.{u_1, u_2}) : sa_impl% "MarginalisationFunctor.RM3" := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ htr w
  exact congrFun (s1 M h₄ h₃ htr) w

end Alignment.Shadows.MarginalisationFunctor.RM3

/-! ## `MarginalisationFunctor.RM4a` -/

namespace Alignment.Shadows.MarginalisationFunctor.RM4a

universe u_1 u_2

sa_claim "MarginalisationFunctor.RM4a" group "MarginalisationFunctor" required
  text "**Result M4 — Theorem T1 (Equivariance).** The diagram [...] commutes infinitesimally **iff** it commutes along all trajectories (under the standing flow / uniqueness hypotheses)."
  impl EBCMCategory.Marginalisation.dynamic_marginalisation_iff_equivariance

@[sa_forward "MarginalisationFunctor.RM4a" 1]
theorem fwd1 (h : sa_impl% "MarginalisationFunctor.RM4a") : S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hu hinf
  exact (h M F₄ F₃ h₄ h₃ hu).mp (fun w => congrFun hinf w)

@[sa_forward "MarginalisationFunctor.RM4a" 2]
theorem fwd2 (h : sa_impl% "MarginalisationFunctor.RM4a") : S2.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hu htr
  exact funext (fun w => (h M F₄ F₃ h₄ h₃ hu).mpr htr w)

@[sa_backward "MarginalisationFunctor.RM4a"]
theorem bwd (s1 : S1.{u_1, u_2}) (s2 : S2.{u_1, u_2}) :
    sa_impl% "MarginalisationFunctor.RM4a" := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hu
  exact ⟨fun hinf => s1 M h₄ h₃ hu (funext hinf),
    fun htr w => congrFun (s2 M h₄ h₃ hu htr) w⟩

end Alignment.Shadows.MarginalisationFunctor.RM4a

/-! ## `MarginalisationFunctor.RM4b` -/

namespace Alignment.Shadows.MarginalisationFunctor.RM4b

universe u_1 u_2

sa_claim "MarginalisationFunctor.RM4b" group "MarginalisationFunctor" required
  text "The intended use is contrapositive: **failure** of trajectory marginalisation `M · u₄(t) = u₃(t)` is detectable from the algebraic failure of `M ∘ F₄ = F₃ ∘ M`, which is checked by Theorem T2."
  impl EBCMCategory.Marginalisation.rhs_commute_of_traj_commute

/-- Forward 1 (flows only): the contrapositive of the impl. -/
@[sa_forward "MarginalisationFunctor.RM4b" 1]
theorem fwd1 (h : sa_impl% "MarginalisationFunctor.RM4b") : S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hninf htr
  exact hninf (funext (fun w => h M F₄ F₃ h₄ h₃ htr w))

/-- Forward 2 (flows plus `UniqueFlow F₃`): the same contrapositive; uniqueness is unused. -/
@[sa_forward "MarginalisationFunctor.RM4b" 2]
theorem fwd2 (h : sa_impl% "MarginalisationFunctor.RM4b") : S2.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ _hu hninf htr
  exact hninf (funext (fun w => h M F₄ F₃ h₄ h₃ htr w))

sa_fail_forward "MarginalisationFunctor.RM4b" 3 "impl rhs_commute_of_traj_commute is the general implication trajectory ⇒ infinitesimal commutation for continuous linear M between real normed spaces with flows. It says nothing about the Theorem T2 Kirkwood witness. S3 is ¬ (M_witness ∘ F4_Kirkwood = F3_Kirkwood ∘ M_witness) on the ℚ-valued surrogate U4/U3, which is not an instance of the impl's setting (no real normed structure, M_witness not continuous linear, no flows). The algebraic failure lives in MarginalisationObstruction.kirkwood_marginalisation_obstruction, which the registry lists only as supporting, not as impl, so S3 does not follow from the impl."

sa_fail_backward "MarginalisationFunctor.RM4b" "impl rhs_commute_of_traj_commute is the direct implication (∀ u t, M (φ₄ u t) = φ₃ (M u) t) ⇒ ∀ u, M (F₄ u) = F₃ (M u). S1 and S2 state only its contrapositive, ¬ (⇑M ∘ F₄ = F₃ ∘ ⇑M) ⇒ ¬ ∀ w t, …, and S3 concerns only the ℚ surrogate. From trajectory commutation, S1 yields ¬¬ (⇑M ∘ F₄ = F₃ ∘ ⇑M). Recovering the equation itself needs double-negation elimination (Classical.byContradiction), which structural proofs forbid. The claim text states only the contrapositive, so this is a classical-vs-constructive gap: the impl is intuitionistically stronger than the text."

end Alignment.Shadows.MarginalisationFunctor.RM4b

/-! ## rhsCommuteOfLocalTrajCommute (`IsLocalSolution F v₀ δ ψ` unfolds to
`0 < δ ∧ ψ 0 = v₀ ∧ ∀ t, |t| < δ → HasDerivAt ψ (F (ψ t)) t`) -/
namespace Alignment.Shadows.MarginalisationFunctor.rhsCommuteOfLocalTrajCommute

universe u_1 u_2

sa_claim "MarginalisationFunctor.rhsCommuteOfLocalTrajCommute" group "MarginalisationFunctor" required
  text "**Result M3, local form.** If local solutions `ψ₄` of `F₄` through `u` and `ψ₃` of `F₃` through `M u` satisfy `M (ψ₄ t) = ψ₃ t` for all `|t| < δ` (with `δ > 0`), then `M (F₄ u) = F₃ (M u)`. No global flow and no uniqueness is assumed."
  impl EBCMCategory.Marginalisation.rhs_commute_of_local_traj_commute

@[sa_forward "MarginalisationFunctor.rhsCommuteOfLocalTrajCommute" 1]
theorem fwd1 (h : sa_impl% "MarginalisationFunctor.rhsCommuteOfLocalTrajCommute") :
    S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ u ψ₄ ψ₃ δ hδ h40 h30 hd4 hd3 htraj
  exact h M F₄ F₃ u ⟨hδ, h40, hd4⟩ ⟨hδ, h30, hd3⟩ hδ htraj

sa_fail_backward "MarginalisationFunctor.rhsCommuteOfLocalTrajCommute" "impl allows three radii: local solutions on |t| < δ₄ and |t| < δ₃ and agreement on |t| < δ. S1 uses one δ for all three. To apply S1 one must shrink to δ' = min(δ, δ₄, δ₃) and transport the hypotheses (lt_min, lt_of_lt_of_le), which are order lemmas, not structural. Mathematically S1 implies impl."

end Alignment.Shadows.MarginalisationFunctor.rhsCommuteOfLocalTrajCommute

/-! ## `MarginalisationFunctor.table.M1` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.MarginalisationFunctor.table_M1

sa_claim "MarginalisationFunctor.table.M1" group "MarginalisationFunctor"
  text "| M1 | pushforward of a flow of `F₄` solves `F₃` if the RHS commute |"
  impl

end Alignment.Shadows.MarginalisationFunctor.table_M1
