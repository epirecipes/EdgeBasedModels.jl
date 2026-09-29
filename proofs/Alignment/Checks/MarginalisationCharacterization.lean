import Alignment.Registry
import Alignment.Shadows.MarginalisationCharacterization

/-!
# Checkers: group `MarginalisationCharacterization`

Registrations, forward / backward checkers and failure records for the claims of
`EBCMCategory/MarginalisationCharacterization.lean`. The shadows are in
`Alignment/Shadows/MarginalisationCharacterization.lean` (written blind).

No bridges are needed. Every shadow is stated directly over the trusted operations
(`Equivariant`, `ClosureFamily`, `ClosureFamily.IsLinear`, `ClosureFamily.IsKirkwoodForm`,
`MℝLin`, `F4Kℝ`, `C4ℝ`, `PGFData.closureKappa`, `IsFlow`, and the T2 witness data
`MarginalisationObstruction.{M_witness, F4_Kirkwood, F3_Kirkwood}`).

Policy used for this group (as in `Checks/Obstructions.lean`). A check counts as proved only when
the shadow is an instance, projection or logical consequence of the implementation's statement,
and `h` supplies the content. The trusted statements are mostly existentials whose witnesses
(`U4ℝ`, `U3ℝ`, `MℝLin`, `C4ℝ`) are visible only in the proof terms. A shadow about the named
witnesses, or a property that the existential does not state (surjectivity of `M`, the `a·b`
component, the witness values), is therefore recorded as failed. Real-number arithmetic
(`(1:ℝ) * 1 = 1`, `(1:ℝ) + 3 = 4 + 0`, …) is not structural and cannot be carried by a bridge,
so a proof from scratch is not possible either.

Proof style for the `kkr_necessary_not_sufficient` checkers. The impl is a 9-fold existential
(ψ, V₄, V₃, four instances, M, C₄). Every nested `obtain`/`Exists.elim` level costs the vacuity
guard's normaliser about twice the level below it, so a direct 8–12-level destructuring exhausts
its budget (`<vacuity guard could not decide>`). The checkers therefore map under the binders with
`Exists.imp` (whitelisted and not unfolded). They use `Exists.elim` only to drop a binder (ψ, or
the eight order-4 binders in two phases of four) or to swap the `AddCommGroup V₃` / `Module ℝ V₄`
binders, whose order differs between impl and shadows.
-/

open EBCMCategory.Marginalisation
open EBCMCategory.MarginalisationCharacterization
open MarginalisationObstruction

universe u_1 u_2

/-! ## `MarginalisationCharacterization.header.T2witness` -/
namespace Alignment.Shadows.MarginalisationCharacterization.header_T2witness

sa_claim "MarginalisationCharacterization.header.T2witness" group "MarginalisationCharacterization"
  required
  text "the witness there shows the diagram fails for one specific Kirkwood-style closure,"
  impl MarginalisationObstruction.kirkwood_marginalisation_obstruction

/-- The impl's point `u` with `M(F₄ u) ≠ F₃(M u)` refutes commutation at every point. -/
@[sa_forward "MarginalisationCharacterization.header.T2witness" 1]
theorem fwd1 (h : sa_impl% "MarginalisationCharacterization.header.T2witness") : S1 := by
  intro hall
  obtain ⟨u, hu⟩ := h
  exact hu (hall u)

sa_fail_backward "MarginalisationCharacterization.header.T2witness" "impl is the constructive existential ∃ u : U4, M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u). S1 is ¬ ∀ w : U4, M_witness (F4_Kirkwood w) = F3_Kirkwood (M_witness w). The two are classically equivalent, but ¬∀ ⇒ ∃¬ needs Classical (not_forall / by_contra), which structural proofs forbid. The only other route is to re-prove the impl from scratch at the concrete witness (a ℚ disequality 6 ≠ 4 obtained by norm_num), which would not use S1. Audit limitation (classical logic), not a meaning gap."

end Alignment.Shadows.MarginalisationCharacterization.header_T2witness

/-! ## `MarginalisationCharacterization.header.T1forces` -/
namespace Alignment.Shadows.MarginalisationCharacterization.header_T1forces

sa_claim "MarginalisationCharacterization.header.T1forces" group "MarginalisationCharacterization" required
  text "and Theorem T1 (`MarginalisationFunctor.lean`) shows that, for systems with global flows, any such algebraic failure forces a dynamical failure of subgraph marginalisation. The T2 witness has no global order-3 flow, so there the local form `rhs_commute_of_local_traj_commute` is the one that applies."
  impl EBCMCategory.Marginalisation.rhs_commute_of_traj_commute

/-- S1 is the contrapositive of the implementation. -/
@[sa_forward "MarginalisationCharacterization.header.T1forces" 1]
theorem fwd1 (h : sa_impl% "MarginalisationCharacterization.header.T1forces") :
    S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hF hT
  exact hF (h M F₄ F₃ h₄ h₃ hT)

sa_fail_forward "MarginalisationCharacterization.header.T1forces" 2 "S2 (the T2 witness F3Kℝ has no global flow) is the trusted theorem MarginalisationDynamicalGap.no_flow_F3Kℝ. It is not in this claim's impl list; impl rhs_commute_of_traj_commute assumes global flows and says nothing about their existence at the witness."

sa_fail_forward "MarginalisationCharacterization.header.T1forces" 3 "S3 (at the witness, local solutions from u₁ and M u₁ do not agree near t = 0) is about the local form rhs_commute_of_local_traj_commute applied at the T2 witness, which is not in this claim's impl list. impl (global flows) does not give it."

sa_fail_backward "MarginalisationCharacterization.header.T1forces" "S1 is the contrapositive of impl. Recovering impl (∀ u, M(F₄ u) = F₃(M u) from trajectory commutation) from S1 gives only ¬¬(∀ u, …) and needs double-negation elimination (Classical.byContradiction), which structural proofs forbid. S2 and S3 are about the witness and do not help. Audit limitation (classical logic), not a meaning gap."

end Alignment.Shadows.MarginalisationCharacterization.header_T1forces

/-! ## `MarginalisationCharacterization.header.T3`

`IsKirkwoodForm` is by definition `∃ u v, C (u + v) ≠ C u + C v`, which gives the shadow's
`¬ ∀ x y, C (x + y) = C x + C y`; the checker maps under the eight existential binders with
`Exists.imp`. -/
namespace Alignment.Shadows.MarginalisationCharacterization.header_T3

sa_claim "MarginalisationCharacterization.header.T3" group "MarginalisationCharacterization" required
  text "T3 — proved here — is an **existential** statement (T3b): *There is a linear marginalisation `M` and a non-additive order-4 closure `C₄` such that no order-3 closure `C₃` makes the diagram commute.*"
  impl EBCMCategory.MarginalisationCharacterization.kirkwood_form_not_equivariant

@[sa_forward "MarginalisationCharacterization.header.T3" 1]
theorem fwd1 (h : sa_impl% "MarginalisationCharacterization.header.T3") : S1 := h

@[sa_forward "MarginalisationCharacterization.header.T3" 2]
theorem fwd2 (h : sa_impl% "MarginalisationCharacterization.header.T3") : S2 :=
  h.imp fun _ => Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ =>
    Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ hc =>
      ⟨fun hall => hc.1.elim fun u hu => hu.elim fun v huv => huv (hall u v), hc.2⟩

@[sa_backward "MarginalisationCharacterization.header.T3"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "MarginalisationCharacterization.header.T3" := s1

end Alignment.Shadows.MarginalisationCharacterization.header_T3

/-! ## `MarginalisationCharacterization.header.interLevel` -/
namespace Alignment.Shadows.MarginalisationCharacterization.header_interLevel

sa_claim "MarginalisationCharacterization.header.interLevel" group "MarginalisationCharacterization" required
  text "T3 below is a different statement: a closure that is exact at the pairwise level constrains nothing at order 4, and the **inter-level marginalisation diagram need not commute**. The formal witness (T3c) only pairs a Poisson record, whose `closureKappa` is 1, with the unrelated surrogate of T3b."
  impl EBCMCategory.MarginalisationCharacterization.kkr_necessary_not_sufficient

sa_fail_forward "MarginalisationCharacterization.header.interLevel" 1 "impl kkr_necessary_not_sufficient is existential: some ψ with closureKappa ψ = 1 (the Poisson record appears only in its proof). S1 (every Poisson record has closureKappa = 1) is universal and does not follow from the existential."

sa_fail_forward "MarginalisationCharacterization.header.interLevel" 2 "impl is existential over V₄, V₃, M, C₄; the T3b surrogate (MℝLin, C4ℝ) appears only in its proof. S2 (no C₃ makes MℝLin intertwine C4ℝ with C₃) is about the named surrogate and does not follow from impl's statement."

sa_fail_backward "MarginalisationCharacterization.header.interLevel" "With the witnesses ψ = poisson 1 (S1), U4ℝ, U3ℝ, MℝLin and C4ℝ (S2), impl still needs C4ℝ.IsKirkwoodForm. That is the trusted lemma C4ℝ_isKirkwoodForm, which a checker may not cite; no shadow states it, and a direct proof needs real arithmetic (1·1 ≠ 0). So impl is stronger than the shadow set by its IsKirkwoodForm conjunct."

end Alignment.Shadows.MarginalisationCharacterization.header_interLevel

/-! ## `MarginalisationCharacterization.header.kkrNotSufficient` -/
namespace Alignment.Shadows.MarginalisationCharacterization.header_kkrNotSufficient

sa_claim "MarginalisationCharacterization.header.kkrNotSufficient" group "MarginalisationCharacterization" required
  text "T3c shows only that a KKR-exact degree record can be paired with an order-4 closure that is **not** equivariant."
  impl EBCMCategory.MarginalisationCharacterization.kkr_necessary_not_sufficient

@[sa_forward "MarginalisationCharacterization.header.kkrNotSufficient" 1]
theorem fwd1 (h : sa_impl% "MarginalisationCharacterization.header.kkrNotSufficient") : S1 :=
  h.imp fun _ hψ =>
    hψ.elim fun _ h => h.elim fun _ h => h.elim fun _ h => h.elim fun _ h =>
      h.elim fun _ h => h.elim fun _ h => h.elim fun _ h => h.elim fun _ hc => hc.1

@[sa_forward "MarginalisationCharacterization.header.kkrNotSufficient" 2]
theorem fwd2 (h : sa_impl% "MarginalisationCharacterization.header.kkrNotSufficient") : S2 :=
  h.elim fun _ hψ =>
    hψ.imp fun _ => Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ =>
      Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ hc => hc.2.2

sa_fail_backward "MarginalisationCharacterization.header.kkrNotSufficient" "impl also asserts that its order-4 closure C₄ is IsKirkwoodForm (non-additive). S2 asserts only the existence of some non-equivariant C₄ and gives no non-additivity, so impl does not follow: impl is stronger than the text ('an order-4 closure that is not equivariant') by that conjunct."

end Alignment.Shadows.MarginalisationCharacterization.header_kkrNotSufficient

/-! ## `MarginalisationCharacterization.table.T3a` -/
namespace Alignment.Shadows.MarginalisationCharacterization.table_T3a

sa_claim "MarginalisationCharacterization.table.T3a" group "MarginalisationCharacterization" required
  text "| T3a | A linear `L₄` admits an equivariant `F₃` iff `L₄(ker M) ⊆ ker M` |"
  impl EBCMCategory.MarginalisationCharacterization.linear_closure_equivariant

sa_fail_forward "MarginalisationCharacterization.table.T3a" 1 "impl linear_closure_equivariant is tautological: its hypothesis h_intertwine is its conclusion Equivariant M L₄ L₃ written out. It says nothing about ker M, so it does not give S1 (an equivariant F₃ forces (ker M).map L₄ ≤ ker M). The row's criterion is linear_admits_equivariant_iff, which is not in this claim's impl list."

sa_fail_forward "MarginalisationCharacterization.table.T3a" 2 "impl (tautological intertwining) needs an intertwining linear L₃ as input. It does not give S2 (L₄(ker M) ⊆ ker M produces some equivariant F₃), which needs a construction of F₃ on the range of M (linear_admits_equivariant_iff, not in impl)."

sa_fail_backward "MarginalisationCharacterization.table.T3a" "impl (∀ M L₄ L₃, (∀ u, M(L₄ u) = L₃(M u)) → Equivariant M L₄ L₃) is its own hypothesis unfolded, provable as fun _ _ _ h => h without any shadow, so a backward checker could only be vacuous."

end Alignment.Shadows.MarginalisationCharacterization.table_T3a

/-! ## `MarginalisationCharacterization.table.T3b` (as `header.T3`) -/
namespace Alignment.Shadows.MarginalisationCharacterization.table_T3b

sa_claim "MarginalisationCharacterization.table.T3b" group "MarginalisationCharacterization" required
  text "| T3b | Some linear `M` and non-additive `C₄` admit no equivariant `C₃` | [...] | | (existential; no `sorry`) |"
  impl EBCMCategory.MarginalisationCharacterization.kirkwood_form_not_equivariant

@[sa_forward "MarginalisationCharacterization.table.T3b" 1]
theorem fwd1 (h : sa_impl% "MarginalisationCharacterization.table.T3b") : S1 := h

@[sa_forward "MarginalisationCharacterization.table.T3b" 2]
theorem fwd2 (h : sa_impl% "MarginalisationCharacterization.table.T3b") : S2 :=
  h.imp fun _ => Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ =>
    Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ hc =>
      ⟨fun hall => hc.1.elim fun u hu => hu.elim fun v huv => huv (hall u v), hc.2⟩

@[sa_backward "MarginalisationCharacterization.table.T3b"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "MarginalisationCharacterization.table.T3b" := s1

end Alignment.Shadows.MarginalisationCharacterization.table_T3b

/-! ## `MarginalisationCharacterization.table.T3c.b` (as `header.kkrNotSufficient`) -/
namespace Alignment.Shadows.MarginalisationCharacterization.table_T3c_b

sa_claim "MarginalisationCharacterization.table.T3c.b" group "MarginalisationCharacterization" required
  text "Corollary: KKR-exactness [...] | | a KKR-exact record pairs with a non-equivariant order-4 closure |"
  impl EBCMCategory.MarginalisationCharacterization.kkr_necessary_not_sufficient

@[sa_forward "MarginalisationCharacterization.table.T3c.b" 1]
theorem fwd1 (h : sa_impl% "MarginalisationCharacterization.table.T3c.b") : S1 :=
  h.imp fun _ hψ =>
    hψ.elim fun _ h => h.elim fun _ h => h.elim fun _ h => h.elim fun _ h =>
      h.elim fun _ h => h.elim fun _ h => h.elim fun _ h => h.elim fun _ hc => hc.1

@[sa_forward "MarginalisationCharacterization.table.T3c.b" 2]
theorem fwd2 (h : sa_impl% "MarginalisationCharacterization.table.T3c.b") : S2 :=
  h.elim fun _ hψ =>
    hψ.imp fun _ => Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ =>
      Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ hc => hc.2.2

sa_fail_backward "MarginalisationCharacterization.table.T3c.b" "impl also asserts that its order-4 closure is IsKirkwoodForm. S2 gives only some non-equivariant order-4 closure, so impl's non-additivity conjunct does not follow; impl is stronger than the table row ('pairs with a non-equivariant order-4 closure')."

end Alignment.Shadows.MarginalisationCharacterization.table_T3c_b

/-! ## `MarginalisationCharacterization.linearClosureEquivariant.a` -/
namespace Alignment.Shadows.MarginalisationCharacterization.linearClosureEquivariant_a

sa_claim "MarginalisationCharacterization.linearClosureEquivariant.a"
  group "MarginalisationCharacterization" required
  text "A linear closure paired with an `M`-compatible linear `L₃` at order 3 yields an equivariant closed RHS"
  impl EBCMCategory.MarginalisationCharacterization.linear_closure_equivariant

/-- Instance of the impl at the linear map `L₄` representing `C₄` (from `IsLinear`): transport
the compatibility hypothesis from `C₄.C` to `L₄`, apply the impl, transport back. -/
@[sa_forward "MarginalisationCharacterization.linearClosureEquivariant.a" 1]
theorem fwd1 (h : sa_impl% "MarginalisationCharacterization.linearClosureEquivariant.a") :
    S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M C₄ L₃ hlin hcompat
  obtain ⟨L₄, hL⟩ := hlin
  have hint : ∀ w, M (L₄ w) = L₃ (M w) := fun w =>
    (congrArg M (hL w)).symm.trans (hcompat w)
  have heq := h M L₄ L₃ hint
  intro w
  exact (congrArg M (hL w)).trans (heq w)

/-- The impl at `L₄` is the shadow at the closure family `⟨fun u => L₄ u⟩`. -/
@[sa_backward "MarginalisationCharacterization.linearClosureEquivariant.a"]
theorem bwd (s1 : S1.{u_1, u_2}) :
    sa_impl% "MarginalisationCharacterization.linearClosureEquivariant.a" := by
  intro V₄ V₃ _ _ _ _ M L₄ L₃ hint
  exact s1 M ⟨fun u => L₄ u⟩ L₃ ⟨L₄, fun _ => rfl⟩ hint

end Alignment.Shadows.MarginalisationCharacterization.linearClosureEquivariant_a

/-! ## `MarginalisationCharacterization.isLinearAdmitsEquivariant` -/
namespace Alignment.Shadows.MarginalisationCharacterization.isLinearAdmitsEquivariant

sa_claim "MarginalisationCharacterization.isLinearAdmitsEquivariant" group "MarginalisationCharacterization" required
  text "**Vacuous; kept for compatibility.** The statement is `∃ F₃, Equivariant M C₄.C F₃ ∨ True`, which holds because of the disjunct `True`; it does not show that an `IsLinear` closure admits an equivariant `F₃`. The correct criterion is `linear_admits_equivariant_iff`: a linear `L₄` admits an equivariant `F₃` iff `L₄` maps `ker M` into `ker M`."
  impl EBCMCategory.MarginalisationCharacterization.isLinear_admits_equivariant

sa_fail_forward "MarginalisationCharacterization.isLinearAdmitsEquivariant" 1 "impl isLinear_admits_equivariant concludes ∃ F₃, Equivariant M C₄.C F₃ ∨ True, which holds through the disjunct True (the text: 'Vacuous; kept for compatibility'). It carries no information, so it cannot give S1 (some IsLinear closure admits no equivariant F₃)."

sa_fail_forward "MarginalisationCharacterization.isLinearAdmitsEquivariant" 2 "S2 (an equivariant F₃ for a linear L₄ forces L₄(ker M) ⊆ ker M) is the forward direction of linear_admits_equivariant_iff, which the text names as the correct criterion and which is not in this claim's impl list. The vacuous impl does not give it."

sa_fail_forward "MarginalisationCharacterization.isLinearAdmitsEquivariant" 3 "S3 (L₄(ker M) ⊆ ker M gives an equivariant F₃) is the reverse direction of linear_admits_equivariant_iff (not in impl). The vacuous impl (… ∨ True) does not give it."

sa_fail_backward "MarginalisationCharacterization.isLinearAdmitsEquivariant" "impl (∃ F₃, … ∨ True) is provable outright as ⟨0, Or.inr trivial⟩ without any shadow, so a backward checker could only be vacuous. The shadows state the content that the text says impl lacks."

end Alignment.Shadows.MarginalisationCharacterization.isLinearAdmitsEquivariant

/-! ## `MarginalisationCharacterization.c4RealIsKirkwoodForm` -/
namespace Alignment.Shadows.MarginalisationCharacterization.c4RealIsKirkwoodForm

sa_claim "MarginalisationCharacterization.c4RealIsKirkwoodForm"
  group "MarginalisationCharacterization" required
  text "The Kirkwood-form predicate holds for `C4ℝ`: the bilinear `a·b` component is non-additive. Witnessed by `u = (1,0)`, `v = (0,1)`: `F₄(u+v) = (1,1)` while `F₄(u) + F₄(v) = (0,1)`."
  impl EBCMCategory.MarginalisationCharacterization.C4ℝ_isKirkwoodForm

@[sa_forward "MarginalisationCharacterization.c4RealIsKirkwoodForm" 1]
theorem fwd1 (h : sa_impl% "MarginalisationCharacterization.c4RealIsKirkwoodForm") : S1 := h

/-- `IsKirkwoodForm` unfolds definitionally to non-additivity. -/
@[sa_forward "MarginalisationCharacterization.c4RealIsKirkwoodForm" 2]
theorem fwd2 (h : sa_impl% "MarginalisationCharacterization.c4RealIsKirkwoodForm") : S2 := by
  unfold ClosureFamily.IsKirkwoodForm at h
  exact h

sa_fail_forward "MarginalisationCharacterization.c4RealIsKirkwoodForm" 3 "impl states only C4ℝ.IsKirkwoodForm, i.e. ∃ u v, C4ℝ.C (u + v) ≠ C4ℝ.C u + C4ℝ.C v (non-additivity somewhere). It says nothing about which component of C4ℝ.C is bilinear, and non-additivity does not imply an a·b component. S3 (∃ i, ∀ w, C4ℝ.C w i = w a * w b) holds only by unfolding C4ℝ / F4Kℝ (⟨Idx4.a, fun _ => rfl⟩), a proof that does not use h."

sa_fail_forward "MarginalisationCharacterization.c4RealIsKirkwoodForm" 4 "impl is the existential ∃ u v, C4ℝ.C (u + v) ≠ C4ℝ.C u + C4ℝ.C v. It does not name the witnesses (1,0), (0,1) (they appear only in the proof) and states no value of C4ℝ.C. S4 (C4ℝ.C (pt 1 0 + pt 0 1) = pt 1 1) is a real-number computation ((1+0)*(0+1) = 1, 0+1 = 1) that follows neither from h nor structurally (no kernel computation on ℝ, no norm_num)."

sa_fail_forward "MarginalisationCharacterization.c4RealIsKirkwoodForm" 5 "impl is the existential ∃ u v, C4ℝ.C (u + v) ≠ C4ℝ.C u + C4ℝ.C v. It does not name the witnesses and states no value of C4ℝ.C. S5 (C4ℝ.C (pt 1 0) + C4ℝ.C (pt 0 1) = pt 0 1) is a real-number computation (1*0 + 0*1 = 0, 0 + 1 = 1) that follows neither from h nor structurally."

sa_fail_forward "MarginalisationCharacterization.c4RealIsKirkwoodForm" 6 "impl is the existential ∃ u v, C4ℝ.C (u + v) ≠ C4ℝ.C u + C4ℝ.C v (C4ℝ.C is definitionally F4Kℝ). It does not name the witnesses and states no value of F4Kℝ. S6 (F4Kℝ (pt 1 0 + pt 0 1) = pt 1 1) is a real-number computation that follows neither from h nor structurally."

sa_fail_forward "MarginalisationCharacterization.c4RealIsKirkwoodForm" 7 "impl is the existential ∃ u v, C4ℝ.C (u + v) ≠ C4ℝ.C u + C4ℝ.C v (C4ℝ.C is definitionally F4Kℝ). It does not name the witnesses and states no value of F4Kℝ. S7 (F4Kℝ (pt 1 0) + F4Kℝ (pt 0 1) = pt 0 1) is a real-number computation that follows neither from h nor structurally."

@[sa_backward "MarginalisationCharacterization.c4RealIsKirkwoodForm"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) (_s5 : S5) (_s6 : S6) (_s7 : S7) :
    sa_impl% "MarginalisationCharacterization.c4RealIsKirkwoodForm" := s1

end Alignment.Shadows.MarginalisationCharacterization.c4RealIsKirkwoodForm

/-! ## `MarginalisationCharacterization.kirkwoodFormNotEquivariant` -/
namespace Alignment.Shadows.MarginalisationCharacterization.kirkwoodFormNotEquivariant

sa_claim "MarginalisationCharacterization.kirkwoodFormNotEquivariant"
  group "MarginalisationCharacterization" required
  text "**Theorem T3b (Kirkwood obstruction, concrete form).** There exist concrete real vector spaces `V₄`, `V₃`, a surjective linear marginalisation `M`, and a Kirkwood-form order-4 closure `C₄` such that no order-3 closure family `C₃` makes the closure diagram commute."
  impl EBCMCategory.MarginalisationCharacterization.kirkwood_form_not_equivariant

sa_fail_forward "MarginalisationCharacterization.kirkwoodFormNotEquivariant" 1 "impl is ∃ V₄ V₃ (ℝ-modules in Type) M C₄, IsKirkwoodForm C₄ ∧ ∀ C₃, ¬ Equivariant M C₄.C C₃.C. It does NOT state Function.Surjective M, which the text requires ('a surjective linear marginalisation M') and S1 contains. The impl's witness MℝLin happens to be surjective, but that is visible only in the proof term, and the ∃ gives an arbitrary M. Proving surjectivity of MℝLin would need real arithmetic (preimage fun _ => y c, 0 with y c + 0 = y c), not a consequence of h."

/-- Drop surjectivity, reorder the instance witnesses, and turn `¬ ∃ C₃` into `∀ C₃, ¬`. -/
@[sa_backward "MarginalisationCharacterization.kirkwoodFormNotEquivariant"]
theorem bwd (s1 : S1) : sa_impl% "MarginalisationCharacterization.kirkwoodFormNotEquivariant" := by
  obtain ⟨V₄, V₃, iA₄, iM₄, iA₃, iM₃, M, C₄, _, hK, hno⟩ := s1
  exact ⟨V₄, V₃, iA₄, iA₃, iM₄, iM₃, M, C₄, hK, fun C₃ hC => hno ⟨C₃, hC⟩⟩

end Alignment.Shadows.MarginalisationCharacterization.kirkwoodFormNotEquivariant

/-! ## `MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient` -/
namespace Alignment.Shadows.MarginalisationCharacterization.kkrNecessaryNotSufficient_notSufficient

sa_claim "MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient"
  group "MarginalisationCharacterization" required
  text "**Theorem T3c.** The Kiss–Kenah–Rempala pairwise-closure exactness conditions (cf. `ClosureTheorem.lean`, Results 51–59) [...] **not sufficient** for marginalisation equivariance with the order-4 closed system used to generate `F₄`."
  impl EBCMCategory.MarginalisationCharacterization.kkr_necessary_not_sufficient

@[sa_forward "MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient" 1]
theorem fwd1 (h : sa_impl% "MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient") :
    S1 := by
  refine Exists.imp (fun ψ h₁ => ?_) h
  -- Keep only `closureKappa ψ = 1` under the eight binders, drop the inner four binders under
  -- the outer four, then drop the outer four (two shallow phases keep the vacuity guard's
  -- normaliser within its budget).
  exact Exists.elim
    ((h₁.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
      h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.1).imp
        fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
          Exists.elim h fun _ h => Exists.elim h fun _ h => Exists.elim h fun _ h =>
            Exists.elim h fun _ h => h)
    fun _ h => Exists.elim h fun _ h => Exists.elim h fun _ h => Exists.elim h fun _ h => h

sa_fail_forward "MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient" 2 "impl is EXISTENTIAL over the order-4 system: ∃ ψ V₄ V₃ M C₄, closureKappa ψ = 1 ∧ IsKirkwoodForm C₄ ∧ ∀ C₃, ¬ Equivariant M C₄.C C₃.C. It says nothing about the named system (MℝLin, F4Kℝ): that the witness is U4ℝ / U3ℝ / MℝLin / C4ℝ is visible only in the proof term, and eliminating the ∃ gives arbitrary V₄ V₃ M C₄. S2 (¬ ∃ F₃ : U3ℝ → U3ℝ, Equivariant MℝLin F4Kℝ F₃) is about that specific system and would need the real-arithmetic fibre argument at u₁, u₂ (norm_num), which h does not supply."

sa_fail_forward "MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient" 3 "impl is EXISTENTIAL over the order-4 system: ∃ ψ V₄ V₃ M C₄, closureKappa ψ = 1 ∧ IsKirkwoodForm C₄ ∧ ∀ C₃, ¬ Equivariant M C₄.C C₃.C. It says nothing about the named system (MℝLin, C4ℝ): the witness is visible only in the proof term. S3 (¬ ∃ F₃ : U3ℝ → U3ℝ, Equivariant MℝLin C4ℝ.C F₃) is about that specific system and would need the real-arithmetic fibre argument at u₁, u₂ (norm_num), which h does not supply."

sa_fail_backward "MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient" "impl additionally asserts C₄.IsKirkwoodForm for its order-4 witness. The shadows give ψ with closureKappa ψ = 1 (S1) and the non-equivariance of the concrete system MℝLin / C4ℝ (S2, S3), so every impl component except IsKirkwoodForm can be assembled from them. The text fragment does not say that the order-4 closure is Kirkwood-form, no shadow states it, and IsKirkwoodForm C4ℝ (the trusted lemma C4ℝ_isKirkwoodForm, proved by norm_num over ℝ) is not derivable structurally. So the impl is strictly stronger than the shadow set."

end Alignment.Shadows.MarginalisationCharacterization.kkrNecessaryNotSufficient_notSufficient

/-! ## `MarginalisationCharacterization.kkrNecessaryNotSufficient.formal` -/
namespace Alignment.Shadows.MarginalisationCharacterization.kkrNecessaryNotSufficient_formal

sa_claim "MarginalisationCharacterization.kkrNecessaryNotSufficient.formal"
  group "MarginalisationCharacterization" required
  text "The formal statement: there exists a degree distribution `ψ` whose `closureKappa` is `1` (so the KKR pairwise-exactness criterion of Result 52 is met) together with concrete `V₄`/`V₃` and a Kirkwood-form order-4 closure `C₄` for which marginalisation equivariance against `M` still fails."
  impl EBCMCategory.MarginalisationCharacterization.kkr_necessary_not_sufficient

@[sa_forward "MarginalisationCharacterization.kkrNecessaryNotSufficient.formal" 1]
theorem fwd1 (h : sa_impl% "MarginalisationCharacterization.kkrNecessaryNotSufficient.formal") :
    S1 := by
  refine Exists.imp (fun ψ h₁ => ?_) h
  -- Keep only `closureKappa ψ = 1` under the eight binders, drop the inner four binders under
  -- the outer four, then drop the outer four (two shallow phases keep the vacuity guard's
  -- normaliser within its budget).
  exact Exists.elim
    ((h₁.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
      h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.1).imp
        fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
          Exists.elim h fun _ h => Exists.elim h fun _ h => Exists.elim h fun _ h =>
            Exists.elim h fun _ h => h)
    fun _ h => Exists.elim h fun _ h => Exists.elim h fun _ h => Exists.elim h fun _ h => h

/-- The impl's order-4 witness, with `¬ ∃ F₃` obtained from `∀ C₃, ¬` at `C₃ = ⟨F₃⟩`. -/
@[sa_forward "MarginalisationCharacterization.kkrNecessaryNotSufficient.formal" 2]
theorem fwd2 (h : sa_impl% "MarginalisationCharacterization.kkrNecessaryNotSufficient.formal") :
    S2 := by
  exact Exists.elim h (fun _ψ h₁ =>
    Exists.imp (fun _V₄ h₂ => Exists.imp (fun _V₃ h₃ => Exists.imp (fun _iA₄ h₄ =>
      Exists.elim h₄ (fun iA₃ h₅ => Exists.imp (fun _iM₄ h₆ =>
        ⟨iA₃, Exists.imp (fun _iM₃ h₇ => Exists.imp (fun _M h₈ => Exists.imp (fun _C₄ h₉ =>
          ⟨h₉.2.1, fun hex => Exists.elim hex (fun F₃ hF => h₉.2.2 ⟨F₃⟩ hF)⟩) h₈) h₇) h₆⟩) h₅))
        h₃) h₂) h₁)

@[sa_backward "MarginalisationCharacterization.kkrNecessaryNotSufficient.formal"]
theorem bwd (s1 : S1) (s2 : S2) :
    sa_impl% "MarginalisationCharacterization.kkrNecessaryNotSufficient.formal" := by
  obtain ⟨ψ, hk⟩ := s1
  obtain ⟨V₄, V₃, iA₄, iM₄, iA₃, iM₃, M, C₄, hK, hno⟩ := s2
  exact ⟨ψ, V₄, V₃, iA₄, iA₃, iM₄, iM₃, M, C₄, hk, hK, fun C₃ hC => hno ⟨C₃.C, hC⟩⟩

end Alignment.Shadows.MarginalisationCharacterization.kkrNecessaryNotSufficient_formal

/-! ## `MarginalisationCharacterization.existsEquivariantIffFibrewise` (`Equivariant M F F₃`
unfolds to `∀ w, M (F w) = F₃ (M w)`) -/
namespace Alignment.Shadows.MarginalisationCharacterization.existsEquivariantIffFibrewise

sa_claim "MarginalisationCharacterization.existsEquivariantIffFibrewise" group "MarginalisationCharacterization" required
  text "**Fibre criterion.** For any field `F` on `V₄`, some order-3 field `F₃` satisfies `M ∘ F = F₃ ∘ M` iff `F` maps each fibre of `M` into a single fibre: `M u = M u' → M (F u) = M (F u')`."
  impl EBCMCategory.MarginalisationCharacterization.exists_equivariant_iff_fibrewise

@[sa_forward "MarginalisationCharacterization.existsEquivariantIffFibrewise" 1]
theorem fwd1 (h : sa_impl% "MarginalisationCharacterization.existsEquivariantIffFibrewise") :
    S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F
  exact (h M F).mp

@[sa_forward "MarginalisationCharacterization.existsEquivariantIffFibrewise" 2]
theorem fwd2 (h : sa_impl% "MarginalisationCharacterization.existsEquivariantIffFibrewise") :
    S2.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F
  exact (h M F).mpr

@[sa_backward "MarginalisationCharacterization.existsEquivariantIffFibrewise"]
theorem bwd (s1 : S1.{u_1, u_2}) (s2 : S2.{u_1, u_2}) :
    sa_impl% "MarginalisationCharacterization.existsEquivariantIffFibrewise" := by
  intro V₄ V₃ _ _ _ _ M F
  exact ⟨s1 M F, s2 M F⟩

end Alignment.Shadows.MarginalisationCharacterization.existsEquivariantIffFibrewise

/-! ## `MarginalisationCharacterization.linearAdmitsEquivariantIff` (`x ∈ LinearMap.ker M`
unfolds to `M x = 0`) -/
namespace Alignment.Shadows.MarginalisationCharacterization.linearAdmitsEquivariantIff

sa_claim "MarginalisationCharacterization.linearAdmitsEquivariantIff" group "MarginalisationCharacterization" required
  text "**Theorem T3a (corrected).** A linear field `L₄` admits an order-3 field `F₃` with `M ∘ L₄ = F₃ ∘ M` iff `L₄` maps `ker M` into `ker M`. So linear closures are *not* equivariant for every linear `M`."
  impl EBCMCategory.MarginalisationCharacterization.linear_admits_equivariant_iff

@[sa_forward "MarginalisationCharacterization.linearAdmitsEquivariantIff" 1]
theorem fwd1 (h : sa_impl% "MarginalisationCharacterization.linearAdmitsEquivariantIff") :
    S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M L₄ hex x hx
  exact (h M L₄).mp hex x hx

@[sa_forward "MarginalisationCharacterization.linearAdmitsEquivariantIff" 2]
theorem fwd2 (h : sa_impl% "MarginalisationCharacterization.linearAdmitsEquivariantIff") :
    S2.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M L₄ hk
  exact (h M L₄).mpr hk

sa_fail_forward "MarginalisationCharacterization.linearAdmitsEquivariantIff" 3 "impl is the iff criterion. S3 (for some linear M, some linear L₄ admits no equivariant F₃: 'linear closures are not equivariant for every linear M') needs a concrete M and L₄ with L₄(ker M) ⊄ ker M. impl exhibits no such pair, and building one needs real arithmetic (e.g. 1 ≠ 0), which is not structural."

@[sa_backward "MarginalisationCharacterization.linearAdmitsEquivariantIff"]
theorem bwd (s1 : S1.{u_1, u_2}) (s2 : S2.{u_1, u_2}) (_s3 : S3) :
    sa_impl% "MarginalisationCharacterization.linearAdmitsEquivariantIff" := by
  intro V₄ V₃ _ _ _ _ M L₄
  exact ⟨fun hex u hu => s1 M L₄ hex u hu, fun hk => s2 M L₄ hk⟩

end Alignment.Shadows.MarginalisationCharacterization.linearAdmitsEquivariantIff

/-! ## `MarginalisationCharacterization.existsKirkwoodFormEquivariant` -/
namespace Alignment.Shadows.MarginalisationCharacterization.existsKirkwoodFormEquivariant

sa_claim "MarginalisationCharacterization.existsKirkwoodFormEquivariant" group "MarginalisationCharacterization" required
  text "A non-additive (`IsKirkwoodForm`) closure can be equivariant: with `M = id` on `ℝ`, the field `x ↦ x²` is non-additive and commutes with itself."
  impl EBCMCategory.MarginalisationCharacterization.exists_kirkwoodForm_equivariant

sa_fail_forward "MarginalisationCharacterization.existsKirkwoodFormEquivariant" 1 "impl exists_kirkwoodForm_equivariant is existential over M, C₄, C₃; the field x ↦ x² appears only in its proof term. S1 (the closure x ↦ x² is IsKirkwoodForm) is about the named field and does not follow from the existential."

sa_fail_forward "MarginalisationCharacterization.existsKirkwoodFormEquivariant" 2 "S2 (with M = id, x ↦ x² intertwines itself) holds by rfl (Equivariant id F F unfolds to F u = F u). impl's existential does not name the field, so a checker could only prove S2 without h (vacuous)."

@[sa_backward "MarginalisationCharacterization.existsKirkwoodFormEquivariant"]
theorem bwd (s1 : S1) (s2 : S2) :
    sa_impl% "MarginalisationCharacterization.existsKirkwoodFormEquivariant" :=
  ⟨LinearMap.id, ⟨fun x => x ^ 2⟩, ⟨fun x => x ^ 2⟩, s1, s1, s2⟩

end Alignment.Shadows.MarginalisationCharacterization.existsKirkwoodFormEquivariant

/-! ## `MarginalisationCharacterization.closureFamilies.linear` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.MarginalisationCharacterization.closureFamilies_linear

sa_claim "MarginalisationCharacterization.closureFamilies.linear" group "MarginalisationCharacterization"
  text "* **Linear** closures: `C(u) = L u` for some linear `L`. (Includes truncation and moment-zero closures. Exact closures of the unclosed CTMC are in general nonlinear: the KKR-exact pairwise closure `[ASI] = κ·[AS][SI]/[S]` is rational.)"
  impl

end Alignment.Shadows.MarginalisationCharacterization.closureFamilies_linear

/-! ## `MarginalisationCharacterization.header.onlyTrivial` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.MarginalisationCharacterization.header_onlyTrivial

sa_claim "MarginalisationCharacterization.header.onlyTrivial" group "MarginalisationCharacterization"
  text "Non-additive closures can escape the obstruction: some `C₃` makes the diagram commute iff `C₄` maps each fibre of `M` into a single fibre (`exists_equivariant_iff_fibrewise`)."
  impl

end Alignment.Shadows.MarginalisationCharacterization.header_onlyTrivial

/-! ## `MarginalisationCharacterization.kkrNecessaryNotSufficient.concretely` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.MarginalisationCharacterization.kkrNecessaryNotSufficient_concretely

sa_claim "MarginalisationCharacterization.kkrNecessaryNotSufficient.concretely" group "MarginalisationCharacterization"
  text "The order-4 closure `C₄` is independent data: a degree record that meets the KKR criterion (`closureKappa = 1` for Poisson) can be paired with the non-equivariant surrogate of T3b. It is false that T3b applies to every Kirkwood-form `C₄`: with `M = id`, `x ↦ x²` is Kirkwood-form and equivariant (`exists_kirkwoodForm_equivariant`)."
  impl

end Alignment.Shadows.MarginalisationCharacterization.kkrNecessaryNotSufficient_concretely

/-! ## `MarginalisationCharacterization.linearClosureEquivariant.b` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.MarginalisationCharacterization.linearClosureEquivariant_b

sa_claim "MarginalisationCharacterization.linearClosureEquivariant.b" group "MarginalisationCharacterization"
  text "It is not the only case in which the diagram commutes: see `exists_equivariant_iff_fibrewise` and `exists_kirkwoodForm_equivariant`."
  impl

end Alignment.Shadows.MarginalisationCharacterization.linearClosureEquivariant_b
