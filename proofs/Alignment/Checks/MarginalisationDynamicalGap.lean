import Alignment.Registry
import Alignment.Shadows.MarginalisationDynamicalGap

/-!
# Checkers: group `MarginalisationDynamicalGap`

Registrations, forward / backward checkers and failure records for the claims of
`EBCMCategory/MarginalisationDynamicalGap.lean`. The shadows are in
`Alignment/Shadows/MarginalisationDynamicalGap.lean` (written blind).

No bridges are used. Every shadow is stated over the trusted operations themselves (`IsFlow`,
`Equivariant`, `ClosureFamily`, `ClosureFamily.IsKirkwoodForm`, `algebraicGap`, `trajectoryGap`,
`MℝLin`, `MℝLinCLM`, `F4Kℝ`, `F3Kℝ`, `u₁`). The remaining differences are definitional:

* `trajectoryGap M φ₄ φ₃ u` is by definition `fun t => M (φ₄ u t) - φ₃ (M u) t`, and
  `algebraicGap M F₄ F₃ u` is by definition `M (F₄ u) - F₃ (M u)`;
* the shadow point `pt13 = (a ↦ 1, b ↦ 3)` is by definition the trusted `u₁`;
* `⇑MℝLinCLM` is by definition `⇑MℝLin` (`MℝLinCLM := ⟨MℝLin, _⟩`);
* a continuous linear map `M` coerces to the linear map `↑M` with the same application;
* `(ClosureFamily.mk F).IsKirkwoodForm` is by definition `∃ u v, F (u + v) ≠ F u + F v`;
* `a ≥ b` is notation for `b ≤ a`.

Differences that are not definitional (a one-sided vs a two-sided derivative, `∃ T > 0, ∀ t ∈
(0, T]` vs `∀ᶠ t in 𝓝[>] 0`, real arithmetic such as `(1 + 1)² / 4 = 1`) are Mathlib content.
They are not structural and cannot be carried by a bridge (whose left-hand side must be a trusted
definition), so those checks are recorded with `sa_fail_*`.
-/

open EBCMCategory.Marginalisation
open EBCMCategory.MarginalisationCharacterization
open MarginalisationObstruction
open EBCMCategory.MarginalisationDynamicalGap

/-! Level names of the universe-polymorphic implementations (`Type _` gives `u_1 u_2`). -/
universe u_1 u_2

/-! ## header.overview -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.header_overview

sa_claim "MarginalisationDynamicalGap.header.overview" group "MarginalisationDynamicalGap" required
  text "T2 (algebraic gap = 2 at u₁) + T5 (gap = first-order divergence rate) give, in local form: *For any local solutions ψ₄ of F4Kℝ from u₁ and ψ₃ of F3Kℝ from M u₁, the trajectory gap `M(ψ₄ t) − ψ₃ t` has derivative exactly 2 at t = 0 (`witness_localGap_hasDerivAt`), and its norm is at least t for all small t > 0 (`witness_localGap_ge`).*"
  impl EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_rate_two_at_witness

sa_fail_forward "MarginalisationDynamicalGap.header.overview" 1 "impl trajectoryGap_rate_two_at_witness is about global flows φ₄, φ₃; its hypothesis IsFlow F3Kℝ φ₃ is unsatisfiable (no_flow_F3Kℝ), so it holds vacuously and gives nothing. S1 (algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = 2) is algebraicGap_at_witness, which is not in this claim's impl list."

sa_fail_forward "MarginalisationDynamicalGap.header.overview" 2 "S2 is T5 in local form (localGap_hasDerivAt_zero), for general M, F₄, F₃. impl is a statement about global flows at the witness only, and its hypothesis is unsatisfiable, so it does not give S2."

sa_fail_forward "MarginalisationDynamicalGap.header.overview" 3 "S3 (for local solutions at the witness the gap has derivative 2) is witness_localGap_hasDerivAt, which the text cites and which is not in impl. impl needs global flows (IsFlow), which local solutions are not; F3Kℝ has no global flow, so impl is vacuous."

sa_fail_forward "MarginalisationDynamicalGap.header.overview" 4 "S4 (the gap's norm is at least t for small t > 0) is witness_localGap_ge (not in impl). impl, a vacuous derivative statement for global flows, does not give it."

sa_fail_backward "MarginalisationDynamicalGap.header.overview" "To derive impl from S3 one turns the global flows into LocalSol curves (φ₄ u₁, φ₃ (M u₁)), which needs a radius δ with 0 < δ in ℝ (e.g. zero_lt_one). A real inequality is not structural. Otherwise S3's conclusion is impl's up to unfolding trajectoryGap and cst. The implementation's hypothesis is in any case refuted by no_flow_F3Kℝ (hypothesis_refuted)."

end Alignment.Shadows.MarginalisationDynamicalGap.header_overview

/-! ## header.T6.a -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.header_T6_a

sa_claim "MarginalisationDynamicalGap.header.T6.a" group "MarginalisationDynamicalGap" required
  text "T6 exhibits an existence result at one state: an order-3 right-hand side `F3_exact` (the constant 6, fitted to `M(F4Kℝ u₁)`) that agrees with the marginalised order-4 surrogate at `u₁`,"
  impl EBCMCategory.MarginalisationDynamicalGap.refinement_failure_exists

sa_fail_forward "MarginalisationDynamicalGap.header.T6.a" 1 "impl refinement_failure_exists is existential over F4_kirk, F3_kirk, F3_exact and u₀; the named witnesses F4Kℝ, u₁ and the constant 6 appear only in its proof. S1 (MℝLinCLM (F4Kℝ u₁) equals the constant field 6 at u₁) is about the named data, so it does not follow from impl's statement. (It would also need the real arithmetic 1·3 + 3 = 6.)"

sa_fail_backward "MarginalisationDynamicalGap.header.T6.a" "S1 gives only the agreement at u₁. impl also needs IsKirkwoodForm for the order-4 and order-3 closures (the trusted lemmas C4ℝ_isKirkwoodForm and F3Kℝ_isKirkwoodForm, which a checker may not cite) and the disequality F3Kℝ(M u₁) ≠ 6 (real arithmetic 4 ≠ 6). It is stated with MℝLin rather than MℝLinCLM. impl is stronger than this fragment of the text."

end Alignment.Shadows.MarginalisationDynamicalGap.header_T6_a

/-! ## `MarginalisationDynamicalGap.fibreCollapseObstruction` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.FibreCollapseObstruction

sa_claim "MarginalisationDynamicalGap.fibreCollapseObstruction" group "MarginalisationDynamicalGap"
  required
  text "**Theorem T4 (Fibre-collapse obstruction).** If `M` identifies two points (`h_fibre : M u₁ = M u₂`) but `F` splits them apart under `M` (`h_split : M (F u₁) ≠ M (F u₂)`), then no order-3 closure family `C₃` can make the diagram `M ∘ F = C₃ ∘ M` commute."
  impl EBCMCategory.MarginalisationDynamicalGap.fibre_collapse_obstruction

/-- The impl holds for any real modules and linear `M`. It is instantiated at the normed spaces of
`S1` with the underlying linear map `↑M` of the continuous linear map `M` (same application). A
commuting diagram `⇑M ∘ F = C₃.C ∘ ⇑M` gives `Equivariant ↑M F C₃.C` pointwise (`congrFun`). -/
@[sa_forward "MarginalisationDynamicalGap.fibreCollapseObstruction" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.fibreCollapseObstruction") :
    S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F w₁ w₂ hfib hsplit C₃ hcomm
  exact h (M : V₄ →ₗ[ℝ] V₃) F w₁ w₂ hfib hsplit C₃ (fun w => congrFun hcomm w)

/-- The impl is stated for arbitrary real modules and linear `M`, and `S1` only for normed spaces
and continuous linear `M`, so `S1` cannot be instantiated at the impl's setting. The impl is,
however, a purely logical consequence of the definition of `Equivariant`: an equivariant `C₃`
forces `M (F w₁) = C₃ (M w₁) = C₃ (M w₂) = M (F w₂)`. It is therefore proved here structurally
(`Eq.trans`, `congrArg`, `Eq.symm`) without using `S1`. This shows that the impl claims nothing
beyond what the text's argument gives. -/
@[sa_backward "MarginalisationDynamicalGap.fibreCollapseObstruction"]
theorem bwd (_s1 : S1.{u_1, u_2}) :
    sa_impl% "MarginalisationDynamicalGap.fibreCollapseObstruction" := by
  intro V₄ V₃ _ _ _ _ M F w₁ w₂ hfib hsplit C₃ hEq
  exact hsplit ((hEq w₁).trans ((congrArg C₃.C hfib).trans (hEq w₂).symm))

end Alignment.Shadows.MarginalisationDynamicalGap.FibreCollapseObstruction

/-! ## `MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.KirkwoodNotEquivariantViaT4

sa_claim "MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4" group
  "MarginalisationDynamicalGap" required
  text "`kirkwood_form_not_equivariant` (T3b) re-derived via T4: the (2,1) ℝ-witness satisfies the fibre-collapse hypothesis."
  impl EBCMCategory.MarginalisationDynamicalGap.kirkwood_not_equivariant_via_T4

/-- `S1` is literally the impl's statement. -/
@[sa_forward "MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4") : S1 :=
  fun C₃ => h C₃

sa_fail_forward "MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4" 2 "impl kirkwood_not_equivariant_via_T4 states only the conclusion ∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin F4Kℝ C₃.C. The fibre-collapse hypothesis at the witness (the points u₁ = (1, 3), u₂ = (4, 0) with MℝLin u₁ = MℝLin u₂ and MℝLin (F4Kℝ u₁) ≠ MℝLin (F4Kℝ u₂)) appears only in its proof, not in its statement. S2 asks for ∃ w₁ w₂ with that property. From impl one gets only ¬¬∃ (if no fibre collapse existed, C₃ v := M (F4Kℝ (section of M at v)) would be equivariant), and removing the double negation needs Classical. Proving S2 directly needs real arithmetic (1 + 3 = 4 + 0, 1·3 + 3 ≠ 4·0 + 0) and would not use h (vacuous). The clause 'the (2,1) ℝ-witness satisfies the fibre-collapse hypothesis' describes how the proof applies T4, but it is also an assertion about the witness that the statement does not carry, so S2 is a fair reading of the text."

@[sa_backward "MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4"]
theorem bwd (s1 : S1) (_s2 : S2) :
    sa_impl% "MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4" :=
  fun C₃ => s1 C₃

end Alignment.Shadows.MarginalisationDynamicalGap.KirkwoodNotEquivariantViaT4

/-! ## `MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapHasDerivAtZero

sa_claim "MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero" group
  "MarginalisationDynamicalGap" required
  text "**Theorem T5 (Quantitative dynamical gap).** For any flow `φ₄` of `F₄` and any flow `φ₃` of `F₃`, the trajectory gap function `t ↦ M(φ₄ u t) − φ₃(M u)(t)` has derivative `algebraicGap M F₄ F₃ u = M(F₄ u) − F₃(M u)` at `t = 0`."
  impl EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_hasDerivAt_zero

/-- `trajectoryGap M φ₄ φ₃ w` is by definition `fun t => M (φ₄ w t) - φ₃ (M w) t`. -/
@[sa_forward "MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero") :
    S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ w
  exact h M F₄ F₃ h₄ h₃ w

/-- As `fwd1`; in addition `algebraicGap M F₄ F₃ w` is by definition `M (F₄ w) - F₃ (M w)`. -/
@[sa_forward "MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero" 2]
theorem fwd2 (h : sa_impl% "MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero") :
    S2.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ w
  exact h M F₄ F₃ h₄ h₃ w

@[sa_backward "MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero"]
theorem bwd (s1 : S1.{u_1, u_2}) (_s2 : S2.{u_1, u_2}) :
    sa_impl% "MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero" := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ w
  exact s1 M F₄ F₃ φ₄ φ₃ h₄ h₃ w

end Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapHasDerivAtZero

/-! ## `MarginalisationDynamicalGap.trajectoryGapAtZero` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapAtZero

sa_claim "MarginalisationDynamicalGap.trajectoryGapAtZero" group "MarginalisationDynamicalGap"
  required
  text "The trajectory gap vanishes at `t = 0`."
  impl EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_at_zero

@[sa_forward "MarginalisationDynamicalGap.trajectoryGapAtZero" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.trajectoryGapAtZero") :
    S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ w
  exact h M h₄ h₃ w

/-- `trajectoryGap M φ₄ φ₃ w 0` is by definition `M (φ₄ w 0) - φ₃ (M w) 0`. -/
@[sa_forward "MarginalisationDynamicalGap.trajectoryGapAtZero" 2]
theorem fwd2 (h : sa_impl% "MarginalisationDynamicalGap.trajectoryGapAtZero") :
    S2.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ w
  exact h M h₄ h₃ w

@[sa_backward "MarginalisationDynamicalGap.trajectoryGapAtZero"]
theorem bwd (s1 : S1.{u_1, u_2}) (_s2 : S2.{u_1, u_2}) :
    sa_impl% "MarginalisationDynamicalGap.trajectoryGapAtZero" := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ w
  exact s1 M F₄ F₃ φ₄ φ₃ h₄ h₃ w

end Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapAtZero

/-! ## `MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapNormGeHalfEpsT

sa_claim "MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT" group
  "MarginalisationDynamicalGap" required
  text "**Theorem T7 (Quantitative lower bound on trajectory gap).** If the algebraic gap has norm at least `ε > 0`, then for all small enough `t > 0` the trajectory gap satisfies `‖trajectoryGap M φ₄ φ₃ u t‖ ≥ ε * t / 2`."
  impl EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_norm_ge_half_eps_t

sa_fail_forward "MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT" 1 "impl gives the explicit threshold form ∃ T > 0, ∀ t, 0 < t → t ≤ T → ε·t/2 ≤ ‖trajectoryGap M φ₄ φ₃ u t‖ (same hypotheses: IsFlow for both, 0 < ε, ε ≤ ‖algebraicGap M F₄ F₃ u‖). S1 states the same bound as ∀ᶠ t in 𝓝[>] 0. The two are mathematically equivalent, but turning (0, T] into a set of the filter nhdsWithin 0 (Set.Ioi 0) needs the library lemmas Iio_mem_nhds / mem_nhdsWithin_Ioi_iff_exists_Ioc_subset (nhds on ℝ is an infimum of principal filters and cannot be unfolded structurally). No trusted definition is involved, so no bridge can carry it either. Audit limitation, not a meaning gap."

sa_fail_backward "MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT" "S1 gives the bound ∀ᶠ t in 𝓝[>] 0. impl asks for an explicit ∃ T > 0, ∀ t, 0 < t → t ≤ T → …. Extracting T from the filter needs mem_nhdsWithin_Ioi_iff_exists_Ioc_subset (or Metric.eventually_nhds_iff) and halving the radius (real arithmetic), which is library content and not structural. The statements are mathematically equivalent. Audit limitation, not a meaning gap."

end Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapNormGeHalfEpsT

/-! ## `MarginalisationDynamicalGap.mRealLinCLMApply` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.MRealLinCLMApply

sa_claim "MarginalisationDynamicalGap.mRealLinCLMApply" group "MarginalisationDynamicalGap"
  required
  text "Application lemma: `MℝLinCLM u i = u Idx4.a + u Idx4.b` for any `i : Idx3`."
  impl EBCMCategory.MarginalisationDynamicalGap.MℝLinCLM_apply

@[sa_forward "MarginalisationDynamicalGap.mRealLinCLMApply" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.mRealLinCLMApply") : S1 :=
  fun w i => h w i

@[sa_backward "MarginalisationDynamicalGap.mRealLinCLMApply"]
theorem bwd (s1 : S1) : sa_impl% "MarginalisationDynamicalGap.mRealLinCLMApply" :=
  fun w i => s1 w i

end Alignment.Shadows.MarginalisationDynamicalGap.MRealLinCLMApply

/-! ## `MarginalisationDynamicalGap.algebraicGapAtWitness.a` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.AlgebraicGapAtWitness_a

sa_claim "MarginalisationDynamicalGap.algebraicGapAtWitness.a" group "MarginalisationDynamicalGap"
  required
  text "At `u₁ = (1, 3)` with the Kirkwood m=3 closure `F3Kℝ`, the algebraic gap equals the constant vector `2` in `U3ℝ`."
  impl EBCMCategory.MarginalisationDynamicalGap.algebraicGap_at_witness

/-- The shadow point `pt13 = (a ↦ 1, b ↦ 3)` is by definition the trusted `u₁`. -/
@[sa_forward "MarginalisationDynamicalGap.algebraicGapAtWitness.a" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.algebraicGapAtWitness.a") : S1 := h

/-- As `fwd1`; `algebraicGap M F₄ F₃ u` is by definition `M (F₄ u) - F₃ (M u)`. -/
@[sa_forward "MarginalisationDynamicalGap.algebraicGapAtWitness.a" 2]
theorem fwd2 (h : sa_impl% "MarginalisationDynamicalGap.algebraicGapAtWitness.a") : S2 := h

@[sa_backward "MarginalisationDynamicalGap.algebraicGapAtWitness.a"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "MarginalisationDynamicalGap.algebraicGapAtWitness.a" :=
  s1

end Alignment.Shadows.MarginalisationDynamicalGap.AlgebraicGapAtWitness_a

/-! ## `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapRateTwoAtWitness_a

sa_claim "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a" group
  "MarginalisationDynamicalGap" required
  text "**Theorem T5 Corollary (Divergence rate at the (2,1) witness).** For *any* flows `φ₄` of `F4Kℝ` and `φ₃` of `F3Kℝ` (existence is a hypothesis, not derived — cf. §3 of `MARGINALISATION_SPEC.md`), the trajectory gap at `u₁ = (1, 3)` diverges at rate exactly `2` in the `Idx3.c` direction at `t = 0`: `M(φ₄ u₁ t) − φ₃(M u₁) t = 2t · ê_c + o(t)`."
  impl EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_rate_two_at_witness

/-- `pt13` is by definition `u₁`. -/
@[sa_forward "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a") :
    S1 :=
  fun _φ₄ _φ₃ h₄ h₃ => h h₄ h₃

/-- As `fwd1`; `trajectoryGap` unfolds to the explicit gap. -/
@[sa_forward "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a" 2]
theorem fwd2 (h : sa_impl% "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a") :
    S2 :=
  fun _φ₄ _φ₃ h₄ h₃ => h h₄ h₃

@[sa_backward "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a"]
theorem bwd (s1 : S1) (_s2 : S2) :
    sa_impl% "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a" := by
  intro φ₄ φ₃ h₄ h₃
  exact s1 φ₄ φ₃ h₄ h₃

end Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapRateTwoAtWitness_a

/-! ## `MarginalisationDynamicalGap.f3RealIsKirkwoodForm` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.F3RealIsKirkwoodForm

sa_claim "MarginalisationDynamicalGap.f3RealIsKirkwoodForm" group "MarginalisationDynamicalGap"
  required
  text "`F3Kℝ` is nonlinear (has Kirkwood form): witnessed by `u = v = (c ↦ 1)`, where `F3Kℝ(u + v)(c) = 1 ≠ 1/2 = F3Kℝ(u)(c) + F3Kℝ(v)(c)`."
  impl EBCMCategory.MarginalisationDynamicalGap.F3Kℝ_isKirkwoodForm

/-- `S1` is literally the impl's statement. -/
@[sa_forward "MarginalisationDynamicalGap.f3RealIsKirkwoodForm" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.f3RealIsKirkwoodForm") : S1 := h

/-- `(ClosureFamily.mk F3Kℝ).IsKirkwoodForm` unfolds to `∃ u v, F3Kℝ (u + v) ≠ F3Kℝ u + F3Kℝ v`. -/
@[sa_forward "MarginalisationDynamicalGap.f3RealIsKirkwoodForm" 2]
theorem fwd2 (h : sa_impl% "MarginalisationDynamicalGap.f3RealIsKirkwoodForm") : S2 := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, hxy⟩

sa_fail_forward "MarginalisationDynamicalGap.f3RealIsKirkwoodForm" 3 "impl F3Kℝ_isKirkwoodForm states only (ClosureFamily.mk F3Kℝ).IsKirkwoodForm, i.e. ∃ u v, F3Kℝ (u + v) ≠ F3Kℝ u + F3Kℝ v. The witness u = v = (c ↦ 1) appears only in its proof. S3 is the witness value F3Kℝ (oneC + oneC) c = 1, i.e. (1 + 1)²/4 = 1 in ℝ. impl does not state it, and proving it needs real arithmetic (norm_num), which is not structural and would not use h (vacuous)."

sa_fail_forward "MarginalisationDynamicalGap.f3RealIsKirkwoodForm" 4 "impl states only the existential non-additivity (∃ u v, F3Kℝ (u + v) ≠ F3Kℝ u + F3Kℝ v), not the witness values. S4 is F3Kℝ oneC c + F3Kℝ oneC c = 1/2, i.e. 1²/4 + 1²/4 = 1/2 in ℝ. impl does not state it, and proving it needs real arithmetic (norm_num), which is not structural and would not use h (vacuous)."

@[sa_backward "MarginalisationDynamicalGap.f3RealIsKirkwoodForm"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) :
    sa_impl% "MarginalisationDynamicalGap.f3RealIsKirkwoodForm" :=
  s1

end Alignment.Shadows.MarginalisationDynamicalGap.F3RealIsKirkwoodForm

/-! ## `MarginalisationDynamicalGap.refinementFailureExists.a` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.RefinementFailureExists_a

sa_claim "MarginalisationDynamicalGap.refinementFailureExists.a" group "MarginalisationDynamicalGap"
  required
  text "**Theorem T6 (Refinement-failure existence).** There exist Kirkwood-form closures `F4_kirk` (order 4) and `F3_kirk` (order 3), an \"exact\" order-3 RHS `F3_exact`, and an initial condition `u₀` such that: * the marginalised m=4 chain is **exact at first order**: `M(F4_kirk u₀) = F3_exact(M u₀)` (algebraic gap = 0); * the m=3 Kirkwood chain **deviates from exact**: `F3_kirk(M u₀) ≠ F3_exact(M u₀)`."
  impl EBCMCategory.MarginalisationDynamicalGap.refinement_failure_exists

/-- The impl's statement is definitionally `S1`: `⇑MℝLinCLM` is by definition `⇑MℝLin`. (A
destructuring proof exhausts the vacuity guard's normalisation budget.) -/
@[sa_forward "MarginalisationDynamicalGap.refinementFailureExists.a" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.refinementFailureExists.a") : S1 := h

@[sa_backward "MarginalisationDynamicalGap.refinementFailureExists.a"]
theorem bwd (s1 : S1) : sa_impl% "MarginalisationDynamicalGap.refinementFailureExists.a" := s1

end Alignment.Shadows.MarginalisationDynamicalGap.RefinementFailureExists_a

/-! ## refinementFailureExists.b -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.refinementFailureExists_b

sa_claim "MarginalisationDynamicalGap.refinementFailureExists.b" group "MarginalisationDynamicalGap" required
  text "Together with T5: relative to the fitted `F3_exact`, the marginalised m=4 surrogate has zero first-order error at `u₁` (by construction), while the m=3 Kirkwood surrogate has first-order error `|4 − 6| = 2`."
  impl EBCMCategory.MarginalisationDynamicalGap.algebraicGap_at_witness

sa_fail_forward "MarginalisationDynamicalGap.refinementFailureExists.b" 1 "impl algebraicGap_at_witness is the gap of F4Kℝ against F3Kℝ at u₁ (= 2). S1 is the gap against the fitted constant field F3_exact (= 0), a different order-3 field. impl does not mention F3_exact, and the zero gap needs the real arithmetic 1·3 + 3 = 6."

sa_fail_forward "MarginalisationDynamicalGap.refinementFailureExists.b" 2 "S2 (F3Kℝ (M u₁) = 4) is not stated by impl. Deriving it from impl's M(F4Kℝ u₁) − F3Kℝ(M u₁) = 2 needs M(F4Kℝ u₁) = 6 and the arithmetic 6 − x = 2 ⇒ x = 4 in ℝ, which are not structural."

sa_fail_forward "MarginalisationDynamicalGap.refinementFailureExists.b" 3 "S3 (‖F3Kℝ(M u₁) − F3_exact(M u₁)‖ = 2) is about the sup norm on Idx3 → ℝ and the field F3_exact, neither of which impl mentions. Computing it needs norm lemmas (pi_norm, Real.norm_eq_abs) and real arithmetic."

sa_fail_backward "MarginalisationDynamicalGap.refinementFailureExists.b" "impl (algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = 2) is not given by the shadows: S1 concerns F3_exact, S2 gives F3Kℝ(M u₁) = 4, and combining them with M(F4Kℝ u₁) = 6 needs real subtraction arithmetic (sub_eq_iff_eq_add etc.), which is not structural."

end Alignment.Shadows.MarginalisationDynamicalGap.refinementFailureExists_b

/-! ## normGeHalfEpsTOfHasDerivAt -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt

sa_claim "MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt" group "MarginalisationDynamicalGap" required
  text "If `f 0 = 0`, `f` has derivative `g` at `0` and `ε ≤ ‖g‖` with `ε > 0`, then `ε * t / 2 ≤ ‖f t‖` for all small enough `t > 0`."
  impl EBCMCategory.MarginalisationDynamicalGap.norm_ge_half_eps_t_of_hasDerivAt

sa_fail_forward "MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt" 1 "impl concludes ∃ T > 0, ∀ t, 0 < t → t ≤ T → ε t/2 ≤ ‖f t‖. S1 concludes ∀ᶠ t in 𝓝[>] 0, ε t/2 ≤ ‖f t‖. The two are equivalent, but turning the explicit interval (0, T] into membership in the filter 𝓝[>] 0 needs filter lemmas (mem_nhdsWithin, Ioc_mem_nhdsGT), which are not structural."

sa_fail_backward "MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt" "S1 gives an eventually-statement in the filter 𝓝[>] 0; impl needs an explicit T > 0 with the bound on (0, T]. Extracting T from filter membership needs Metric.mem_nhdsWithin_iff-type lemmas (and a positive radius), which are not structural."

end Alignment.Shadows.MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt

/-! ## localGapHasDerivAtZero (`LocalSol F v ψ` and `IsLocalSolution F v δ ψ` carry the same
data, packed differently: `ψ 0 = v ∧ ∃ δ, 0 < δ ∧ …` against `0 < δ ∧ ψ 0 = v ∧ …`) -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.localGapHasDerivAtZero

sa_claim "MarginalisationDynamicalGap.localGapHasDerivAtZero" group "MarginalisationDynamicalGap" required
  text "**Theorem T5, local form.** For any local solutions `ψ₄` of `F₄` through `u` and `ψ₃` of `F₃` through `M u` (`IsLocalSolution`), the gap `t ↦ M (ψ₄ t) − ψ₃ t` has derivative `algebraicGap M F₄ F₃ u` at `t = 0`."
  impl EBCMCategory.MarginalisationDynamicalGap.localGap_hasDerivAt_zero

@[sa_forward "MarginalisationDynamicalGap.localGapHasDerivAtZero" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.localGapHasDerivAtZero") :
    S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ w ψ₄ ψ₃ h₄ h₃
  obtain ⟨h40, δ₄, hδ₄, hd4⟩ := h₄
  obtain ⟨h30, δ₃, hδ₃, hd3⟩ := h₃
  exact h M F₄ F₃ w ⟨hδ₄, h40, hd4⟩ ⟨hδ₃, h30, hd3⟩

@[sa_backward "MarginalisationDynamicalGap.localGapHasDerivAtZero"]
theorem bwd (s1 : S1.{u_1, u_2}) :
    sa_impl% "MarginalisationDynamicalGap.localGapHasDerivAtZero" := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ u δ₄ δ₃ ψ₄ ψ₃ h₄ h₃
  exact s1 M F₄ F₃ u ψ₄ ψ₃ ⟨h₄.2.1, δ₄, h₄.1, h₄.2.2⟩ ⟨h₃.2.1, δ₃, h₃.1, h₃.2.2⟩

end Alignment.Shadows.MarginalisationDynamicalGap.localGapHasDerivAtZero

/-! ## localGapNormGeHalfEpsT -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.localGapNormGeHalfEpsT

sa_claim "MarginalisationDynamicalGap.localGapNormGeHalfEpsT" group "MarginalisationDynamicalGap" required
  text "**Theorem T7, local form.** If `‖algebraicGap M F₄ F₃ u‖ ≥ ε > 0`, then for any local solutions `ψ₄` of `F₄` through `u` and `ψ₃` of `F₃` through `M u`, `‖M (ψ₄ t) − ψ₃ t‖ ≥ ε * t / 2` for all small enough `t > 0`."
  impl EBCMCategory.MarginalisationDynamicalGap.localGap_norm_ge_half_eps_t

sa_fail_forward "MarginalisationDynamicalGap.localGapNormGeHalfEpsT" 1 "impl concludes ∃ T > 0, ∀ t, 0 < t → t ≤ T → ε t/2 ≤ ‖M(ψ₄ t) − ψ₃ t‖. S1 concludes the same bound as ∀ᶠ t in 𝓝[>] 0. Converting the explicit interval into filter membership needs filter lemmas (mem_nhdsWithin, Ioc_mem_nhdsGT), which are not structural. The content is the same."

sa_fail_backward "MarginalisationDynamicalGap.localGapNormGeHalfEpsT" "S1 gives an eventually-statement in 𝓝[>] 0; impl needs an explicit T > 0. Extracting T from filter membership needs Metric.mem_nhdsWithin_iff-type lemmas, which are not structural."

end Alignment.Shadows.MarginalisationDynamicalGap.localGapNormGeHalfEpsT

/-! ## algebraicGapWitness (`cst 6 - C₃ (cst 4)` unfolds to `fun i => 6 - C₃ (fun _ => 4) i`) -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.algebraicGapWitness

sa_claim "MarginalisationDynamicalGap.algebraicGapWitness" group "MarginalisationDynamicalGap" required
  text "The first-order rate at the witness for an arbitrary order-3 field `C₃`: `algebraicGap MℝLinCLM F4Kℝ C₃ u₁ = 6 − C₃(4)`, where `4 = MℝLinCLM u₁`. So the rate is 2 only when `C₃(4) = 4`, as for `F3Kℝ`."
  impl EBCMCategory.MarginalisationDynamicalGap.algebraicGap_witness

@[sa_forward "MarginalisationDynamicalGap.algebraicGapWitness" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.algebraicGapWitness") : S1 :=
  fun C₃ => h C₃

sa_fail_forward "MarginalisationDynamicalGap.algebraicGapWitness" 2 "S2 (MℝLinCLM u₁ = 4) is the real arithmetic 1 + 3 = 4 at u₁. It is used inside impl's proof (the local fact hM), not stated by impl, and it is not structural."

sa_fail_forward "MarginalisationDynamicalGap.algebraicGapWitness" 3 "S3 (a rate of 2 forces C₃(4) = 4) follows from impl's 6 − C₃(4) only by the real arithmetic 6 − x = 2 ⇒ x = 4 (sub_eq_iff_eq_add, funext on coordinates), which is not structural."

sa_fail_forward "MarginalisationDynamicalGap.algebraicGapWitness" 4 "S4 (F3Kℝ(4) = 4, i.e. 4²/4 = 4 in ℝ) is not stated by impl and is real arithmetic, not structural."

@[sa_backward "MarginalisationDynamicalGap.algebraicGapWitness"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) :
    sa_impl% "MarginalisationDynamicalGap.algebraicGapWitness" :=
  fun C₃ => s1 C₃

end Alignment.Shadows.MarginalisationDynamicalGap.algebraicGapWitness

/-! ## kirkwoodFormMatchesAtWitness (`C3match` unfolds to the implementation's field) -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness

sa_claim "MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness" group "MarginalisationDynamicalGap" required
  text "A non-additive order-3 closure that matches the marginalised order-4 surrogate at the witness: `C₃ v = (c ↦ 3 v(c)² / 8)` is non-additive (`IsKirkwoodForm`) and `M(F4Kℝ u₁) = C₃(M u₁)`, since `3·4²/8 = 6`. So \"no Kirkwood-form order-3 closure matches at `u₁`\" is false."
  impl EBCMCategory.MarginalisationDynamicalGap.kirkwoodForm_matches_at_witness

@[sa_forward "MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness") : S1 :=
  h.1

sa_fail_forward "MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness" 2 "impl states algebraicGap MℝLinCLM F4Kℝ C3match u₁ = 0, i.e. M(F4Kℝ u₁) − C3match(M u₁) = 0. S2 is the equation M(F4Kℝ u₁) = C3match(M u₁). Going from the zero difference to the equation needs sub_eq_zero (a library lemma), which is not structural."

sa_fail_forward "MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness" 3 "S3 (some Kirkwood-form order-3 closure matches at u₁) needs the matching equation M(F4Kℝ u₁) = C.C(M u₁). impl gives only the zero algebraic gap, and the step from a zero difference to the equation needs sub_eq_zero, which is not structural."

sa_fail_backward "MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness" "impl's second conjunct is algebraicGap … = 0. From S2's equation it needs x − x = 0 in Idx3 → ℝ (sub_self), which is a library lemma, not structural. The first conjunct is S1."

end Alignment.Shadows.MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness

/-! ## witnessLocalSolutionsExist -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.witnessLocalSolutionsExist

sa_claim "MarginalisationDynamicalGap.witnessLocalSolutionsExist" group "MarginalisationDynamicalGap" required
  text "**Local solutions exist at the witness.** `t ↦ (exp (3 (eᵗ − 1)), 3 eᵗ)` solves `F4Kℝ` (`a' = a b`, `b' = b`) from `u₁ = (1, 3)` for every `t`, and `t ↦ (c ↦ 4 / (1 − t))` solves `F3Kℝ` (`v' = v²/4`) from `MℝLinCLM u₁ = 4` on `(-1, 1)`."
  impl EBCMCategory.MarginalisationDynamicalGap.witness_local_solutions_exist

sa_fail_forward "MarginalisationDynamicalGap.witnessLocalSolutionsExist" 1 "impl witness_local_solutions_exist is existential (∃ ψ₄ ψ₃ with IsLocalSolution on radius 1); the curves (exp(3(eᵗ − 1)), 3eᵗ) and 4/(1 − t) appear only in its proof. S1 says the named curve psi4w solves F4Kℝ for every t (a global IsSolution), which neither follows from the existential nor from a local solution on (−1, 1)."

sa_fail_forward "MarginalisationDynamicalGap.witnessLocalSolutionsExist" 2 "S2 (psi3w 0 = MℝLinCLM u₁, i.e. 4/(1 − 0) = 1 + 3) is about the named curve and is real arithmetic. impl's existential does not name the curve."

sa_fail_forward "MarginalisationDynamicalGap.witnessLocalSolutionsExist" 3 "S3 (the named curve 4/(1 − t) solves F3Kℝ on (−1, 1)) is about a curve that impl's existential does not name, so it does not follow from impl's statement."

sa_fail_backward "MarginalisationDynamicalGap.witnessLocalSolutionsExist" "With the witnesses psi4w and psi3w, impl needs IsLocalSolution … 1 …, whose first field is 0 < (1 : ℝ) (zero_lt_one, not structural). The order-3 part also needs |t| < 1 ⇒ −1 < t ∧ t < 1 (abs_lt), a library lemma, to use S3. Not structurally derivable."

end Alignment.Shadows.MarginalisationDynamicalGap.witnessLocalSolutionsExist

/-! ## witnessLocalGapHasDerivAt (`cst 2` is `fun _ => 2`) -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.witnessLocalGapHasDerivAt

sa_claim "MarginalisationDynamicalGap.witnessLocalGapHasDerivAt" group "MarginalisationDynamicalGap" required
  text "**Theorem T5 Corollary, local form.** For any local solutions `ψ₄` of `F4Kℝ` through `u₁ = (1, 3)` and `ψ₃` of `F3Kℝ` through `MℝLinCLM u₁`, the gap `t ↦ M(ψ₄ t) − ψ₃ t` has derivative `2` (in every coordinate) at `t = 0`."
  impl EBCMCategory.MarginalisationDynamicalGap.witness_localGap_hasDerivAt

@[sa_forward "MarginalisationDynamicalGap.witnessLocalGapHasDerivAt" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.witnessLocalGapHasDerivAt") : S1 := by
  intro ψ₄ ψ₃ h₄ h₃
  obtain ⟨h40, δ₄, hδ₄, hd4⟩ := h₄
  obtain ⟨h30, δ₃, hδ₃, hd3⟩ := h₃
  exact h ⟨hδ₄, h40, hd4⟩ ⟨hδ₃, h30, hd3⟩

@[sa_backward "MarginalisationDynamicalGap.witnessLocalGapHasDerivAt"]
theorem bwd (s1 : S1) : sa_impl% "MarginalisationDynamicalGap.witnessLocalGapHasDerivAt" := by
  intro δ₄ δ₃ ψ₄ ψ₃ h₄ h₃
  exact s1 ψ₄ ψ₃ ⟨h₄.2.1, δ₄, h₄.1, h₄.2.2⟩ ⟨h₃.2.1, δ₃, h₃.1, h₃.2.2⟩

end Alignment.Shadows.MarginalisationDynamicalGap.witnessLocalGapHasDerivAt

/-! ## witnessLocalGapGe (`∃ T > 0, P T` unfolds to `∃ T, 0 < T ∧ P T`) -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.witnessLocalGapGe

sa_claim "MarginalisationDynamicalGap.witnessLocalGapGe" group "MarginalisationDynamicalGap" required
  text "**Theorem T7 Corollary, local form.** For any local solutions `ψ₄` of `F4Kℝ` through `u₁` and `ψ₃` of `F3Kℝ` through `MℝLinCLM u₁`, there is `T > 0` with `t ≤ ‖M(ψ₄ t) − ψ₃ t‖` for all `0 < t ≤ T`. In particular the marginalised order-4 trajectory and the order-3 trajectory differ at every such `t`."
  impl EBCMCategory.MarginalisationDynamicalGap.witness_localGap_ge

@[sa_forward "MarginalisationDynamicalGap.witnessLocalGapGe" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.witnessLocalGapGe") : S1 := by
  intro ψ₄ ψ₃ h₄ h₃
  obtain ⟨h40, δ₄, hδ₄, hd4⟩ := h₄
  obtain ⟨h30, δ₃, hδ₃, hd3⟩ := h₃
  exact h ⟨hδ₄, h40, hd4⟩ ⟨hδ₃, h30, hd3⟩

sa_fail_forward "MarginalisationDynamicalGap.witnessLocalGapGe" 2 "S2 (the trajectories differ on some (0, T]) follows from impl's t ≤ ‖M(ψ₄ t) − ψ₃ t‖ with t > 0 only through norm_pos_iff / sub_ne_zero and order reasoning (0 < t ≤ ‖x‖ ⇒ x ≠ 0), which are library lemmas, not structural. impl does not state the disequality."

@[sa_backward "MarginalisationDynamicalGap.witnessLocalGapGe"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "MarginalisationDynamicalGap.witnessLocalGapGe" := by
  intro δ₄ δ₃ ψ₄ ψ₃ h₄ h₃
  exact s1 ψ₄ ψ₃ ⟨h₄.2.1, δ₄, h₄.1, h₄.2.2⟩ ⟨h₃.2.1, δ₃, h₃.1, h₃.2.2⟩

end Alignment.Shadows.MarginalisationDynamicalGap.witnessLocalGapGe

/-! ## trajectoryGapRateTwoAtWitness.b -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness_b

sa_claim "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b" group "MarginalisationDynamicalGap" required
  text "**Vacuity.** The hypothesis `IsFlow F3Kℝ φ₃` cannot be satisfied: `F3Kℝ` has no global flow (`no_flow_F3Kℝ`; from `v(c) = 4` the solution `4/(1 − t)` blows up at `t = 1`)."
  impl EBCMCategory.MarginalisationDynamicalGap.no_flow_F3Kℝ

@[sa_forward "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b") :
    S1 := fun φ₃ => h φ₃

sa_fail_forward "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b" 2 "impl no_flow_F3Kℝ states only that F3Kℝ has no global flow. S2 (every solution of w′ = w²/4 from w(0) = 4 is 4/(1 − t) before t = 1) is a uniqueness statement for the scalar IVP; it appears in impl's docstring and proof idea but not in its statement."

sa_fail_forward "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b" 3 "S3 (4/(1 − t) → ∞ as t → 1⁻) is a limit statement that impl does not make; impl's statement is only the non-existence of a global flow."

@[sa_backward "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) :
    sa_impl% "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b" := fun φ₃ => s1 φ₃

end Alignment.Shadows.MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness_b

/-! ## noGlobalSolutionSqDivFour -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.noGlobalSolutionSqDivFour

sa_claim "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour" group "MarginalisationDynamicalGap" required
  text "There is no real function `w` with `w 0 = 4` and `HasDerivAt w (w t ^ 2 / 4) t` for every `t : ℝ`: the solution of this initial-value problem, `4/(1 − t)`, blows up at `t = 1`."
  impl EBCMCategory.MarginalisationDynamicalGap.no_global_solution_sq_div_four

@[sa_forward "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour") : S1 :=
  fun hex => hex.elim fun w hw => h w hw.1 hw.2

sa_fail_forward "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour" 2 "impl states only that no global solution exists. S2 (t ↦ 4/(1 − t) solves w′ = w²/4 for t < 1) is a derivative computation that impl does not state."

sa_fail_forward "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour" 3 "S3 (the solution from w(0) = 4 is 4/(1 − t) before t = 1: uniqueness for the IVP) is not stated by impl, whose conclusion is False under the global-solution hypotheses."

sa_fail_forward "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour" 4 "S4 (4/(1 − t) blows up as t → 1⁻) is a limit statement that impl does not make."

@[sa_backward "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) :
    sa_impl% "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour" :=
  fun w h0 hd => s1 ⟨w, h0, hd⟩

end Alignment.Shadows.MarginalisationDynamicalGap.noGlobalSolutionSqDivFour

/-! ## noFlowF3Real -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.noFlowF3Real

sa_claim "MarginalisationDynamicalGap.noFlowF3Real" group "MarginalisationDynamicalGap" required
  text "**No global flow of `F3Kℝ`.** The order-3 Kirkwood witness field `F3Kℝ v = (c ↦ v(c)²/4)` has no flow in the sense of `IsFlow`, which requires solutions for all `t ∈ ℝ`."
  impl EBCMCategory.MarginalisationDynamicalGap.no_flow_F3Kℝ

@[sa_forward "MarginalisationDynamicalGap.noFlowF3Real" 1]
theorem fwd1 (h : sa_impl% "MarginalisationDynamicalGap.noFlowF3Real") : S1 := fun φ₃ => h φ₃

sa_fail_forward "MarginalisationDynamicalGap.noFlowF3Real" 2 "S2 (F3Kℝ v at c is v(c)²/4) is the definition of F3Kℝ (it holds by rfl). impl no_flow_F3Kℝ does not state it, so a checker could only prove S2 without h (vacuous)."

@[sa_backward "MarginalisationDynamicalGap.noFlowF3Real"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "MarginalisationDynamicalGap.noFlowF3Real" :=
  fun φ₃ => s1 φ₃

end Alignment.Shadows.MarginalisationDynamicalGap.noFlowF3Real

/-! ## `MarginalisationDynamicalGap.header.T6.b` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.header_T6_b

sa_claim "MarginalisationDynamicalGap.header.T6.b" group "MarginalisationDynamicalGap"
  text "and the Kirkwood surrogate F3Kℝ, which does not. Other non-additive order-3 closures do match at that state: `c ↦ 3c²/8` gives 6 (`kirkwoodForm_matches_at_witness`)."
  impl

end Alignment.Shadows.MarginalisationDynamicalGap.header_T6_b

/-! ## `MarginalisationDynamicalGap.refinementFailureExists.c` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.refinementFailureExists_c

sa_claim "MarginalisationDynamicalGap.refinementFailureExists.c" group "MarginalisationDynamicalGap"
  text "T6 does not explain the empirical B(c) phase reversal. T3b (via T4) shows only that no order-3 field commutes with `F4Kℝ` under `MℝLin` at every state."
  impl

end Alignment.Shadows.MarginalisationDynamicalGap.refinementFailureExists_c
