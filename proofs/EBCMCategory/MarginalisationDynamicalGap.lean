import EBCMCategory.MarginalisationCharacterization
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

/-!
# Marginalisation: Dynamical Gap and Refinement Failure (T4–T6)

Companion to `MarginalisationFunctor.lean` (T1), the Kirkwood obstruction
in `Obstructions.lean` (T2), and `MarginalisationCharacterization.lean` (T3).

This file relates the **algebraic** obstruction `kirkwood_form_not_equivariant`
(T3b) to the first-order behaviour of trajectories of the surrogate fields.
No formal object refers to the Phase B B(c) Gillespie comparison
(`NodeBasedModels.jl`), which motivated it; nothing here explains that
experiment.

| Result | Statement                                                        |
|--------|------------------------------------------------------------------|
| T4     | `fibre_collapse_obstruction`: abstract reusable structural lemma  |
|        | (lifts the inlined argument in T3b to a named theorem)            |
| T5     | `trajectoryGap_hasDerivAt_zero`: algebraic gap = first-order      |
|        | trajectory divergence rate; specialised to the (2,1) witness      |
| T6     | `refinement_failure_exists`: there exist Kirkwood-form closures   |
|        | where the m=4 marginalisation is *exact* at first order while     |
|        | the m=3 Kirkwood closure deviates, exhibiting the phase reversal  |
| T7     | `trajectoryGap_norm_ge_half_eps_t`: quantitative lower bound:     |
|        | if `‖algebraicGap‖ ≥ ε > 0` then `‖trajectoryGap u t‖ ≥ εt/2`   |
|        | for all sufficiently small `t > 0` (little-o bound)               |
| T5ℓ    | `localGap_hasDerivAt_zero`: T5 for local solutions                |
| T7ℓ    | `localGap_norm_ge_half_eps_t`: T7 for local solutions             |

## Overview

T2 (algebraic gap = 2 at u₁) + T5 (gap = first-order divergence rate) give,
in local form:

  *For any local solutions ψ₄ of F4Kℝ from u₁ and ψ₃ of F3Kℝ from M u₁, the
   trajectory gap `M(ψ₄ t) − ψ₃ t` has derivative exactly 2 at t = 0
   (`witness_localGap_hasDerivAt`), and its norm is at least t for all
   small t > 0 (`witness_localGap_ge`).*

Such local solutions exist (`witness_local_solutions_exist`). For another
order-3 closure C₃ the first-order rate is 6 − C₃(4) (`algebraicGap_witness`),
not 2. The global-flow versions (T1 and `trajectoryGap_rate_two_at_witness`)
are vacuous at this witness, because F3Kℝ has no global flow (`no_flow_F3Kℝ`).

T6 exhibits an existence result at one state: an order-3 right-hand side
`F3_exact` (the constant 6, fitted to `M(F4Kℝ u₁)`) that agrees with the
marginalised order-4 surrogate at `u₁`,
and the Kirkwood surrogate F3Kℝ, which does not. Other non-additive
order-3 closures do match at that state: `c ↦ 3c²/8` gives 6
(`kirkwoodForm_matches_at_witness`).
So T6 says nothing about the empirical comparison of `err_m4` and `err_m3`.
-/

namespace EBCMCategory.MarginalisationDynamicalGap

open EBCMCategory.Marginalisation
open EBCMCategory.MarginalisationCharacterization
open MarginalisationObstruction

/-! ## T4 — Abstract fibre-collapse obstruction -/

/-- **Theorem T4 (Fibre-collapse obstruction).** If `M` identifies two
    points (`h_fibre : M u₁ = M u₂`) but `F` splits them apart under `M`
    (`h_split : M (F u₁) ≠ M (F u₂)`), then no order-3 closure family
    `C₃` can make the diagram `M ∘ F = C₃ ∘ M` commute.

    This is the structural engine behind `kirkwood_form_not_equivariant`
    (T3b): the fibre collapse `M u₁ = M u₂` (both coordinate-sums equal 4)
    combined with the split `M(F u₁) ≠ M(F u₂)` (6 ≠ 0) gives the
    obstruction without inspecting the specific numeric values.

    The proof is one line: any `C₃` satisfying `Equivariant M F C₃.C`
    forces `M(F u₁) = C₃(M u₁) = C₃(M u₂) = M(F u₂)`, contradicting
    `h_split`. -/
theorem fibre_collapse_obstruction
    {V₄ V₃ : Type _} [AddCommGroup V₄] [AddCommGroup V₃]
    [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (F : V₄ → V₄)
    (u₁ u₂ : V₄) (h_fibre : M u₁ = M u₂)
    (h_split : M (F u₁) ≠ M (F u₂)) :
    ∀ (C₃ : ClosureFamily V₃), ¬ Equivariant M F C₃.C := fun C₃ hEq =>
  h_split (by rw [hEq u₁, h_fibre, ← hEq u₂])

/-- `kirkwood_form_not_equivariant` (T3b) re-derived via T4:
    the (2,1) ℝ-witness satisfies the fibre-collapse hypothesis. -/
theorem kirkwood_not_equivariant_via_T4 :
    ∀ (C₃ : ClosureFamily U3ℝ), ¬ Equivariant MℝLin F4Kℝ C₃.C :=
  fibre_collapse_obstruction MℝLin F4Kℝ u₁ u₂
    (by funext; simp [MℝLin, u₁, u₂]; norm_num)
    (by intro h; have := congrFun h Idx3.c;
        simp [MℝLin, F4Kℝ, u₁, u₂] at this)

/-! ## T5 — Quantitative dynamical gap -/

section DynamicalGap

variable {V₄ V₃ : Type _}
  [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
  [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]

/-- The algebraic gap `M(F₄ u) − F₃(M u)` is the value of the first-order
    divergence rate between any marginalised m=4 trajectory and any m=3
    trajectory starting from the same image point `M u`.
    Established by T5 below. -/
def algebraicGap (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    (u : V₄) : V₃ :=
  M (F₄ u) - F₃ (M u)

/-- The trajectory deviation at time `t` between the marginalised m=4
    flow and the m=3 flow starting at the same image point `M u`. -/
noncomputable def trajectoryGap (M : V₄ →L[ℝ] V₃)
    (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃)
    (u : V₄) (t : ℝ) : V₃ :=
  M (φ₄ u t) - φ₃ (M u) t

/-- **Theorem T5 (Quantitative dynamical gap).**
    For any flow `φ₄` of `F₄` and any flow `φ₃` of `F₃`, the trajectory
    gap function `t ↦ M(φ₄ u t) − φ₃(M u)(t)` has derivative
    `algebraicGap M F₄ F₃ u = M(F₄ u) − F₃(M u)` at `t = 0`.

    **Proof.** Differentiate the two summands at `t = 0`:
    * `d/dt M(φ₄ u t)|₀ = M(F₄ (φ₄ u 0)) = M(F₄ u)` (by the flow
      property of `φ₄` and continuity of `M`).
    * `d/dt φ₃(M u)(t)|₀ = F₃(φ₃(M u)(0)) = F₃(M u)` (by the flow
      property of `φ₃`).
    Subtract via `HasDerivAt.sub`. -/
theorem trajectoryGap_hasDerivAt_zero
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃}
    (h₄ : IsFlow F₄ φ₄) (h₃ : IsFlow F₃ φ₃) (u : V₄) :
    HasDerivAt (trajectoryGap M φ₄ φ₃ u) (algebraicGap M F₄ F₃ u) 0 := by
  have hφ : HasDerivAt (φ₄ u) (F₄ u) 0 := by
    have := h₄.2 u 0; rwa [h₄.1 u] at this
  have hψ : HasDerivAt (φ₃ (M u)) (F₃ (M u)) 0 := by
    have := h₃.2 (M u) 0; rwa [h₃.1 (M u)] at this
  have h_lhs : HasDerivAt (fun t => M (φ₄ u t)) (M (F₄ u)) 0 :=
    M.hasFDerivAt.comp_hasDerivAt 0 hφ
  show HasDerivAt (fun t => M (φ₄ u t) - φ₃ (M u) t) (M (F₄ u) - F₃ (M u)) 0
  exact h_lhs.sub hψ

/-- The trajectory gap vanishes at `t = 0`. -/
lemma trajectoryGap_at_zero
    (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃}
    (h₄ : IsFlow F₄ φ₄) (h₃ : IsFlow F₃ φ₃) (u : V₄) :
    trajectoryGap M φ₄ φ₃ u 0 = 0 := by
  simp only [trajectoryGap, h₄.1 u, h₃.1 (M u), sub_self]

/-- **Theorem T7 (Quantitative lower bound on trajectory gap).**
    If the algebraic gap has norm at least `ε > 0`, then for all small enough
    `t > 0` the trajectory gap satisfies `‖trajectoryGap M φ₄ φ₃ u t‖ ≥ ε * t / 2`.

    **Proof.** By T5 the map `f := trajectoryGap M φ₄ φ₃ u` satisfies
    `HasDerivAt f g 0` where `g := algebraicGap M F₄ F₃ u`.  Since `f 0 = 0`,
    the `isLittleO` characterisation of differentiability gives
    `(fun t => f t - t • g) =o[𝓝 0] id`. Choosing `c = ε/2` yields a radius
    `δ > 0` on which the residual is bounded by `ε/2 * t`, and then the
    reverse triangle inequality `‖t • g‖ - ‖f t‖ ≤ ‖f t - t • g‖` together
    with `‖t • g‖ = t * ‖g‖ ≥ ε * t` gives the result. -/
theorem trajectoryGap_norm_ge_half_eps_t
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃}
    (h₄ : IsFlow F₄ φ₄) (h₃ : IsFlow F₃ φ₃)
    (u : V₄) {ε : ℝ} (hε : 0 < ε)
    (h_gap : ε ≤ ‖algebraicGap M F₄ F₃ u‖) :
    ∃ T > 0, ∀ t, 0 < t → t ≤ T → ε * t / 2 ≤ ‖trajectoryGap M φ₄ φ₃ u t‖ := by
  set f := trajectoryGap M φ₄ φ₃ u
  set g := algebraicGap M F₄ F₃ u
  have hf0 : f 0 = 0 := trajectoryGap_at_zero M h₄ h₃ u
  have h5 : HasDerivAt f g 0 := trajectoryGap_hasDerivAt_zero M F₄ F₃ h₄ h₃ u
  have hlit : (fun t => f t - t • g) =o[nhds (0 : ℝ)] (fun t => t) := by
    have h := h5.isLittleO
    simp only [hf0, sub_zero] at h
    exact h
  rw [Asymptotics.isLittleO_iff] at hlit
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp (hlit (half_pos hε))
  refine ⟨δ / 2, half_pos hδ_pos, fun t ht_pos ht_le => ?_⟩
  have hdist : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht_pos]; linarith
  have hresid : ‖f t - t • g‖ ≤ ε / 2 * ‖(t : ℝ)‖ := hδ hdist
  rw [Real.norm_eq_abs, abs_of_pos ht_pos] at hresid
  have htg : ‖t • g‖ = t * ‖g‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
  have hnormtg : ε * t ≤ ‖t • g‖ := by
    rw [htg]; nlinarith [mul_le_mul_of_nonneg_right h_gap ht_pos.le]
  have hrtri : ‖t • g‖ - ‖f t‖ ≤ ‖f t - t • g‖ := by
    have h1 := norm_sub_norm_le (t • g) (f t)
    rw [norm_sub_rev] at h1
    exact h1
  linarith

/-- If `f 0 = 0`, `f` has derivative `g` at `0` and `ε ≤ ‖g‖` with `ε > 0`,
    then `ε * t / 2 ≤ ‖f t‖` for all small enough `t > 0`. This is the
    little-o argument behind T7, for an arbitrary curve `f`. -/
theorem norm_ge_half_eps_t_of_hasDerivAt {f : ℝ → V₃} {g : V₃}
    (hf0 : f 0 = 0) (hd : HasDerivAt f g 0) {ε : ℝ} (hε : 0 < ε)
    (h_gap : ε ≤ ‖g‖) :
    ∃ T > 0, ∀ t, 0 < t → t ≤ T → ε * t / 2 ≤ ‖f t‖ := by
  have hlit : (fun t => f t - t • g) =o[nhds (0 : ℝ)] (fun t => t) := by
    have h := hd.isLittleO
    simp only [hf0, sub_zero] at h
    exact h
  rw [Asymptotics.isLittleO_iff] at hlit
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp (hlit (half_pos hε))
  refine ⟨δ / 2, half_pos hδ_pos, fun t ht_pos ht_le => ?_⟩
  have hdist : dist t 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht_pos]; linarith
  have hresid : ‖f t - t • g‖ ≤ ε / 2 * ‖(t : ℝ)‖ := hδ hdist
  rw [Real.norm_eq_abs, abs_of_pos ht_pos] at hresid
  have htg : ‖t • g‖ = t * ‖g‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
  have hnormtg : ε * t ≤ ‖t • g‖ := by
    rw [htg]; nlinarith [mul_le_mul_of_nonneg_right h_gap ht_pos.le]
  have hrtri : ‖t • g‖ - ‖f t‖ ≤ ‖f t - t • g‖ := by
    have h1 := norm_sub_norm_le (t • g) (f t)
    rw [norm_sub_rev] at h1
    exact h1
  linarith

/-- **Theorem T5, local form.** For any local solutions `ψ₄` of `F₄` through
    `u` and `ψ₃` of `F₃` through `M u` (`IsLocalSolution`), the gap
    `t ↦ M (ψ₄ t) − ψ₃ t` has derivative `algebraicGap M F₄ F₃ u` at `t = 0`.
    No global flow is assumed, so this applies to fields whose solutions
    blow up in finite time. -/
theorem localGap_hasDerivAt_zero
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (u : V₄)
    {δ₄ δ₃ : ℝ} {ψ₄ : ℝ → V₄} {ψ₃ : ℝ → V₃}
    (h₄ : IsLocalSolution F₄ u δ₄ ψ₄) (h₃ : IsLocalSolution F₃ (M u) δ₃ ψ₃) :
    HasDerivAt (fun t => M (ψ₄ t) - ψ₃ t) (algebraicGap M F₄ F₃ u) 0 := by
  obtain ⟨hδ₄, h₄0, h₄d⟩ := h₄
  obtain ⟨hδ₃, h₃0, h₃d⟩ := h₃
  have hφ : HasDerivAt ψ₄ (F₄ u) 0 := by
    have := h₄d 0 (by simpa using hδ₄); rwa [h₄0] at this
  have hψ : HasDerivAt ψ₃ (F₃ (M u)) 0 := by
    have := h₃d 0 (by simpa using hδ₃); rwa [h₃0] at this
  have h_lhs : HasDerivAt (fun t => M (ψ₄ t)) (M (F₄ u)) 0 :=
    M.hasFDerivAt.comp_hasDerivAt 0 hφ
  show HasDerivAt (fun t => M (ψ₄ t) - ψ₃ t) (M (F₄ u) - F₃ (M u)) 0
  exact h_lhs.sub hψ

/-- **Theorem T7, local form.** If `‖algebraicGap M F₄ F₃ u‖ ≥ ε > 0`, then
    for any local solutions `ψ₄` of `F₄` through `u` and `ψ₃` of `F₃`
    through `M u`, `‖M (ψ₄ t) − ψ₃ t‖ ≥ ε * t / 2` for all small enough
    `t > 0`. -/
theorem localGap_norm_ge_half_eps_t
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (u : V₄)
    {δ₄ δ₃ : ℝ} {ψ₄ : ℝ → V₄} {ψ₃ : ℝ → V₃}
    (h₄ : IsLocalSolution F₄ u δ₄ ψ₄) (h₃ : IsLocalSolution F₃ (M u) δ₃ ψ₃)
    {ε : ℝ} (hε : 0 < ε) (h_gap : ε ≤ ‖algebraicGap M F₄ F₃ u‖) :
    ∃ T > 0, ∀ t, 0 < t → t ≤ T → ε * t / 2 ≤ ‖M (ψ₄ t) - ψ₃ t‖ :=
  norm_ge_half_eps_t_of_hasDerivAt (f := fun t => M (ψ₄ t) - ψ₃ t)
    (by simp [h₄.2.1, h₃.2.1]) (localGap_hasDerivAt_zero M F₄ F₃ u h₄ h₃) hε h_gap

end DynamicalGap

/-! ### Witness corollary for T5 -/

-- Fintype instances are needed so that `Idx4 → ℝ` and `Idx3 → ℝ` carry
-- the Pi norm (making them NormedAddCommGroup / NormedSpace ℝ).
instance : Fintype Idx4 where
  elems := {.a, .b}
  complete := by intro x; cases x; simp; simp

instance : Fintype Idx3 where
  elems := {.c}
  complete := by intro x; cases x; simp

/-- The order-3 Kirkwood-form RHS: `v(c)²/4`. -/
noncomputable def F3Kℝ : U3ℝ → U3ℝ := fun v => fun _ => (v .c) ^ 2 / 4

/-- `MℝLin` promoted to a continuous linear map.
    Continuity holds since `U4ℝ = Idx4 → ℝ` is finite-dimensional:
    each output component `fun u => u .a + u .b` is continuous by
    pointwise evaluation. -/
noncomputable def MℝLinCLM : U4ℝ →L[ℝ] U3ℝ :=
  ⟨MℝLin, by
    show Continuous (fun u : U4ℝ => fun _ : Idx3 => u Idx4.a + u Idx4.b)
    exact continuous_pi fun _ =>
      (continuous_apply Idx4.a).add (continuous_apply Idx4.b)⟩

/-- Application lemma: `MℝLinCLM u i = u Idx4.a + u Idx4.b` for any `i : Idx3`. -/
@[simp]
lemma MℝLinCLM_apply (u : U4ℝ) (i : Idx3) : MℝLinCLM u i = u Idx4.a + u Idx4.b := rfl

/-- At `u₁ = (1, 3)` with the Kirkwood m=3 closure `F3Kℝ`, the algebraic
    gap equals the constant vector `2` in `U3ℝ`. This is the ℝ-valued
    translation of `kirkwood_obstruction_witness_value` (which proved
    the same over ℚ). -/
lemma algebraicGap_at_witness :
    algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = fun _ => (2 : ℝ) := by
  funext i; cases i
  simp only [algebraicGap, Pi.sub_apply, MℝLinCLM_apply, F4Kℝ, F3Kℝ, u₁]
  norm_num

/-- **Theorem T5 Corollary (Divergence rate at the (2,1) witness).**
    For *any* flows `φ₄` of `F4Kℝ` and `φ₃` of `F3Kℝ` (existence is
    a hypothesis, not derived — cf. §3 of `MARGINALISATION_SPEC.md`),
    the trajectory gap at `u₁ = (1, 3)` diverges at rate exactly `2`
    in the `Idx3.c` direction at `t = 0`:

      `M(φ₄ u₁ t) − φ₃(M u₁) t = 2t · ê_c + o(t)`.

    **Vacuity.** The hypothesis `IsFlow F3Kℝ φ₃` cannot be satisfied:
    `F3Kℝ` has no global flow (`no_flow_F3Kℝ`; from `v(c) = 4` the
    solution `4/(1 − t)` blows up at `t = 1`). This theorem is therefore
    vacuously true and is not a formal bridge to the empirically observed
    `err_m4 − err_m3 ≈ 0.32` in the B(c) Gillespie testset. -/
theorem trajectoryGap_rate_two_at_witness
    {φ₄ : U4ℝ → ℝ → U4ℝ} {φ₃ : U3ℝ → ℝ → U3ℝ}
    (h₄ : IsFlow F4Kℝ φ₄) (h₃ : IsFlow F3Kℝ φ₃) :
    HasDerivAt (trajectoryGap MℝLinCLM φ₄ φ₃ u₁) (fun _ => (2 : ℝ)) 0 := by
  have h := trajectoryGap_hasDerivAt_zero MℝLinCLM F4Kℝ F3Kℝ h₄ h₃ u₁
  rwa [algebraicGap_at_witness] at h

/-! ### Vacuity of the order-3 witness flow -/

/-- There is no real function `w` with `w 0 = 4` and
    `HasDerivAt w (w t ^ 2 / 4) t` for every `t : ℝ`: the solution of this
    initial-value problem, `4/(1 − t)`, blows up at `t = 1`. -/
theorem no_global_solution_sq_div_four (w : ℝ → ℝ) (h0 : w 0 = 4)
    (hd : ∀ t, HasDerivAt w (w t ^ 2 / 4) t) : False := by
  have hdiff : Differentiable ℝ w := fun t => (hd t).differentiableAt
  have hmono : Monotone w := by
    apply monotone_of_deriv_nonneg hdiff
    intro t
    rw [(hd t).deriv]
    positivity
  have hge : ∀ t, 0 ≤ t → 4 ≤ w t := fun t ht => h0 ▸ hmono ht
  -- `g t = -4 / w t - t` has zero derivative on `[0, ∞)`, so it is constant there
  set g : ℝ → ℝ := fun t => -4 / w t - t with hg
  have hgd : ∀ t, 0 ≤ t → HasDerivAt g 0 t := by
    intro t ht
    have hw : w t ≠ 0 := by linarith [hge t ht]
    have h1 : HasDerivAt (fun s => -4 / w s) (4 * (w t ^ 2 / 4) / (w t) ^ 2) t := by
      have := ((hd t).inv hw).const_mul (-4)
      convert this using 1
      ring
    have h2 := h1.sub (hasDerivAt_id t)
    convert h2 using 1
    field_simp
    ring
  have hcont : ContinuousOn g (Set.Icc 0 1) := fun t ht =>
    (hgd t ht.1).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hgd t ht.1).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
  simp only [hg, h0] at hconst
  -- `g 1 = g 0` gives `4 / w 1 = 0`, contradicting `w 1 ≥ 4`
  have hw1pos : 0 < w 1 := by linarith [hge 1 zero_le_one]
  have e1 : (-4 : ℝ) / w 1 = -(4 / w 1) := neg_div _ _
  have e2 : (-4 : ℝ) / 4 - 0 = -1 := by norm_num
  rw [e1, e2] at hconst
  have : 0 < 4 / w 1 := by positivity
  linarith

/-- **No global flow of `F3Kℝ`.** The order-3 Kirkwood witness field
    `F3Kℝ v = (c ↦ v(c)²/4)` has no flow in the sense of `IsFlow`, which
    requires solutions for all `t ∈ ℝ`. From `v(c) = 4` the solution is
    `4/(1 − t)`, which blows up at `t = 1`. Hence `IsFlow F3Kℝ φ₃` is
    unsatisfiable, and every theorem that assumes it (such as
    `trajectoryGap_rate_two_at_witness`) holds vacuously. -/
theorem no_flow_F3Kℝ (φ₃ : U3ℝ → ℝ → U3ℝ) : ¬ IsFlow F3Kℝ φ₃ := by
  intro ⟨h0, hd⟩
  let v : U3ℝ := fun _ => 4
  apply no_global_solution_sq_div_four (fun t => φ₃ v t .c)
  · simp [h0 v, v]
  · intro t
    have := (hasDerivAt_pi.mp (hd v t)) .c
    simpa [F3Kℝ] using this

/-! ### Local-solution form of the witness corollaries -/

/-- The first-order rate at the witness for an arbitrary order-3 field `C₃`:
    `algebraicGap MℝLinCLM F4Kℝ C₃ u₁ = 6 − C₃(4)`, where `4 = MℝLinCLM u₁`.
    So the rate is 2 only when `C₃(4) = 4`, as for `F3Kℝ`. -/
theorem algebraicGap_witness (C₃ : U3ℝ → U3ℝ) :
    algebraicGap MℝLinCLM F4Kℝ C₃ u₁ = fun i => 6 - C₃ (fun _ => 4) i := by
  have hM : MℝLinCLM u₁ = fun _ => (4 : ℝ) := by
    funext i; simp only [MℝLinCLM_apply, u₁]; norm_num
  funext i
  simp only [algebraicGap, Pi.sub_apply, MℝLinCLM_apply, hM, F4Kℝ, u₁]
  norm_num

/-- A non-additive order-3 closure that matches the marginalised order-4
    surrogate at the witness: `C₃ v = (c ↦ 3 v(c)² / 8)` is non-additive
    (`IsKirkwoodForm`) and `M(F4Kℝ u₁) = C₃(M u₁)`, since `3·4²/8 = 6`. So
    "no Kirkwood-form order-3 closure matches at `u₁`" is false. -/
theorem kirkwoodForm_matches_at_witness :
    (ClosureFamily.mk (fun v : U3ℝ => fun _ => 3 * (v .c) ^ 2 / 8)).IsKirkwoodForm ∧
    algebraicGap MℝLinCLM F4Kℝ (fun v : U3ℝ => fun _ => 3 * (v .c) ^ 2 / 8) u₁ = 0 := by
  refine ⟨⟨fun _ => (1 : ℝ), fun _ => (1 : ℝ), ?_⟩, ?_⟩
  · intro h
    have h_c := congrFun h Idx3.c
    simp only [Pi.add_apply] at h_c
    norm_num at h_c
  · rw [algebraicGap_witness]
    funext i
    simp only [Pi.zero_apply]
    norm_num

/-- **Local solutions exist at the witness.** `t ↦ (exp (3 (eᵗ − 1)), 3 eᵗ)`
    solves `F4Kℝ` (`a' = a b`, `b' = b`) from `u₁ = (1, 3)` for every `t`,
    and `t ↦ (c ↦ 4 / (1 − t))` solves `F3Kℝ` (`v' = v²/4`) from
    `MℝLinCLM u₁ = 4` on `(-1, 1)`. So the hypotheses of the local witness
    theorems can be satisfied, unlike `IsFlow F3Kℝ φ₃` (`no_flow_F3Kℝ`). -/
theorem witness_local_solutions_exist :
    ∃ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ),
      IsLocalSolution F4Kℝ u₁ 1 ψ₄ ∧ IsLocalSolution F3Kℝ (MℝLinCLM u₁) 1 ψ₃ := by
  refine ⟨fun t i => match i with
      | .a => Real.exp (3 * (Real.exp t - 1))
      | .b => 3 * Real.exp t,
    fun t _ => 4 / (1 - t), ⟨one_pos, ?_, ?_⟩, ⟨one_pos, ?_, ?_⟩⟩
  · funext i; cases i <;> simp [u₁]
  · intro t _
    rw [hasDerivAt_pi]
    intro i
    cases i
    · show HasDerivAt (fun t => Real.exp (3 * (Real.exp t - 1)))
        (Real.exp (3 * (Real.exp t - 1)) * (3 * Real.exp t)) t
      exact (((Real.hasDerivAt_exp t).sub_const 1).const_mul 3).exp
    · show HasDerivAt (fun t => 3 * Real.exp t) (3 * Real.exp t) t
      exact (Real.hasDerivAt_exp t).const_mul 3
  · funext i; simp only [MℝLinCLM_apply, u₁]; norm_num
  · intro t ht
    have ht1 : t < 1 := (abs_lt.mp ht).2
    have hne : (1 : ℝ) - t ≠ 0 := by linarith
    rw [hasDerivAt_pi]
    intro i
    show HasDerivAt (fun t : ℝ => 4 / (1 - t)) ((4 / (1 - t)) ^ 2 / 4) t
    have h := (hasDerivAt_const t (4 : ℝ)).div ((hasDerivAt_const t (1 : ℝ)).sub
      (hasDerivAt_id' t)) hne
    convert h using 1
    simp only [Pi.sub_apply]
    field_simp
    ring

/-- **Theorem T5 Corollary, local form.** For any local solutions `ψ₄` of
    `F4Kℝ` through `u₁ = (1, 3)` and `ψ₃` of `F3Kℝ` through `MℝLinCLM u₁`,
    the gap `t ↦ M(ψ₄ t) − ψ₃ t` has derivative `2` (in every coordinate)
    at `t = 0`. Unlike `trajectoryGap_rate_two_at_witness`, its hypotheses
    can be satisfied (`witness_local_solutions_exist`). -/
theorem witness_localGap_hasDerivAt {δ₄ δ₃ : ℝ} {ψ₄ : ℝ → U4ℝ} {ψ₃ : ℝ → U3ℝ}
    (h₄ : IsLocalSolution F4Kℝ u₁ δ₄ ψ₄)
    (h₃ : IsLocalSolution F3Kℝ (MℝLinCLM u₁) δ₃ ψ₃) :
    HasDerivAt (fun t => MℝLinCLM (ψ₄ t) - ψ₃ t) (fun _ => (2 : ℝ)) 0 := by
  have h := localGap_hasDerivAt_zero MℝLinCLM F4Kℝ F3Kℝ u₁ h₄ h₃
  rwa [algebraicGap_at_witness] at h

/-- **Theorem T7 Corollary, local form.** For any local solutions `ψ₄` of
    `F4Kℝ` through `u₁` and `ψ₃` of `F3Kℝ` through `MℝLinCLM u₁`, there is
    `T > 0` with `t ≤ ‖M(ψ₄ t) − ψ₃ t‖` for all `0 < t ≤ T`. In particular
    the marginalised order-4 trajectory and the order-3 trajectory differ
    at every such `t`. -/
theorem witness_localGap_ge {δ₄ δ₃ : ℝ} {ψ₄ : ℝ → U4ℝ} {ψ₃ : ℝ → U3ℝ}
    (h₄ : IsLocalSolution F4Kℝ u₁ δ₄ ψ₄)
    (h₃ : IsLocalSolution F3Kℝ (MℝLinCLM u₁) δ₃ ψ₃) :
    ∃ T > 0, ∀ t, 0 < t → t ≤ T → t ≤ ‖MℝLinCLM (ψ₄ t) - ψ₃ t‖ := by
  haveI : Nonempty Idx3 := ⟨Idx3.c⟩
  have h_gap : (2 : ℝ) ≤ ‖algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁‖ := by
    rw [algebraicGap_at_witness, pi_norm_const]
    norm_num
  obtain ⟨T, hT, hb⟩ :=
    localGap_norm_ge_half_eps_t MℝLinCLM F4Kℝ F3Kℝ u₁ h₄ h₃ two_pos h_gap
  exact ⟨T, hT, fun t ht htT => by have := hb t ht htT; linarith⟩

/-! ## T6 — Refinement-failure existence -/

/-- `F3Kℝ` is nonlinear (has Kirkwood form): witnessed by `u = v = (c ↦ 1)`,
    where `F3Kℝ(u + v)(c) = 1 ≠ 1/2 = F3Kℝ(u)(c) + F3Kℝ(v)(c)`. -/
lemma F3Kℝ_isKirkwoodForm : (ClosureFamily.mk F3Kℝ).IsKirkwoodForm := by
  refine ⟨fun _ => (1 : ℝ), fun _ => (1 : ℝ), ?_⟩
  intro h
  have h_c := congrFun h Idx3.c
  simp only [F3Kℝ, Pi.add_apply] at h_c
  norm_num at h_c

/-- **Theorem T6 (Refinement-failure existence).**
    There exist Kirkwood-form closures `F4_kirk` (order 4) and
    `F3_kirk` (order 3), an "exact" order-3 RHS `F3_exact`, and an
    initial condition `u₀` such that:

    * the marginalised m=4 chain is **exact at first order**:
        `M(F4_kirk u₀) = F3_exact(M u₀)`  (algebraic gap = 0);
    * the m=3 Kirkwood chain **deviates from exact**:
        `F3_kirk(M u₀) ≠ F3_exact(M u₀)`.

    **Witness.**  `F4_kirk = F4Kℝ`, `F3_kirk = F3Kℝ`,
    `F3_exact = const 6` (the "true" marginalised m=4 RHS at u₁),
    `u₀ = u₁ = (1, 3)`:
    * `M(F4Kℝ u₁)(c) = 1·3 + 3 = 6 = F3_exact(M u₁)(c)`.
    * `F3Kℝ(M u₁)(c) = 4²/4 = 4 ≠ 6`.

    Together with T5: relative to the fitted `F3_exact`, the marginalised
    m=4 surrogate has zero first-order error at `u₁` (by construction),
    while the m=3 Kirkwood surrogate has first-order error `|4 − 6| = 2`.
    T6 does not explain the empirical B(c) phase reversal. T3b (via T4)
    shows only that no order-3 field commutes with `F4Kℝ` under `MℝLin` at
    every state. -/
theorem refinement_failure_exists :
    ∃ (F4_kirk : U4ℝ → U4ℝ) (F3_kirk : U3ℝ → U3ℝ) (F3_exact : U3ℝ → U3ℝ)
      (u₀ : U4ℝ),
      (ClosureFamily.mk F4_kirk).IsKirkwoodForm ∧
      (ClosureFamily.mk F3_kirk).IsKirkwoodForm ∧
      MℝLin (F4_kirk u₀) = F3_exact (MℝLin u₀) ∧
      F3_kirk (MℝLin u₀) ≠ F3_exact (MℝLin u₀) := by
  -- Witness: F4_kirk = F4Kℝ, F3_kirk = F3Kℝ, F3_exact = const 6, u₀ = u₁
  refine ⟨F4Kℝ, F3Kℝ, fun _ _ => (6 : ℝ), u₁,
          C4ℝ_isKirkwoodForm, F3Kℝ_isKirkwoodForm, ?_, ?_⟩
  · -- MℝLin (F4Kℝ u₁) = fun _ _ => 6
    -- i.e. (F4Kℝ u₁) .a + (F4Kℝ u₁) .b = 1·3 + 3 = 6
    funext i; cases i
    simp only [MℝLin, F4Kℝ, u₁, LinearMap.coe_mk, AddHom.coe_mk]
    norm_num
  · -- F3Kℝ (MℝLin u₁) ≠ fun _ _ => 6
    -- i.e. (M u₁ .c)²/4 = 4²/4 = 4 ≠ 6
    intro h
    have h_c := congrFun h Idx3.c
    simp only [F3Kℝ, MℝLin, u₁, LinearMap.coe_mk, AddHom.coe_mk] at h_c
    norm_num at h_c

end EBCMCategory.MarginalisationDynamicalGap
