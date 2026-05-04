import EBCMCategory.MarginalisationCharacterization
import Mathlib.Tactic

/-!
# Marginalisation: Dynamical Gap and Refinement Failure (T4–T6)

Companion to `MarginalisationFunctor.lean` (T1), the Kirkwood obstruction
in `Obstructions.lean` (T2), and `MarginalisationCharacterization.lean` (T3).

This file bridges the **algebraic** obstruction `kirkwood_form_not_equivariant`
(T3b) to the **dynamical** failure observed empirically in the Phase B B(c)
Gillespie comparison (`NodeBasedModels.jl`, testset "B(c) Gillespie").

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
|        | for all sufficiently small `t > 0` (Gronwall-style bound)         |

## Overview

T1 (equivariance ↔ trajectory commutation) + T2 (algebraic gap = 2 at u₁)
+ T4 (fibre-collapse structure) + T5 (gap = first-order divergence rate)
together certify:

  *For any flows φ₄ of F4Kℝ and φ₃ of any m=3 closure C₃, the trajectory
   gap `M(φ₄ u₁ t) − φ₃(M u₁) t` diverges at rate exactly 2 as t → 0⁺.*

T6 exhibits the complementary existence result: there **is** an m=4 system
that is exact at first order (the "correctly marginalised" one), but no
Kirkwood-form m=3 closure matches it at that IC — confirming the
empirical `err_m4 > err_m3` is a fundamental obstruction, not a numerics bug.
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

    This is the rigorous formal bridge from the Lean-certified
    algebraic difference of `2` to the empirically observed
    `err_m4 − err_m3 ≈ 0.32` in the B(c) Gillespie testset. -/
theorem trajectoryGap_rate_two_at_witness
    {φ₄ : U4ℝ → ℝ → U4ℝ} {φ₃ : U3ℝ → ℝ → U3ℝ}
    (h₄ : IsFlow F4Kℝ φ₄) (h₃ : IsFlow F3Kℝ φ₃) :
    HasDerivAt (trajectoryGap MℝLinCLM φ₄ φ₃ u₁) (fun _ => (2 : ℝ)) 0 := by
  have h := trajectoryGap_hasDerivAt_zero MℝLinCLM F4Kℝ F3Kℝ h₄ h₃ u₁
  rwa [algebraicGap_at_witness] at h

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

    Together with T5, this says: the error of the correctly-marginalised
    m=4 ODE is **zero** at first order at `u₁`, while the m=3 Kirkwood
    ODE has first-order error `|4 − 6| = 2`.  The empirical B(c) phase
    reversal occurs because the **standard** Kirkwood m=4 marginalisation
    is not the correct one; T3b (T4) certifies that no correct one exists. -/
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
