import Alignment.Registry
import EBCMCategory.MarginalisationDynamicalGap

/-!
# Blind shadow sets: group `MarginalisationDynamicalGap`

Written blind. The author read only `SA-PASS_SKILL.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/MarginalisationDynamicalGap.md` and
this group's entries of `Alignment/claims_blind.yaml`. Types (not bodies) of the DataTypes
vocabulary were learned with `#check`, and their docstrings were read.

Vocabulary used (DataTypes): `IsFlow F φ` ("φ is a flow of F"), `algebraicGap`, `trajectoryGap`,
`F3Kℝ` (the order-3 Kirkwood RHS), `F4Kℝ` (the Kirkwood order-4 RHS at the witness
configuration), `MℝLin` / `MℝLinCLM` (the marginalisation `M`, linear / continuous linear),
`u₁` (the point `(a ↦ 1, b ↦ 3)`), `ClosureFamily` (with field `C`) and `ClosureFamily.mk`,
`ClosureFamily.IsKirkwoodForm`, `Equivariant`, `U4ℝ = Idx4 → ℝ`, `U3ℝ = Idx3 → ℝ`
(`Idx4 = {a, b}`, `Idx3 = {c}`).

Conventions: an "order-3 / m=3 closure" or "RHS" is a map `U3ℝ → U3ℝ`, and an order-4 one is a map
`U4ℝ → U4ℝ`. A "closure family" is a `ClosureFamily`. "Has Kirkwood form" is
`(ClosureFamily.mk F).IsKirkwoodForm`. Because `Idx3` has the single index `c`, the vector
`x · ê_c` of `U3ℝ` is the constant function `fun _ => x`.

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace). Ids of that pass not formalised (remarks on proof status, on which notions the library
defines, or cited results needing models the vocabulary lacks): `header.T6.c`, `header.bridge`.
-/

open EBCMCategory.Marginalisation
open EBCMCategory.MarginalisationCharacterization
open MarginalisationObstruction
open EBCMCategory.MarginalisationDynamicalGap
open Filter Topology

namespace Alignment.Shadows.MarginalisationDynamicalGap

/-- The point `(1, 3)` of `U4ℝ` in primitive terms: `a ↦ 1`, `b ↦ 3` (text: "`u₁ = (1, 3)`"). -/
def pt13 : U4ℝ := fun i =>
  match i with
  | Idx4.a => 1
  | Idx4.b => 3

/-- The point `(c ↦ 1)` of `U3ℝ` (text: "`u = v = (c ↦ 1)`"). -/
def oneC : U3ℝ := fun _ => 1

end Alignment.Shadows.MarginalisationDynamicalGap

/-! ## `MarginalisationDynamicalGap.fibreCollapseObstruction` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.FibreCollapseObstruction

/-! Blind text: "**Theorem T4 (Fibre-collapse obstruction).** If `M` identifies two points
(`h_fibre : M u₁ = M u₂`) but `F` splits them apart under `M` (`h_split : M (F u₁) ≠ M (F u₂)`),
then no order-3 closure family `C₃` can make the diagram `M ∘ F = C₃ ∘ M` commute."

-- AMBIGUITY: the text does not give the type of `M`. It is read in the module's stated setting:
-- real normed spaces `V₄`, `V₃` in arbitrary universes, `M : V₄ →L[ℝ] V₃`, and an arbitrary map
-- `F : V₄ → V₄`. Here `u₁` and `u₂` are arbitrary points (hypothesis names), not the constants
-- `u₁` and `u₂`.
-- The diagram is stated in primitive terms, `⇑M ∘ F = C₃.C ∘ ⇑M`. "No C₃ can make it commute"
-- is read as "for every C₃, not ...".
-/

universe u v

/-- Intended statement (T4). -/
@[sa_reference "MarginalisationDynamicalGap.fibreCollapseObstruction"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F : V₄ → V₄) (w₁ w₂ : V₄),
    M w₁ = M w₂ → M (F w₁) ≠ M (F w₂) →
      ∀ C₃ : ClosureFamily V₃, ¬ ((⇑M ∘ F) = (C₃.C ∘ ⇑M))

/-- S1: the whole statement (a single implication). -/
@[sa_shadow "MarginalisationDynamicalGap.fibreCollapseObstruction" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F : V₄ → V₄) (w₁ w₂ : V₄),
    M w₁ = M w₂ → M (F w₁) ≠ M (F w₂) →
      ∀ C₃ : ClosureFamily V₃, ¬ ((⇑M ∘ F) = (C₃.C ∘ ⇑M))

@[sa_ref_forward "MarginalisationDynamicalGap.fibreCollapseObstruction" 1]
theorem ref_fwd1 : T.{u, v} → S1.{u, v} := fun t => t

@[sa_complete "MarginalisationDynamicalGap.fibreCollapseObstruction"]
theorem complete (s1 : S1.{u, v}) : T.{u, v} := s1

end Alignment.Shadows.MarginalisationDynamicalGap.FibreCollapseObstruction

/-! ## `MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.KirkwoodNotEquivariantViaT4

/-! Blind text: "`kirkwood_form_not_equivariant` (T3b) re-derived via T4: the (2,1) ℝ-witness
satisfies the fibre-collapse hypothesis."

-- AMBIGUITY: the conclusion of T3b is not quoted. It is read, as the conclusion of T4 for the
-- Kirkwood order-4 RHS `F4Kℝ` ("the (2,1) ℝ-witness"), as: no order-3 closure family C₃ makes
-- `MℝLin` intertwine `F4Kℝ` and `C₃.C` (vocabulary `Equivariant`, "M intertwines F and G"). (S1)
-- AMBIGUITY: "the (2,1) ℝ-witness satisfies the fibre-collapse hypothesis": the text does not
-- name the witness points, so the claim is read existentially. Two points of `U4ℝ` are identified
-- by M, and F4Kℝ splits them under M. (S2)
-/

/-- Intended statement: T3b's conclusion, and the fibre-collapse hypothesis holds for `F4Kℝ`. -/
@[sa_reference "MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4"]
def T : Prop :=
  (∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin F4Kℝ C₃.C) ∧
    ∃ w₁ w₂ : U4ℝ, MℝLin w₁ = MℝLin w₂ ∧ MℝLin (F4Kℝ w₁) ≠ MℝLin (F4Kℝ w₂)

/-- S1: `F4Kℝ` is not M-equivariant with any order-3 closure family. -/
@[sa_shadow "MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4" 1]
def S1 : Prop := ∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin F4Kℝ C₃.C

/-- S2: the witness satisfies the fibre-collapse hypothesis (`h_fibre` and `h_split`). -/
@[sa_shadow "MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4" 2]
def S2 : Prop :=
  ∃ w₁ w₂ : U4ℝ, MℝLin w₁ = MℝLin w₂ ∧ MℝLin (F4Kℝ w₁) ≠ MℝLin (F4Kℝ w₂)

@[sa_ref_forward "MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "MarginalisationDynamicalGap.kirkwoodNotEquivariantViaT4"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MarginalisationDynamicalGap.KirkwoodNotEquivariantViaT4

/-! ## `MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapHasDerivAtZero

/-! Blind text: "**Theorem T5 (Quantitative dynamical gap).** For any flow `φ₄` of `F₄` and any
flow `φ₃` of `F₃`, the trajectory gap function `t ↦ M(φ₄ u t) − φ₃(M u)(t)` has derivative
`algebraicGap M F₄ F₃ u = M(F₄ u) − F₃(M u)` at `t = 0`."

Setting: real normed spaces in arbitrary universes, `M : V₄ →L[ℝ] V₃`, and arbitrary vector
fields `F₄`, `F₃` and point `u`. The gap function is written as the text writes it. The derivative
is required both as the vocabulary `algebraicGap M F₄ F₃ u` (S1) and as the explicit
`M(F₄ u) − F₃(M u)` (S2), since the text asserts both.
-/

universe u v

/-- Intended statement (T5). -/
@[sa_reference "MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ w : V₄,
      HasDerivAt (fun t => M (φ₄ w t) - φ₃ (M w) t) (algebraicGap M F₄ F₃ w) 0 ∧
      HasDerivAt (fun t => M (φ₄ w t) - φ₃ (M w) t) (M (F₄ w) - F₃ (M w)) 0

/-- S1: the derivative at `t = 0` is `algebraicGap M F₄ F₃ u`. -/
@[sa_shadow "MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ w : V₄,
      HasDerivAt (fun t => M (φ₄ w t) - φ₃ (M w) t) (algebraicGap M F₄ F₃ w) 0

/-- S2: the derivative at `t = 0` is `M(F₄ u) − F₃(M u)`. -/
@[sa_shadow "MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ w : V₄,
      HasDerivAt (fun t => M (φ₄ w t) - φ₃ (M w) t) (M (F₄ w) - F₃ (M w)) 0

@[sa_ref_forward "MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero" 1]
theorem ref_fwd1 : T.{u, v} → S1.{u, v} := by
  intro t V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h4 h3 w
  exact (t M F₄ F₃ φ₄ φ₃ h4 h3 w).1

@[sa_ref_forward "MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero" 2]
theorem ref_fwd2 : T.{u, v} → S2.{u, v} := by
  intro t V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h4 h3 w
  exact (t M F₄ F₃ φ₄ φ₃ h4 h3 w).2

@[sa_complete "MarginalisationDynamicalGap.trajectoryGapHasDerivAtZero"]
theorem complete (s1 : S1.{u, v}) (s2 : S2.{u, v}) : T.{u, v} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h4 h3 w
  exact ⟨s1 M F₄ F₃ φ₄ φ₃ h4 h3 w, s2 M F₄ F₃ φ₄ φ₃ h4 h3 w⟩

end Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapHasDerivAtZero

/-! ## `MarginalisationDynamicalGap.trajectoryGapAtZero` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapAtZero

/-! Blind text: "The trajectory gap vanishes at `t = 0`."

-- AMBIGUITY: "the trajectory gap" presupposes the setting of T5: flows φ₄ of F₄ and φ₃ of F₃,
-- with M continuous linear between real normed spaces. It is read with `IsFlow` hypotheses, for
-- all vector fields and all points u. The gap is required both through the vocabulary
-- `trajectoryGap` (S1) and through T5's explicit formula `M(φ₄ u t) − φ₃(M u) t` (S2).
-/

universe u v

/-- Intended statement: for flows of any two vector fields, the gap at time 0 is zero. -/
@[sa_reference "MarginalisationDynamicalGap.trajectoryGapAtZero"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ w : V₄,
      trajectoryGap M φ₄ φ₃ w 0 = 0 ∧ M (φ₄ w 0) - φ₃ (M w) 0 = 0

/-- S1: `trajectoryGap M φ₄ φ₃ u 0 = 0`. -/
@[sa_shadow "MarginalisationDynamicalGap.trajectoryGapAtZero" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ w : V₄,
      trajectoryGap M φ₄ φ₃ w 0 = 0

/-- S2: the gap written out, `M(φ₄ u 0) − φ₃(M u) 0 = 0`. -/
@[sa_shadow "MarginalisationDynamicalGap.trajectoryGapAtZero" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ w : V₄,
      M (φ₄ w 0) - φ₃ (M w) 0 = 0

@[sa_ref_forward "MarginalisationDynamicalGap.trajectoryGapAtZero" 1]
theorem ref_fwd1 : T.{u, v} → S1.{u, v} := by
  intro t V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h4 h3 w
  exact (t M F₄ F₃ φ₄ φ₃ h4 h3 w).1

@[sa_ref_forward "MarginalisationDynamicalGap.trajectoryGapAtZero" 2]
theorem ref_fwd2 : T.{u, v} → S2.{u, v} := by
  intro t V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h4 h3 w
  exact (t M F₄ F₃ φ₄ φ₃ h4 h3 w).2

@[sa_complete "MarginalisationDynamicalGap.trajectoryGapAtZero"]
theorem complete (s1 : S1.{u, v}) (s2 : S2.{u, v}) : T.{u, v} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h4 h3 w
  exact ⟨s1 M F₄ F₃ φ₄ φ₃ h4 h3 w, s2 M F₄ F₃ φ₄ φ₃ h4 h3 w⟩

end Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapAtZero

/-! ## `MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapNormGeHalfEpsT

/-! Blind text: "**Theorem T7 (Quantitative lower bound on trajectory gap).** If the algebraic
gap has norm at least `ε > 0`, then for all small enough `t > 0` the trajectory gap satisfies
`‖trajectoryGap M φ₄ φ₃ u t‖ ≥ ε * t / 2`."

-- AMBIGUITY: the text leaves the flows implicit. It is read in the setting of T5: φ₄ a flow of
-- F₄ and φ₃ a flow of F₃, with "the algebraic gap" being `algebraicGap M F₄ F₃ u`.
-- "for all small enough t > 0" is read as `∀ᶠ t in 𝓝[>] 0`, as the DataTypes vocabulary
-- suggests. The threshold may depend on everything quantified before it.
-/

universe u v

/-- Intended statement (T7). -/
@[sa_reference "MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ →
    ∀ (w : V₄) (ε : ℝ), 0 < ε → ‖algebraicGap M F₄ F₃ w‖ ≥ ε →
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ‖trajectoryGap M φ₄ φ₃ w t‖ ≥ ε * t / 2

/-- S1: the whole statement (a single implication). -/
@[sa_shadow "MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ →
    ∀ (w : V₄) (ε : ℝ), 0 < ε → ‖algebraicGap M F₄ F₃ w‖ ≥ ε →
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ‖trajectoryGap M φ₄ φ₃ w t‖ ≥ ε * t / 2

@[sa_ref_forward "MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT" 1]
theorem ref_fwd1 : T.{u, v} → S1.{u, v} := fun t => t

@[sa_complete "MarginalisationDynamicalGap.trajectoryGapNormGeHalfEpsT"]
theorem complete (s1 : S1.{u, v}) : T.{u, v} := s1

end Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapNormGeHalfEpsT

/-! ## `MarginalisationDynamicalGap.mRealLinCLMApply` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.MRealLinCLMApply

/-! Blind text: "Application lemma: `MℝLinCLM u i = u Idx4.a + u Idx4.b` for any `i : Idx3`." -/

/-- Intended statement: for every `u : U4ℝ` and every `i : Idx3`,
`MℝLinCLM u i = u a + u b`. -/
@[sa_reference "MarginalisationDynamicalGap.mRealLinCLMApply"]
def T : Prop := ∀ (w : U4ℝ) (i : Idx3), MℝLinCLM w i = w Idx4.a + w Idx4.b

/-- S1: the whole statement. -/
@[sa_shadow "MarginalisationDynamicalGap.mRealLinCLMApply" 1]
def S1 : Prop := ∀ (w : U4ℝ) (i : Idx3), MℝLinCLM w i = w Idx4.a + w Idx4.b

@[sa_ref_forward "MarginalisationDynamicalGap.mRealLinCLMApply" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MarginalisationDynamicalGap.mRealLinCLMApply"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MarginalisationDynamicalGap.MRealLinCLMApply

/-! ## `MarginalisationDynamicalGap.algebraicGapAtWitness.a` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.AlgebraicGapAtWitness_a

/-! Blind text: "At `u₁ = (1, 3)` with the Kirkwood m=3 closure `F3Kℝ`, the algebraic gap equals
the constant vector `2` in `U3ℝ`."

-- AMBIGUITY: the text does not name M or the m=4 RHS. They are read as the marginalisation
-- `MℝLinCLM` and the Kirkwood order-4 RHS `F4Kℝ` of the witness configuration.
-- The point is stated in primitive terms as `(a ↦ 1, b ↦ 3)` (`pt13`), from "u₁ = (1, 3)".
-- The gap is required both through the vocabulary `algebraicGap` (S1) and as the explicit
-- `M(F₄ u) − F₃(M u)` (S2).
-/

open Alignment.Shadows.MarginalisationDynamicalGap

/-- Intended statement: at `(1, 3)` the algebraic gap `M(F4Kℝ u) − F3Kℝ(M u)` is the constant
vector `2`. -/
@[sa_reference "MarginalisationDynamicalGap.algebraicGapAtWitness.a"]
def T : Prop :=
  algebraicGap MℝLinCLM F4Kℝ F3Kℝ pt13 = (fun _ => (2 : ℝ)) ∧
    MℝLinCLM (F4Kℝ pt13) - F3Kℝ (MℝLinCLM pt13) = (fun _ => (2 : ℝ))

/-- S1: `algebraicGap MℝLinCLM F4Kℝ F3Kℝ (1, 3) = 2`. -/
@[sa_shadow "MarginalisationDynamicalGap.algebraicGapAtWitness.a" 1]
def S1 : Prop := algebraicGap MℝLinCLM F4Kℝ F3Kℝ pt13 = (fun _ => (2 : ℝ))

/-- S2: `M(F4Kℝ (1, 3)) − F3Kℝ(M (1, 3)) = 2`. -/
@[sa_shadow "MarginalisationDynamicalGap.algebraicGapAtWitness.a" 2]
def S2 : Prop := MℝLinCLM (F4Kℝ pt13) - F3Kℝ (MℝLinCLM pt13) = (fun _ => (2 : ℝ))

@[sa_ref_forward "MarginalisationDynamicalGap.algebraicGapAtWitness.a" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MarginalisationDynamicalGap.algebraicGapAtWitness.a" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "MarginalisationDynamicalGap.algebraicGapAtWitness.a"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MarginalisationDynamicalGap.AlgebraicGapAtWitness_a

/-! ## `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapRateTwoAtWitness_a

/-! Blind text: "**Theorem T5 Corollary (Divergence rate at the (2,1) witness).** For *any* flows
`φ₄` of `F4Kℝ` and `φ₃` of `F3Kℝ` (existence is a hypothesis, not derived — cf. §3 of
`MARGINALISATION_SPEC.md`), the trajectory gap at `u₁ = (1, 3)` diverges at rate exactly `2` in
the `Idx3.c` direction at `t = 0`: `M(φ₄ u₁ t) − φ₃(M u₁) t = 2t · ê_c + o(t)`."

-- AMBIGUITY: "diverges at rate exactly 2 in the Idx3.c direction at t = 0: ... = 2t·ê_c + o(t)"
-- is read as a two-sided derivative at t = 0 ("at t = 0", an unqualified o(t)) equal to the
-- vector 2·ê_c. This is the first DataTypes rendering, `HasDerivAt (trajectoryGap …) g 0`.
-- Because the gap vanishes at 0, it is the same as the stated expansion. Since `Idx3 = {c}`,
-- 2·ê_c is `fun _ => 2`.
-- The flows are hypotheses, universally quantified. M is `MℝLinCLM`. The point u₁ = (1, 3) is
-- stated in primitive terms (`pt13`). The gap is required both as the vocabulary `trajectoryGap`
-- ("the trajectory gap", S1) and as the explicit formula (S2).
-/

open Alignment.Shadows.MarginalisationDynamicalGap

/-- Intended statement: for all flows φ₄ of F4Kℝ and φ₃ of F3Kℝ, the gap at `(1, 3)` has
derivative `2·ê_c` at `t = 0`. -/
@[sa_reference "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a"]
def T : Prop :=
  ∀ (φ₄ : U4ℝ → ℝ → U4ℝ) (φ₃ : U3ℝ → ℝ → U3ℝ), IsFlow F4Kℝ φ₄ → IsFlow F3Kℝ φ₃ →
    HasDerivAt (trajectoryGap MℝLinCLM φ₄ φ₃ pt13) (fun _ => (2 : ℝ)) 0 ∧
    HasDerivAt (fun t => MℝLinCLM (φ₄ pt13 t) - φ₃ (MℝLinCLM pt13) t) (fun _ => (2 : ℝ)) 0

/-- S1: through the vocabulary `trajectoryGap`. -/
@[sa_shadow "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a" 1]
def S1 : Prop :=
  ∀ (φ₄ : U4ℝ → ℝ → U4ℝ) (φ₃ : U3ℝ → ℝ → U3ℝ), IsFlow F4Kℝ φ₄ → IsFlow F3Kℝ φ₃ →
    HasDerivAt (trajectoryGap MℝLinCLM φ₄ φ₃ pt13) (fun _ => (2 : ℝ)) 0

/-- S2: through the explicit gap `M(φ₄ u₁ t) − φ₃(M u₁) t`. -/
@[sa_shadow "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a" 2]
def S2 : Prop :=
  ∀ (φ₄ : U4ℝ → ℝ → U4ℝ) (φ₃ : U3ℝ → ℝ → U3ℝ), IsFlow F4Kℝ φ₄ → IsFlow F3Kℝ φ₃ →
    HasDerivAt (fun t => MℝLinCLM (φ₄ pt13 t) - φ₃ (MℝLinCLM pt13) t) (fun _ => (2 : ℝ)) 0

@[sa_ref_forward "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a" 1]
theorem ref_fwd1 : T → S1 := fun t φ₄ φ₃ h4 h3 => (t φ₄ φ₃ h4 h3).1

@[sa_ref_forward "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a" 2]
theorem ref_fwd2 : T → S2 := fun t φ₄ φ₃ h4 h3 => (t φ₄ φ₃ h4 h3).2

@[sa_complete "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.a"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun φ₄ φ₃ h4 h3 => ⟨s1 φ₄ φ₃ h4 h3, s2 φ₄ φ₃ h4 h3⟩

end Alignment.Shadows.MarginalisationDynamicalGap.TrajectoryGapRateTwoAtWitness_a

/-! ## `MarginalisationDynamicalGap.f3RealIsKirkwoodForm` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.F3RealIsKirkwoodForm

/-! Blind text: "`F3Kℝ` is nonlinear (has Kirkwood form): witnessed by `u = v = (c ↦ 1)`, where
`F3Kℝ(u + v)(c) = 1 ≠ 1/2 = F3Kℝ(u)(c) + F3Kℝ(v)(c)`."

-- AMBIGUITY: "nonlinear" is read as failure of additivity, since that is what the witness
-- exhibits: ∃ u v, F3Kℝ (u + v) ≠ F3Kℝ u + F3Kℝ v (S2). "has Kirkwood form" is the vocabulary
-- marker `(ClosureFamily.mk F3Kℝ).IsKirkwoodForm` (S1). The two witness values are S3 and S4.
-- Together they give the witnessed inequality, since 1 ≠ 1/2.
-/

open Alignment.Shadows.MarginalisationDynamicalGap

/-- Intended statement. -/
@[sa_reference "MarginalisationDynamicalGap.f3RealIsKirkwoodForm"]
def T : Prop :=
  (ClosureFamily.mk F3Kℝ).IsKirkwoodForm ∧
    (∃ x y : U3ℝ, F3Kℝ (x + y) ≠ F3Kℝ x + F3Kℝ y) ∧
    F3Kℝ (oneC + oneC) Idx3.c = 1 ∧
    F3Kℝ oneC Idx3.c + F3Kℝ oneC Idx3.c = 1 / 2

/-- S1: `F3Kℝ` has Kirkwood form. -/
@[sa_shadow "MarginalisationDynamicalGap.f3RealIsKirkwoodForm" 1]
def S1 : Prop := (ClosureFamily.mk F3Kℝ).IsKirkwoodForm

/-- S2: `F3Kℝ` is nonlinear (not additive). -/
@[sa_shadow "MarginalisationDynamicalGap.f3RealIsKirkwoodForm" 2]
def S2 : Prop := ∃ x y : U3ℝ, F3Kℝ (x + y) ≠ F3Kℝ x + F3Kℝ y

/-- S3: `F3Kℝ(u + v)(c) = 1` at `u = v = (c ↦ 1)`. -/
@[sa_shadow "MarginalisationDynamicalGap.f3RealIsKirkwoodForm" 3]
def S3 : Prop := F3Kℝ (oneC + oneC) Idx3.c = 1

/-- S4: `F3Kℝ(u)(c) + F3Kℝ(v)(c) = 1/2` at `u = v = (c ↦ 1)`. -/
@[sa_shadow "MarginalisationDynamicalGap.f3RealIsKirkwoodForm" 4]
def S4 : Prop := F3Kℝ oneC Idx3.c + F3Kℝ oneC Idx3.c = 1 / 2

@[sa_ref_forward "MarginalisationDynamicalGap.f3RealIsKirkwoodForm" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MarginalisationDynamicalGap.f3RealIsKirkwoodForm" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MarginalisationDynamicalGap.f3RealIsKirkwoodForm" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1

@[sa_ref_forward "MarginalisationDynamicalGap.f3RealIsKirkwoodForm" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2

@[sa_complete "MarginalisationDynamicalGap.f3RealIsKirkwoodForm"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.MarginalisationDynamicalGap.F3RealIsKirkwoodForm

/-! ## `MarginalisationDynamicalGap.refinementFailureExists.a` -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.RefinementFailureExists_a

/-! Blind text: "**Theorem T6 (Refinement-failure existence).** There exist Kirkwood-form closures
`F4_kirk` (order 4) and `F3_kirk` (order 3), an "exact" order-3 RHS `F3_exact`, and an initial
condition `u₀` such that: * the marginalised m=4 chain is **exact at first order**:
`M(F4_kirk u₀) = F3_exact(M u₀)` (algebraic gap = 0); * the m=3 Kirkwood chain **deviates from
exact**: `F3_kirk(M u₀) ≠ F3_exact(M u₀)`."

-- VOCAB-GAP: "exact" has no DataTypes notion. As in the text ("an 'exact' order-3 RHS"),
-- F3_exact is only existentially quantified.
-- "Kirkwood-form closure" is `(ClosureFamily.mk F).IsKirkwoodForm`, and M is `MℝLinCLM` (the
-- order-4 space is `U4ℝ`, the order-3 space `U3ℝ`). "(algebraic gap = 0)" is taken as a gloss of
-- the displayed equation, which is the requirement. The four conditions share the existential
-- witnesses, so they cannot be split into independent shadows.
-/

/-- Intended statement (T6). -/
@[sa_reference "MarginalisationDynamicalGap.refinementFailureExists.a"]
def T : Prop :=
  ∃ (F4k : U4ℝ → U4ℝ) (F3k : U3ℝ → U3ℝ) (F3ex : U3ℝ → U3ℝ) (u₀ : U4ℝ),
    (ClosureFamily.mk F4k).IsKirkwoodForm ∧ (ClosureFamily.mk F3k).IsKirkwoodForm ∧
    MℝLinCLM (F4k u₀) = F3ex (MℝLinCLM u₀) ∧ F3k (MℝLinCLM u₀) ≠ F3ex (MℝLinCLM u₀)

/-- S1: the whole existential statement. -/
@[sa_shadow "MarginalisationDynamicalGap.refinementFailureExists.a" 1]
def S1 : Prop :=
  ∃ (F4k : U4ℝ → U4ℝ) (F3k : U3ℝ → U3ℝ) (F3ex : U3ℝ → U3ℝ) (u₀ : U4ℝ),
    (ClosureFamily.mk F4k).IsKirkwoodForm ∧ (ClosureFamily.mk F3k).IsKirkwoodForm ∧
    MℝLinCLM (F4k u₀) = F3ex (MℝLinCLM u₀) ∧ F3k (MℝLinCLM u₀) ≠ F3ex (MℝLinCLM u₀)

@[sa_ref_forward "MarginalisationDynamicalGap.refinementFailureExists.a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MarginalisationDynamicalGap.refinementFailureExists.a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MarginalisationDynamicalGap.RefinementFailureExists_a

noncomputable section

/-! ## Shared notions for the re-authored MarginalisationDynamicalGap blocks (blind)

Not registered; inlined by the audit. A *local solution* of `F` through `v` (the texts'
`IsLocalSolution`, which is not in the DataTypes) is written in primitive terms: `ψ 0 = v` and
`ψ` has derivative `F (ψ t)` at every `t` with `|t| < δ`, for some `δ > 0`. `F3exact` is the text's
fitted order-3 right-hand side, the constant 6; `C3match` is the text's closure `c ↦ 3c²/8`. -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.Shared2

universe u

/-- `ψ` is a local solution of `F` through `v`. -/
def LocalSol {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → V) (v : V)
    (ψ : ℝ → V) : Prop :=
  ψ 0 = v ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → HasDerivAt ψ (F (ψ t)) t

/-- The constant order-3 vector with value `r`. -/
def cst (r : ℝ) : U3ℝ := fun _ => r
/-- The fitted order-3 right-hand side `F3_exact`, the constant 6. -/
def F3exact : U3ℝ → U3ℝ := fun _ => cst 6
/-- The order-3 closure `c ↦ 3 v(c)²/8`. -/
def C3match : U3ℝ → U3ℝ := fun v => cst (3 * v Idx3.c ^ 2 / 8)

end Alignment.Shadows.MarginalisationDynamicalGap.Shared2

/-! ## `MarginalisationDynamicalGap.header.T6.a` (re-authored blind)

Text: "T6 exhibits an existence result at one state: an order-3 right-hand side `F3_exact` (the
constant 6, fitted to `M(F4Kℝ u₁)`) that agrees with the marginalised order-4 surrogate at `u₁`," -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.header_T6_a

open Alignment.Shadows.MarginalisationDynamicalGap.Shared2

@[sa_reference "MarginalisationDynamicalGap.header.T6.a"]
def T : Prop := MℝLinCLM (F4Kℝ u₁) = F3exact (MℝLinCLM u₁)

/-- S1: the constant field 6 agrees with `M ∘ F4Kℝ` at `u₁`. -/
@[sa_shadow "MarginalisationDynamicalGap.header.T6.a" 1]
def S1 : Prop := MℝLinCLM (F4Kℝ u₁) = F3exact (MℝLinCLM u₁)

@[sa_ref_forward "MarginalisationDynamicalGap.header.T6.a" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t
@[sa_complete "MarginalisationDynamicalGap.header.T6.a"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MarginalisationDynamicalGap.header_T6_a

/-! ## `MarginalisationDynamicalGap.header.T6.b` (blind)

Text: "and the Kirkwood surrogate F3Kℝ, which does not. Other non-additive order-3 closures do
match at that state: `c ↦ 3c²/8` gives 6 (`kirkwoodForm_matches_at_witness`)."

"Non-additive" = `IsKirkwoodForm` (the vocabulary's marker). -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.header_T6_b

open Alignment.Shadows.MarginalisationDynamicalGap.Shared2

@[sa_reference "MarginalisationDynamicalGap.header.T6.b"]
def T : Prop :=
  MℝLinCLM (F4Kℝ u₁) ≠ F3Kℝ (MℝLinCLM u₁) ∧ (ClosureFamily.mk C3match).IsKirkwoodForm ∧
    MℝLinCLM (F4Kℝ u₁) = C3match (MℝLinCLM u₁) ∧ C3match (MℝLinCLM u₁) = cst 6

/-- S1: `F3Kℝ` does not agree with `M ∘ F4Kℝ` at `u₁`. -/
@[sa_shadow "MarginalisationDynamicalGap.header.T6.b" 1]
def S1 : Prop := MℝLinCLM (F4Kℝ u₁) ≠ F3Kℝ (MℝLinCLM u₁)
/-- S2: `c ↦ 3c²/8` is non-additive. -/
@[sa_shadow "MarginalisationDynamicalGap.header.T6.b" 2]
def S2 : Prop := (ClosureFamily.mk C3match).IsKirkwoodForm
/-- S3: `c ↦ 3c²/8` agrees with `M ∘ F4Kℝ` at `u₁`. -/
@[sa_shadow "MarginalisationDynamicalGap.header.T6.b" 3]
def S3 : Prop := MℝLinCLM (F4Kℝ u₁) = C3match (MℝLinCLM u₁)
/-- S4: `c ↦ 3c²/8` gives 6 at `M u₁`. -/
@[sa_shadow "MarginalisationDynamicalGap.header.T6.b" 4]
def S4 : Prop := C3match (MℝLinCLM u₁) = cst 6

@[sa_ref_forward "MarginalisationDynamicalGap.header.T6.b" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "MarginalisationDynamicalGap.header.T6.b" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "MarginalisationDynamicalGap.header.T6.b" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "MarginalisationDynamicalGap.header.T6.b" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2
@[sa_complete "MarginalisationDynamicalGap.header.T6.b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.MarginalisationDynamicalGap.header_T6_b

/-! ## `MarginalisationDynamicalGap.header.overview` (re-authored blind)

Text: "T2 (algebraic gap = 2 at u₁) + T5 (gap = first-order divergence rate) give, in local form:
*For any local solutions ψ₄ of F4Kℝ from u₁ and ψ₃ of F3Kℝ from M u₁, the trajectory gap
`M(ψ₄ t) − ψ₃ t` has derivative exactly 2 at t = 0 (`witness_localGap_hasDerivAt`), and its norm is
at least t for all small t > 0 (`witness_localGap_ge`).*"

S1: T2, the algebraic gap at `u₁` is 2; S2: T5 in local form for all fields (the gap of local
solutions has derivative `algebraicGap` at 0); S3, S4: the two conclusions at the witness. -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.header_overview

open Alignment.Shadows.MarginalisationDynamicalGap.Shared2

universe u v

@[sa_reference "MarginalisationDynamicalGap.header.overview"]
def T : Prop :=
  algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = cst 2 ∧
  (∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
      [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄)
      (F₃ : V₃ → V₃) (w : V₄) (ψ₄ : ℝ → V₄) (ψ₃ : ℝ → V₃), LocalSol F₄ w ψ₄ →
      LocalSol F₃ (M w) ψ₃ → HasDerivAt (fun t => M (ψ₄ t) - ψ₃ t) (algebraicGap M F₄ F₃ w) 0) ∧
  (∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
      HasDerivAt (fun t => MℝLinCLM (ψ₄ t) - ψ₃ t) (cst 2) 0) ∧
  (∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ ‖MℝLinCLM (ψ₄ t) - ψ₃ t‖)

/-- S1: the algebraic gap at `u₁` is 2. -/
@[sa_shadow "MarginalisationDynamicalGap.header.overview" 1]
def S1 : Prop := algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = cst 2
/-- S2: T5, local form: the algebraic gap is the first-order divergence rate. -/
@[sa_shadow "MarginalisationDynamicalGap.header.overview" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄)
    (F₃ : V₃ → V₃) (w : V₄) (ψ₄ : ℝ → V₄) (ψ₃ : ℝ → V₃), LocalSol F₄ w ψ₄ →
    LocalSol F₃ (M w) ψ₃ → HasDerivAt (fun t => M (ψ₄ t) - ψ₃ t) (algebraicGap M F₄ F₃ w) 0
/-- S3: at the witness the trajectory gap has derivative 2 at t = 0. -/
@[sa_shadow "MarginalisationDynamicalGap.header.overview" 3]
def S3 : Prop :=
  ∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
    HasDerivAt (fun t => MℝLinCLM (ψ₄ t) - ψ₃ t) (cst 2) 0
/-- S4: at the witness the gap's norm is at least t for all small t > 0. -/
@[sa_shadow "MarginalisationDynamicalGap.header.overview" 4]
def S4 : Prop :=
  ∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
    ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ ‖MℝLinCLM (ψ₄ t) - ψ₃ t‖

@[sa_ref_forward "MarginalisationDynamicalGap.header.overview" 1] theorem ref_fwd1 :
    T.{u, v} → S1 := fun t => t.1
@[sa_ref_forward "MarginalisationDynamicalGap.header.overview" 2] theorem ref_fwd2 :
    T.{u, v} → S2.{u, v} := fun t => t.2.1
@[sa_ref_forward "MarginalisationDynamicalGap.header.overview" 3] theorem ref_fwd3 :
    T.{u, v} → S3 := fun t => t.2.2.1
@[sa_ref_forward "MarginalisationDynamicalGap.header.overview" 4] theorem ref_fwd4 :
    T.{u, v} → S4 := fun t => t.2.2.2
@[sa_complete "MarginalisationDynamicalGap.header.overview"]
theorem complete (s1 : S1) (s2 : S2.{u, v}) (s3 : S3) (s4 : S4) : T.{u, v} := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.MarginalisationDynamicalGap.header_overview

/-! ## `MarginalisationDynamicalGap.refinementFailureExists.b` (re-authored blind)

Text: "Together with T5: relative to the fitted `F3_exact`, the marginalised m=4 surrogate has zero
first-order error at `u₁` (by construction), while the m=3 Kirkwood surrogate has first-order error
`|4 − 6| = 2`."

First-order errors at `u₁` relative to `F3_exact` (the rates T5 attaches to them): for the m=4
surrogate, `algebraicGap M F4Kℝ F3_exact u₁` (S1); for the m=3 surrogate, the difference
`F3Kℝ(M u₁) − F3_exact(M u₁)`, with `F3Kℝ(M u₁) = 4` (S2) and norm 2 (S3). -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.refinementFailureExists_b

open Alignment.Shadows.MarginalisationDynamicalGap.Shared2

@[sa_reference "MarginalisationDynamicalGap.refinementFailureExists.b"]
def T : Prop :=
  algebraicGap MℝLinCLM F4Kℝ F3exact u₁ = 0 ∧ F3Kℝ (MℝLinCLM u₁) = cst 4 ∧
    ‖F3Kℝ (MℝLinCLM u₁) - F3exact (MℝLinCLM u₁)‖ = 2

/-- S1: zero first-order error of the marginalised m=4 surrogate. -/
@[sa_shadow "MarginalisationDynamicalGap.refinementFailureExists.b" 1]
def S1 : Prop := algebraicGap MℝLinCLM F4Kℝ F3exact u₁ = 0
/-- S2: the m=3 Kirkwood surrogate gives 4 at `M u₁`. -/
@[sa_shadow "MarginalisationDynamicalGap.refinementFailureExists.b" 2]
def S2 : Prop := F3Kℝ (MℝLinCLM u₁) = cst 4
/-- S3: its first-order error relative to `F3_exact` has size 2. -/
@[sa_shadow "MarginalisationDynamicalGap.refinementFailureExists.b" 3]
def S3 : Prop := ‖F3Kℝ (MℝLinCLM u₁) - F3exact (MℝLinCLM u₁)‖ = 2

@[sa_ref_forward "MarginalisationDynamicalGap.refinementFailureExists.b" 1] theorem ref_fwd1 :
    T → S1 := fun t => t.1
@[sa_ref_forward "MarginalisationDynamicalGap.refinementFailureExists.b" 2] theorem ref_fwd2 :
    T → S2 := fun t => t.2.1
@[sa_ref_forward "MarginalisationDynamicalGap.refinementFailureExists.b" 3] theorem ref_fwd3 :
    T → S3 := fun t => t.2.2
@[sa_complete "MarginalisationDynamicalGap.refinementFailureExists.b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.MarginalisationDynamicalGap.refinementFailureExists_b

/-! ## `MarginalisationDynamicalGap.refinementFailureExists.c` (blind)

Text: "T6 does not explain the empirical B(c) phase reversal. T3b (via T4) shows only that no
order-3 field commutes with `F4Kℝ` under `MℝLin` at every state."

The first sentence is a remark about an experiment. S1: no order-3 field `F₃` satisfies
`MℝLin (F4Kℝ u) = F₃ (MℝLin u)` at every state `u`. -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.refinementFailureExists_c

@[sa_reference "MarginalisationDynamicalGap.refinementFailureExists.c"]
def T : Prop := ∀ F₃ : U3ℝ → U3ℝ, ¬ ∀ w : U4ℝ, MℝLin (F4Kℝ w) = F₃ (MℝLin w)

/-- S1: no order-3 field commutes with `F4Kℝ` under `MℝLin` at every state. -/
@[sa_shadow "MarginalisationDynamicalGap.refinementFailureExists.c" 1]
def S1 : Prop := ∀ F₃ : U3ℝ → U3ℝ, ¬ ∀ w : U4ℝ, MℝLin (F4Kℝ w) = F₃ (MℝLin w)

@[sa_ref_forward "MarginalisationDynamicalGap.refinementFailureExists.c" 1] theorem ref_fwd1 :
    T → S1 := fun t => t
@[sa_complete "MarginalisationDynamicalGap.refinementFailureExists.c"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MarginalisationDynamicalGap.refinementFailureExists_c

/-! ## `MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt` (blind)

Text: "If `f 0 = 0`, `f` has derivative `g` at `0` and `ε ≤ ‖g‖` with `ε > 0`, then
`ε * t / 2 ≤ ‖f t‖` for all small enough `t > 0`."

"For all small enough t > 0" = eventually in `𝓝[>] 0` (DataTypes (d)). -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt

universe u

@[sa_reference "MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt"]
def T : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : ℝ → V) (g : V) (ε : ℝ),
    f 0 = 0 → HasDerivAt f g 0 → 0 < ε → ε ≤ ‖g‖ → ∀ᶠ t in 𝓝[>] (0 : ℝ), ε * t / 2 ≤ ‖f t‖

/-- S1: the lower bound `ε t / 2 ≤ ‖f t‖` for small `t > 0`. -/
@[sa_shadow "MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt" 1]
def S1 : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : ℝ → V) (g : V) (ε : ℝ),
    f 0 = 0 → HasDerivAt f g 0 → 0 < ε → ε ≤ ‖g‖ → ∀ᶠ t in 𝓝[>] (0 : ℝ), ε * t / 2 ≤ ‖f t‖

@[sa_ref_forward "MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt" 1] theorem ref_fwd1 :
    T.{u} → S1.{u} := fun t => t
@[sa_complete "MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt"]
theorem complete (s1 : S1.{u}) : T.{u} := s1

end Alignment.Shadows.MarginalisationDynamicalGap.normGeHalfEpsTOfHasDerivAt

/-! ## `MarginalisationDynamicalGap.localGapHasDerivAtZero` (blind)

Text: "**Theorem T5, local form.** For any local solutions `ψ₄` of `F₄` through `u` and `ψ₃` of `F₃`
through `M u` (`IsLocalSolution`), the gap `t ↦ M (ψ₄ t) − ψ₃ t` has derivative
`algebraicGap M F₄ F₃ u` at `t = 0`." -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.localGapHasDerivAtZero

open Alignment.Shadows.MarginalisationDynamicalGap.Shared2

universe u v

@[sa_reference "MarginalisationDynamicalGap.localGapHasDerivAtZero"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄)
    (F₃ : V₃ → V₃) (w : V₄) (ψ₄ : ℝ → V₄) (ψ₃ : ℝ → V₃), LocalSol F₄ w ψ₄ →
    LocalSol F₃ (M w) ψ₃ → HasDerivAt (fun t => M (ψ₄ t) - ψ₃ t) (algebraicGap M F₄ F₃ w) 0

/-- S1: the local trajectory gap has derivative `algebraicGap` at 0. -/
@[sa_shadow "MarginalisationDynamicalGap.localGapHasDerivAtZero" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄)
    (F₃ : V₃ → V₃) (w : V₄) (ψ₄ : ℝ → V₄) (ψ₃ : ℝ → V₃), LocalSol F₄ w ψ₄ →
    LocalSol F₃ (M w) ψ₃ → HasDerivAt (fun t => M (ψ₄ t) - ψ₃ t) (algebraicGap M F₄ F₃ w) 0

@[sa_ref_forward "MarginalisationDynamicalGap.localGapHasDerivAtZero" 1] theorem ref_fwd1 :
    T.{u, v} → S1.{u, v} := fun t => t
@[sa_complete "MarginalisationDynamicalGap.localGapHasDerivAtZero"]
theorem complete (s1 : S1.{u, v}) : T.{u, v} := s1

end Alignment.Shadows.MarginalisationDynamicalGap.localGapHasDerivAtZero

/-! ## `MarginalisationDynamicalGap.localGapNormGeHalfEpsT` (blind)

Text: "**Theorem T7, local form.** If `‖algebraicGap M F₄ F₃ u‖ ≥ ε > 0`, then for any local
solutions `ψ₄` of `F₄` through `u` and `ψ₃` of `F₃` through `M u`, `‖M (ψ₄ t) − ψ₃ t‖ ≥ ε * t / 2`
for all small enough `t > 0`." -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.localGapNormGeHalfEpsT

open Alignment.Shadows.MarginalisationDynamicalGap.Shared2

universe u v

@[sa_reference "MarginalisationDynamicalGap.localGapNormGeHalfEpsT"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄)
    (F₃ : V₃ → V₃) (w : V₄) (ε : ℝ) (ψ₄ : ℝ → V₄) (ψ₃ : ℝ → V₃), 0 < ε →
    ε ≤ ‖algebraicGap M F₄ F₃ w‖ → LocalSol F₄ w ψ₄ → LocalSol F₃ (M w) ψ₃ →
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ε * t / 2 ≤ ‖M (ψ₄ t) - ψ₃ t‖

/-- S1: the local lower bound `ε t / 2 ≤ ‖M(ψ₄ t) − ψ₃ t‖` for small `t > 0`. -/
@[sa_shadow "MarginalisationDynamicalGap.localGapNormGeHalfEpsT" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄)
    (F₃ : V₃ → V₃) (w : V₄) (ε : ℝ) (ψ₄ : ℝ → V₄) (ψ₃ : ℝ → V₃), 0 < ε →
    ε ≤ ‖algebraicGap M F₄ F₃ w‖ → LocalSol F₄ w ψ₄ → LocalSol F₃ (M w) ψ₃ →
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ε * t / 2 ≤ ‖M (ψ₄ t) - ψ₃ t‖

@[sa_ref_forward "MarginalisationDynamicalGap.localGapNormGeHalfEpsT" 1] theorem ref_fwd1 :
    T.{u, v} → S1.{u, v} := fun t => t
@[sa_complete "MarginalisationDynamicalGap.localGapNormGeHalfEpsT"]
theorem complete (s1 : S1.{u, v}) : T.{u, v} := s1

end Alignment.Shadows.MarginalisationDynamicalGap.localGapNormGeHalfEpsT

/-! ## `MarginalisationDynamicalGap.algebraicGapWitness` (blind)

Text: "The first-order rate at the witness for an arbitrary order-3 field `C₃`:
`algebraicGap MℝLinCLM F4Kℝ C₃ u₁ = 6 − C₃(4)`, where `4 = MℝLinCLM u₁`. So the rate is 2 only when
`C₃(4) = 4`, as for `F3Kℝ`."

"6" and "4" are the constant order-3 vectors. -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.algebraicGapWitness

open Alignment.Shadows.MarginalisationDynamicalGap.Shared2

@[sa_reference "MarginalisationDynamicalGap.algebraicGapWitness"]
def T : Prop :=
  (∀ C₃ : U3ℝ → U3ℝ, algebraicGap MℝLinCLM F4Kℝ C₃ u₁ = cst 6 - C₃ (cst 4)) ∧
  MℝLinCLM u₁ = cst 4 ∧
  (∀ C₃ : U3ℝ → U3ℝ, algebraicGap MℝLinCLM F4Kℝ C₃ u₁ = cst 2 → C₃ (cst 4) = cst 4) ∧
  F3Kℝ (cst 4) = cst 4

/-- S1: the rate at the witness is `6 − C₃(4)`. -/
@[sa_shadow "MarginalisationDynamicalGap.algebraicGapWitness" 1]
def S1 : Prop := ∀ C₃ : U3ℝ → U3ℝ, algebraicGap MℝLinCLM F4Kℝ C₃ u₁ = cst 6 - C₃ (cst 4)
/-- S2: `MℝLinCLM u₁ = 4`. -/
@[sa_shadow "MarginalisationDynamicalGap.algebraicGapWitness" 2]
def S2 : Prop := MℝLinCLM u₁ = cst 4
/-- S3: the rate is 2 only when `C₃(4) = 4`. -/
@[sa_shadow "MarginalisationDynamicalGap.algebraicGapWitness" 3]
def S3 : Prop :=
  ∀ C₃ : U3ℝ → U3ℝ, algebraicGap MℝLinCLM F4Kℝ C₃ u₁ = cst 2 → C₃ (cst 4) = cst 4
/-- S4: `F3Kℝ(4) = 4`. -/
@[sa_shadow "MarginalisationDynamicalGap.algebraicGapWitness" 4]
def S4 : Prop := F3Kℝ (cst 4) = cst 4

@[sa_ref_forward "MarginalisationDynamicalGap.algebraicGapWitness" 1] theorem ref_fwd1 :
    T → S1 := fun t => t.1
@[sa_ref_forward "MarginalisationDynamicalGap.algebraicGapWitness" 2] theorem ref_fwd2 :
    T → S2 := fun t => t.2.1
@[sa_ref_forward "MarginalisationDynamicalGap.algebraicGapWitness" 3] theorem ref_fwd3 :
    T → S3 := fun t => t.2.2.1
@[sa_ref_forward "MarginalisationDynamicalGap.algebraicGapWitness" 4] theorem ref_fwd4 :
    T → S4 := fun t => t.2.2.2
@[sa_complete "MarginalisationDynamicalGap.algebraicGapWitness"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.MarginalisationDynamicalGap.algebraicGapWitness

/-! ## `MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness` (blind)

Text: "A non-additive order-3 closure that matches the marginalised order-4 surrogate at the
witness: `C₃ v = (c ↦ 3 v(c)² / 8)` is non-additive (`IsKirkwoodForm`) and `M(F4Kℝ u₁) = C₃(M u₁)`,
since `3·4²/8 = 6`. So "no Kirkwood-form order-3 closure matches at `u₁`" is false."

M is `MℝLinCLM`. The arithmetic `3·4²/8 = 6` is a closed fact and not a separate shadow. -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness

open Alignment.Shadows.MarginalisationDynamicalGap.Shared2

@[sa_reference "MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness"]
def T : Prop :=
  (ClosureFamily.mk C3match).IsKirkwoodForm ∧ MℝLinCLM (F4Kℝ u₁) = C3match (MℝLinCLM u₁) ∧
    ∃ C : ClosureFamily U3ℝ, C.IsKirkwoodForm ∧ MℝLinCLM (F4Kℝ u₁) = C.C (MℝLinCLM u₁)

/-- S1: `c ↦ 3c²/8` is Kirkwood-form. -/
@[sa_shadow "MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness" 1]
def S1 : Prop := (ClosureFamily.mk C3match).IsKirkwoodForm
/-- S2: it matches `M ∘ F4Kℝ` at `u₁`. -/
@[sa_shadow "MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness" 2]
def S2 : Prop := MℝLinCLM (F4Kℝ u₁) = C3match (MℝLinCLM u₁)
/-- S3: some Kirkwood-form order-3 closure matches at `u₁`. -/
@[sa_shadow "MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness" 3]
def S3 : Prop :=
  ∃ C : ClosureFamily U3ℝ, C.IsKirkwoodForm ∧ MℝLinCLM (F4Kℝ u₁) = C.C (MℝLinCLM u₁)

@[sa_ref_forward "MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness" 1] theorem ref_fwd1 :
    T → S1 := fun t => t.1
@[sa_ref_forward "MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness" 2] theorem ref_fwd2 :
    T → S2 := fun t => t.2.1
@[sa_ref_forward "MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness" 3] theorem ref_fwd3 :
    T → S3 := fun t => t.2.2
@[sa_complete "MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.MarginalisationDynamicalGap.kirkwoodFormMatchesAtWitness

/-! ## `MarginalisationDynamicalGap.witnessLocalSolutionsExist` (blind)

Text: "**Local solutions exist at the witness.** `t ↦ (exp (3 (eᵗ − 1)), 3 eᵗ)` solves `F4Kℝ`
(`a' = a b`, `b' = b`) from `u₁ = (1, 3)` for every `t`, and `t ↦ (c ↦ 4 / (1 − t))` solves `F3Kℝ`
(`v' = v²/4`) from `MℝLinCLM u₁ = 4` on `(-1, 1)`."

"Solves from u₁ for every t" = `IsSolution F4Kℝ u₁` (S1); the order-3 curve starts at `M u₁` (S2)
and solves `F3Kℝ` on `(−1, 1)` (S3). The parenthesised equations describe the fields. -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.witnessLocalSolutionsExist

open Alignment.Shadows.MarginalisationDynamicalGap.Shared2

/-- The order-4 curve `t ↦ (exp (3 (eᵗ − 1)), 3 eᵗ)`. -/
def psi4w (t : ℝ) : U4ℝ := fun i =>
  match i with
  | Idx4.a => Real.exp (3 * (Real.exp t - 1))
  | Idx4.b => 3 * Real.exp t
/-- The order-3 curve `t ↦ (c ↦ 4/(1 − t))`. -/
def psi3w (t : ℝ) : U3ℝ := cst (4 / (1 - t))

@[sa_reference "MarginalisationDynamicalGap.witnessLocalSolutionsExist"]
def T : Prop :=
  IsSolution F4Kℝ u₁ psi4w ∧ psi3w 0 = MℝLinCLM u₁ ∧
    ∀ t : ℝ, -1 < t → t < 1 → HasDerivAt psi3w (F3Kℝ (psi3w t)) t

/-- S1: the order-4 curve solves `F4Kℝ` from `u₁` for every t. -/
@[sa_shadow "MarginalisationDynamicalGap.witnessLocalSolutionsExist" 1]
def S1 : Prop := IsSolution F4Kℝ u₁ psi4w
/-- S2: the order-3 curve starts at `MℝLinCLM u₁`. -/
@[sa_shadow "MarginalisationDynamicalGap.witnessLocalSolutionsExist" 2]
def S2 : Prop := psi3w 0 = MℝLinCLM u₁
/-- S3: the order-3 curve solves `F3Kℝ` on (−1, 1). -/
@[sa_shadow "MarginalisationDynamicalGap.witnessLocalSolutionsExist" 3]
def S3 : Prop := ∀ t : ℝ, -1 < t → t < 1 → HasDerivAt psi3w (F3Kℝ (psi3w t)) t

@[sa_ref_forward "MarginalisationDynamicalGap.witnessLocalSolutionsExist" 1] theorem ref_fwd1 :
    T → S1 := fun t => t.1
@[sa_ref_forward "MarginalisationDynamicalGap.witnessLocalSolutionsExist" 2] theorem ref_fwd2 :
    T → S2 := fun t => t.2.1
@[sa_ref_forward "MarginalisationDynamicalGap.witnessLocalSolutionsExist" 3] theorem ref_fwd3 :
    T → S3 := fun t => t.2.2
@[sa_complete "MarginalisationDynamicalGap.witnessLocalSolutionsExist"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.MarginalisationDynamicalGap.witnessLocalSolutionsExist

/-! ## `MarginalisationDynamicalGap.witnessLocalGapHasDerivAt` (blind)

Text: "**Theorem T5 Corollary, local form.** For any local solutions `ψ₄` of `F4Kℝ` through
`u₁ = (1, 3)` and `ψ₃` of `F3Kℝ` through `MℝLinCLM u₁`, the gap `t ↦ M(ψ₄ t) − ψ₃ t` has derivative
`2` (in every coordinate) at `t = 0`." -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.witnessLocalGapHasDerivAt

open Alignment.Shadows.MarginalisationDynamicalGap.Shared2

@[sa_reference "MarginalisationDynamicalGap.witnessLocalGapHasDerivAt"]
def T : Prop :=
  ∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
    HasDerivAt (fun t => MℝLinCLM (ψ₄ t) - ψ₃ t) (cst 2) 0

/-- S1: the witness gap has derivative 2 at t = 0. -/
@[sa_shadow "MarginalisationDynamicalGap.witnessLocalGapHasDerivAt" 1]
def S1 : Prop :=
  ∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
    HasDerivAt (fun t => MℝLinCLM (ψ₄ t) - ψ₃ t) (cst 2) 0

@[sa_ref_forward "MarginalisationDynamicalGap.witnessLocalGapHasDerivAt" 1] theorem ref_fwd1 :
    T → S1 := fun t => t
@[sa_complete "MarginalisationDynamicalGap.witnessLocalGapHasDerivAt"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MarginalisationDynamicalGap.witnessLocalGapHasDerivAt

/-! ## `MarginalisationDynamicalGap.witnessLocalGapGe` (blind)

Text: "**Theorem T7 Corollary, local form.** For any local solutions `ψ₄` of `F4Kℝ` through `u₁` and
`ψ₃` of `F3Kℝ` through `MℝLinCLM u₁`, there is `T > 0` with `t ≤ ‖M(ψ₄ t) − ψ₃ t‖` for all
`0 < t ≤ T`. In particular the marginalised order-4 trajectory and the order-3 trajectory differ at
every such `t`." -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.witnessLocalGapGe

open Alignment.Shadows.MarginalisationDynamicalGap.Shared2

@[sa_reference "MarginalisationDynamicalGap.witnessLocalGapGe"]
def T : Prop :=
  (∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
      ∃ τ : ℝ, 0 < τ ∧ ∀ t : ℝ, 0 < t → t ≤ τ → t ≤ ‖MℝLinCLM (ψ₄ t) - ψ₃ t‖) ∧
  (∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
      ∃ τ : ℝ, 0 < τ ∧ ∀ t : ℝ, 0 < t → t ≤ τ → MℝLinCLM (ψ₄ t) ≠ ψ₃ t)

/-- S1: `t ≤ ‖M(ψ₄ t) − ψ₃ t‖` on some `(0, T]`. -/
@[sa_shadow "MarginalisationDynamicalGap.witnessLocalGapGe" 1]
def S1 : Prop :=
  ∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
    ∃ τ : ℝ, 0 < τ ∧ ∀ t : ℝ, 0 < t → t ≤ τ → t ≤ ‖MℝLinCLM (ψ₄ t) - ψ₃ t‖
/-- S2: the two trajectories differ on some `(0, T]`. -/
@[sa_shadow "MarginalisationDynamicalGap.witnessLocalGapGe" 2]
def S2 : Prop :=
  ∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
    ∃ τ : ℝ, 0 < τ ∧ ∀ t : ℝ, 0 < t → t ≤ τ → MℝLinCLM (ψ₄ t) ≠ ψ₃ t

@[sa_ref_forward "MarginalisationDynamicalGap.witnessLocalGapGe" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "MarginalisationDynamicalGap.witnessLocalGapGe" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "MarginalisationDynamicalGap.witnessLocalGapGe"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MarginalisationDynamicalGap.witnessLocalGapGe

/-! ## `MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b` (blind)

Text: "**Vacuity.** The hypothesis `IsFlow F3Kℝ φ₃` cannot be satisfied: `F3Kℝ` has no global flow
(`no_flow_F3Kℝ`; from `v(c) = 4` the solution `4/(1 − t)` blows up at `t = 1`)."

S1: no flow of `F3Kℝ`. S2: from 4, every solution of `w' = w²/4` on `t < 1` is `4/(1 − t)`
(the coordinate equation of `F3Kℝ`); S3: `4/(1 − t)` blows up as `t → 1⁻`. -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness_b

@[sa_reference "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b"]
def T : Prop :=
  (∀ φ₃ : U3ℝ → ℝ → U3ℝ, ¬ IsFlow F3Kℝ φ₃) ∧
  (∀ w : ℝ → ℝ, w 0 = 4 → (∀ t : ℝ, t < 1 → HasDerivAt w (w t ^ 2 / 4) t) →
      ∀ t : ℝ, t < 1 → w t = 4 / (1 - t)) ∧
  Tendsto (fun t : ℝ => 4 / (1 - t)) (𝓝[<] 1) atTop

/-- S1: `F3Kℝ` has no global flow. -/
@[sa_shadow "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b" 1]
def S1 : Prop := ∀ φ₃ : U3ℝ → ℝ → U3ℝ, ¬ IsFlow F3Kℝ φ₃
/-- S2: the solution from 4 is `4/(1 − t)` before t = 1. -/
@[sa_shadow "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b" 2]
def S2 : Prop :=
  ∀ w : ℝ → ℝ, w 0 = 4 → (∀ t : ℝ, t < 1 → HasDerivAt w (w t ^ 2 / 4) t) →
    ∀ t : ℝ, t < 1 → w t = 4 / (1 - t)
/-- S3: `4/(1 − t)` blows up at t = 1. -/
@[sa_shadow "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b" 3]
def S3 : Prop := Tendsto (fun t : ℝ => 4 / (1 - t)) (𝓝[<] 1) atTop

@[sa_ref_forward "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness.b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.MarginalisationDynamicalGap.trajectoryGapRateTwoAtWitness_b

/-! ## `MarginalisationDynamicalGap.noGlobalSolutionSqDivFour` (blind)

Text: "There is no real function `w` with `w 0 = 4` and `HasDerivAt w (w t ^ 2 / 4) t` for every
`t : ℝ`: the solution of this initial-value problem, `4/(1 − t)`, blows up at `t = 1`." -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.noGlobalSolutionSqDivFour

@[sa_reference "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour"]
def T : Prop :=
  (¬ ∃ w : ℝ → ℝ, w 0 = 4 ∧ ∀ t : ℝ, HasDerivAt w (w t ^ 2 / 4) t) ∧
  (∀ t : ℝ, t < 1 → HasDerivAt (fun s : ℝ => 4 / (1 - s)) ((4 / (1 - t)) ^ 2 / 4) t) ∧
  (∀ w : ℝ → ℝ, w 0 = 4 → (∀ t : ℝ, t < 1 → HasDerivAt w (w t ^ 2 / 4) t) →
      ∀ t : ℝ, t < 1 → w t = 4 / (1 - t)) ∧
  Tendsto (fun t : ℝ => 4 / (1 - t)) (𝓝[<] 1) atTop

/-- S1: no global solution of `w' = w²/4`, `w 0 = 4`. -/
@[sa_shadow "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour" 1]
def S1 : Prop := ¬ ∃ w : ℝ → ℝ, w 0 = 4 ∧ ∀ t : ℝ, HasDerivAt w (w t ^ 2 / 4) t
/-- S2: `4/(1 − t)` solves the equation before t = 1. -/
@[sa_shadow "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour" 2]
def S2 : Prop :=
  ∀ t : ℝ, t < 1 → HasDerivAt (fun s : ℝ => 4 / (1 - s)) ((4 / (1 - t)) ^ 2 / 4) t
/-- S3: it is the solution of the initial-value problem before t = 1. -/
@[sa_shadow "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour" 3]
def S3 : Prop :=
  ∀ w : ℝ → ℝ, w 0 = 4 → (∀ t : ℝ, t < 1 → HasDerivAt w (w t ^ 2 / 4) t) →
    ∀ t : ℝ, t < 1 → w t = 4 / (1 - t)
/-- S4: it blows up at t = 1. -/
@[sa_shadow "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour" 4]
def S4 : Prop := Tendsto (fun t : ℝ => 4 / (1 - t)) (𝓝[<] 1) atTop

@[sa_ref_forward "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour" 1] theorem ref_fwd1 :
    T → S1 := fun t => t.1
@[sa_ref_forward "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour" 2] theorem ref_fwd2 :
    T → S2 := fun t => t.2.1
@[sa_ref_forward "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour" 3] theorem ref_fwd3 :
    T → S3 := fun t => t.2.2.1
@[sa_ref_forward "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour" 4] theorem ref_fwd4 :
    T → S4 := fun t => t.2.2.2
@[sa_complete "MarginalisationDynamicalGap.noGlobalSolutionSqDivFour"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.MarginalisationDynamicalGap.noGlobalSolutionSqDivFour

/-! ## `MarginalisationDynamicalGap.noFlowF3Real` (blind)

Text: "**No global flow of `F3Kℝ`.** The order-3 Kirkwood witness field `F3Kℝ v = (c ↦ v(c)²/4)` has
no flow in the sense of `IsFlow`, which requires solutions for all `t ∈ ℝ`." -/
namespace Alignment.Shadows.MarginalisationDynamicalGap.noFlowF3Real

@[sa_reference "MarginalisationDynamicalGap.noFlowF3Real"]
def T : Prop :=
  (∀ φ₃ : U3ℝ → ℝ → U3ℝ, ¬ IsFlow F3Kℝ φ₃) ∧ ∀ v : U3ℝ, F3Kℝ v Idx3.c = v Idx3.c ^ 2 / 4

/-- S1: `F3Kℝ` has no flow. -/
@[sa_shadow "MarginalisationDynamicalGap.noFlowF3Real" 1]
def S1 : Prop := ∀ φ₃ : U3ℝ → ℝ → U3ℝ, ¬ IsFlow F3Kℝ φ₃
/-- S2: `F3Kℝ v = (c ↦ v(c)²/4)`. -/
@[sa_shadow "MarginalisationDynamicalGap.noFlowF3Real" 2]
def S2 : Prop := ∀ v : U3ℝ, F3Kℝ v Idx3.c = v Idx3.c ^ 2 / 4

@[sa_ref_forward "MarginalisationDynamicalGap.noFlowF3Real" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "MarginalisationDynamicalGap.noFlowF3Real" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "MarginalisationDynamicalGap.noFlowF3Real"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MarginalisationDynamicalGap.noFlowF3Real

end
