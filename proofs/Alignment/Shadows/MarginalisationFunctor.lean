import Alignment.Registry
import EBCMCategory.MarginalisationFunctor
import EBCMCategory.Obstructions

/-!
# Blind shadow sets: group `MarginalisationFunctor`

Written blind from `Alignment/claims_blind.yaml` (ids `MarginalisationFunctor.*`),
`Alignment/DataTypes/MarginalisationFunctor.md`, `Alignment/README.md` and
`Alignment/Example/ExampleShadows.lean` only.

Common vocabulary (DataTypes §(a)–(c)):
* state spaces: real normed spaces `V₄`, `V₃`; the marginalisation is a continuous linear map
  `M : V₄ →L[ℝ] V₃`;
* vector fields (right-hand sides) `F₄ : V₄ → V₄`, `F₃ : V₃ → V₃`; closed dynamics as
  `ClosedSystem V` (field `F` = the closed RHS);
* `IsFlow F φ` (flow of `F`), `IsSolution F v₀ ψ` (solution curve of `F` through `v₀`),
  `UniqueFlow F` (uniqueness of solutions of `F`);
* *infinitesimal commutation*: `⇑M ∘ F₄ = F₃ ∘ ⇑M`;
* *trajectory commutation*: `∀ w t, M (φ₄ w t) = φ₃ (M w) t` (all `w : V₄`, all `t : ℝ`);
* the Kirkwood witness of `EBCMCategory.Obstructions` (Theorem T2):
  `M_witness : U4 → U3`, `F4_Kirkwood : U4 → U4`, `F3_Kirkwood : U3 → U3`.

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace). Ids of that pass not formalised (remarks on proof status, on which notions the library
defines, or cited results needing models the vocabulary lacks): `header.scaffolding`.
-/

open EBCMCategory.Marginalisation

/-! ## `MarginalisationFunctor.header.closedNeedNotCommute`

Blind text: "For the **closed** dynamics (e.g., Kirkwood at order 4 vs order 3), the diagram
[...] need not commute," -/

namespace Alignment.Shadows.MarginalisationFunctor.header_closedNeedNotCommute

open MarginalisationObstruction

-- AMBIGUITY: "need not commute" read as the negation of a universal ("it is not the case that
-- the diagram always commutes for closed dynamics"), i.e. `¬ ∀ …`, not as a constructive `∃ …`.
-- AMBIGUITY: "the diagram [...]" (the diagram itself is elided from the quoted text) may be the
-- right-hand-side square (`M ∘ F₄ = F₃ ∘ M`) or the trajectory square
-- (`M (φ₄ w t) = φ₃ (M w) t`); both readings are required (S1, S2).
-- AMBIGUITY: "(e.g., Kirkwood at order 4 vs order 3)" read as asserting that the Kirkwood
-- order-4 / order-3 pair is an instance where the diagram does not commute (S3).
-- VOCAB-GAP: DataTypes defines no Kirkwood closure on the motif spaces `V4`/`V3` (which carry no
-- normed structure) and no marginalisation map `V4 → V3`. The general reading is therefore
-- stated over arbitrary real normed spaces (in `Type`) with a continuous linear `M` and closed
-- systems `ClosedSystem V`; the Kirkwood example uses the Obstructions witness surrogate
-- `M_witness`, `F4_Kirkwood`, `F3_Kirkwood` (ℚ-valued, so only the RHS square is expressible).

/-- S1 body: for closed dynamics the RHS square need not commute. -/
def rhsNeedNotCommute : Prop :=
  ¬ ∀ (V₄ V₃ : Type) [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
      [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
      (M : V₄ →L[ℝ] V₃) (C₄ : ClosedSystem V₄) (C₃ : ClosedSystem V₃),
      (⇑M ∘ C₄.F) = (C₃.F ∘ ⇑M)

/-- S2 body: for closed dynamics the trajectory square need not commute. -/
def trajNeedNotCommute : Prop :=
  ¬ ∀ (V₄ V₃ : Type) [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
      [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
      (M : V₄ →L[ℝ] V₃) (C₄ : ClosedSystem V₄) (C₃ : ClosedSystem V₃)
      (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃),
      IsFlow C₄.F φ₄ → IsFlow C₃.F φ₃ → ∀ (w : V₄) (t : ℝ), M (φ₄ w t) = φ₃ (M w) t

/-- S3 body: the Kirkwood order-4 / order-3 pair does not commute. -/
def kirkwoodNotCommute : Prop :=
  ¬ ((M_witness ∘ F4_Kirkwood) = (F3_Kirkwood ∘ M_witness))

/-- Intended statement: for closed dynamics the diagram need not commute (in both readings of
"the diagram"), and Kirkwood order 4 vs order 3 is an instance where it does not. -/
@[sa_reference "MarginalisationFunctor.header.closedNeedNotCommute"]
def T : Prop := rhsNeedNotCommute ∧ trajNeedNotCommute ∧ kirkwoodNotCommute

/-- S1: the RHS square `M ∘ C₄.F = C₃.F ∘ M` does not hold for all closed systems and all
continuous linear `M`. -/
@[sa_shadow "MarginalisationFunctor.header.closedNeedNotCommute" 1]
def S1 : Prop :=
  ¬ ∀ (V₄ V₃ : Type) [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
      [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
      (M : V₄ →L[ℝ] V₃) (C₄ : ClosedSystem V₄) (C₃ : ClosedSystem V₃),
      (⇑M ∘ C₄.F) = (C₃.F ∘ ⇑M)

/-- S2: trajectory commutation does not hold for all closed systems (with flows) and all
continuous linear `M`. -/
@[sa_shadow "MarginalisationFunctor.header.closedNeedNotCommute" 2]
def S2 : Prop :=
  ¬ ∀ (V₄ V₃ : Type) [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
      [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
      (M : V₄ →L[ℝ] V₃) (C₄ : ClosedSystem V₄) (C₃ : ClosedSystem V₃)
      (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃),
      IsFlow C₄.F φ₄ → IsFlow C₃.F φ₃ → ∀ (w : V₄) (t : ℝ), M (φ₄ w t) = φ₃ (M w) t

/-- S3: the Kirkwood closures at order 4 and order 3 do not commute with the marginalisation. -/
@[sa_shadow "MarginalisationFunctor.header.closedNeedNotCommute" 3]
def S3 : Prop := ¬ ((M_witness ∘ F4_Kirkwood) = (F3_Kirkwood ∘ M_witness))

@[sa_ref_forward "MarginalisationFunctor.header.closedNeedNotCommute" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MarginalisationFunctor.header.closedNeedNotCommute" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MarginalisationFunctor.header.closedNeedNotCommute" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2

@[sa_complete "MarginalisationFunctor.header.closedNeedNotCommute"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.MarginalisationFunctor.header_closedNeedNotCommute

/-! ## `MarginalisationFunctor.RM2`

Blind text: "**Result M2 (→).** Infinitesimal commutation `M ∘ F₄ = F₃ ∘ M` and a unique flow for
`F₃` imply trajectory commutation." -/

namespace Alignment.Shadows.MarginalisationFunctor.RM2

universe u v

-- AMBIGUITY: "a unique flow for `F₃`" read as: `φ₃` is a flow of `F₃` (`IsFlow F₃ φ₃`) and
-- solutions of `F₃` are unique (`UniqueFlow F₃`, the DataTypes uniqueness predicate), rather
-- than `∃! φ₃, IsFlow F₃ φ₃`. "Trajectory commutation" needs a flow `φ₄` of `F₄` (standing
-- hypothesis, `IsFlow F₄ φ₄`); no uniqueness for `F₄` is stated, so none is assumed.
-- `M` is the continuous linear marginalisation (DataTypes §(a)).

/-- Intended statement: infinitesimal commutation plus a unique flow of `F₃` imply trajectory
commutation for all `w : V₄` and all `t : ℝ`. -/
@[sa_reference "MarginalisationFunctor.RM2"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → (⇑M ∘ F₄) = (F₃ ∘ ⇑M) → IsFlow F₃ φ₃ → UniqueFlow F₃ →
      ∀ (w : V₄) (t : ℝ), M (φ₄ w t) = φ₃ (M w) t

/-- S1: the whole statement (a single atomic implication). -/
@[sa_shadow "MarginalisationFunctor.RM2" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → (⇑M ∘ F₄) = (F₃ ∘ ⇑M) → IsFlow F₃ φ₃ → UniqueFlow F₃ →
      ∀ (w : V₄) (t : ℝ), M (φ₄ w t) = φ₃ (M w) t

@[sa_ref_forward "MarginalisationFunctor.RM2" 1]
theorem ref_fwd1 : T.{u, v} → S1.{u, v} := fun t => t

@[sa_complete "MarginalisationFunctor.RM2"]
theorem complete (s1 : S1.{u, v}) : T.{u, v} := s1

end Alignment.Shadows.MarginalisationFunctor.RM2

/-! ## `MarginalisationFunctor.RM3`

Blind text: "**Result M3 (←).** Trajectory commutation implies infinitesimal commutation, by
differentiating at `t = 0`." -/

namespace Alignment.Shadows.MarginalisationFunctor.RM3

universe u v

-- Standing hypotheses: `φ₄`, `φ₃` are flows of `F₄`, `F₃` (needed to speak of trajectories);
-- `M` is continuous linear. No uniqueness hypothesis is stated, so none is assumed.
-- "by differentiating at `t = 0`" names the proof method and is not a checkable requirement.

/-- Intended statement: trajectory commutation (all `w`, all `t`) implies infinitesimal
commutation `M ∘ F₄ = F₃ ∘ M`. -/
@[sa_reference "MarginalisationFunctor.RM3"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ →
      (∀ (w : V₄) (t : ℝ), M (φ₄ w t) = φ₃ (M w) t) → (⇑M ∘ F₄) = (F₃ ∘ ⇑M)

/-- S1: the whole statement (a single atomic implication). -/
@[sa_shadow "MarginalisationFunctor.RM3" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ →
      (∀ (w : V₄) (t : ℝ), M (φ₄ w t) = φ₃ (M w) t) → (⇑M ∘ F₄) = (F₃ ∘ ⇑M)

@[sa_ref_forward "MarginalisationFunctor.RM3" 1]
theorem ref_fwd1 : T.{u, v} → S1.{u, v} := fun t => t

@[sa_complete "MarginalisationFunctor.RM3"]
theorem complete (s1 : S1.{u, v}) : T.{u, v} := s1

end Alignment.Shadows.MarginalisationFunctor.RM3

/-! ## `MarginalisationFunctor.RM4a`

Blind text: "**Result M4 — Theorem T1 (Equivariance).** The diagram [...] commutes infinitesimally
**iff** it commutes along all trajectories (under the standing flow / uniqueness hypotheses)." -/

namespace Alignment.Shadows.MarginalisationFunctor.RM4a

universe u v

-- AMBIGUITY: "the standing flow / uniqueness hypotheses" read as `IsFlow F₄ φ₄`, `IsFlow F₃ φ₃`
-- and `UniqueFlow F₃` (the uniqueness hypothesis of Result M2); uniqueness for `F₄` is not
-- assumed. Both directions of the iff are stated under all standing hypotheses.
-- "commutes infinitesimally": `M ∘ F₄ = F₃ ∘ M`; "commutes along all trajectories":
-- `M (φ₄ w t) = φ₃ (M w) t` for all `w : V₄`, `t : ℝ`.

/-- Intended statement: under the standing hypotheses, infinitesimal commutation iff trajectory
commutation. -/
@[sa_reference "MarginalisationFunctor.RM4a"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → UniqueFlow F₃ →
      ((⇑M ∘ F₄) = (F₃ ∘ ⇑M) ↔ ∀ (w : V₄) (t : ℝ), M (φ₄ w t) = φ₃ (M w) t)

/-- S1 (→): infinitesimal commutation implies commutation along all trajectories. -/
@[sa_shadow "MarginalisationFunctor.RM4a" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → UniqueFlow F₃ →
      (⇑M ∘ F₄) = (F₃ ∘ ⇑M) → ∀ (w : V₄) (t : ℝ), M (φ₄ w t) = φ₃ (M w) t

/-- S2 (←): commutation along all trajectories implies infinitesimal commutation. -/
@[sa_shadow "MarginalisationFunctor.RM4a" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → UniqueFlow F₃ →
      (∀ (w : V₄) (t : ℝ), M (φ₄ w t) = φ₃ (M w) t) → (⇑M ∘ F₄) = (F₃ ∘ ⇑M)

@[sa_ref_forward "MarginalisationFunctor.RM4a" 1]
theorem ref_fwd1 : T.{u, v} → S1.{u, v} := by
  intro t V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hu hinf
  exact (t M h₄ h₃ hu).mp hinf

@[sa_ref_forward "MarginalisationFunctor.RM4a" 2]
theorem ref_fwd2 : T.{u, v} → S2.{u, v} := by
  intro t V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hu htr
  exact (t M h₄ h₃ hu).mpr htr

@[sa_complete "MarginalisationFunctor.RM4a"]
theorem complete (s1 : S1.{u, v}) (s2 : S2.{u, v}) : T.{u, v} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hu
  exact ⟨s1 M h₄ h₃ hu, s2 M h₄ h₃ hu⟩

end Alignment.Shadows.MarginalisationFunctor.RM4a

/-! ## `MarginalisationFunctor.RM4b`

Blind text: "The intended use is contrapositive: **failure** of trajectory marginalisation
`M · u₄(t) = u₃(t)` is detectable from the algebraic failure of `M ∘ F₄ = F₃ ∘ M`, which is
checked by Theorem T2." -/

namespace Alignment.Shadows.MarginalisationFunctor.RM4b

universe u v

open MarginalisationObstruction

-- "trajectory marginalisation `M · u₄(t) = u₃(t)`" read with `u₄(t) = φ₄ w t` and
-- `u₃(t) = φ₃ (M w) t` (flows `φ₄`, `φ₃` of `F₄`, `F₃`, consistent initial data), for all `w, t`.
-- "failure" is read as the negation `¬ ∀ w t, …`; "detectable from" as implication.
-- AMBIGUITY: the contrapositive is of Theorem T1 "under the standing flow / uniqueness
-- hypotheses", but this sentence itself states no uniqueness hypothesis. Reading A: flows only
-- (S1). Reading B: flows plus `UniqueFlow F₃` (S2). Both readings are required.
-- "which is checked by Theorem T2" read as: the algebraic failure is established for the
-- Kirkwood order-4 / order-3 witness of Theorem T2 (S3).
-- VOCAB-GAP: the Kirkwood witness lives on ℚ-valued `U4`/`U3` (no normed real structure, no
-- flows), so the resulting failure of *trajectory* marginalisation for the Kirkwood pair cannot
-- be stated; only the algebraic failure is shadowed.

/-- Intended statement: algebraic failure implies trajectory failure (readings A and B), and
the algebraic failure holds for the Theorem T2 Kirkwood witness. -/
@[sa_reference "MarginalisationFunctor.RM4b"]
def T : Prop :=
  (∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ →
      ¬ ((⇑M ∘ F₄) = (F₃ ∘ ⇑M)) → ¬ ∀ (w : V₄) (t : ℝ), M (φ₄ w t) = φ₃ (M w) t) ∧
  (∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → UniqueFlow F₃ →
      ¬ ((⇑M ∘ F₄) = (F₃ ∘ ⇑M)) → ¬ ∀ (w : V₄) (t : ℝ), M (φ₄ w t) = φ₃ (M w) t) ∧
  ¬ ((M_witness ∘ F4_Kirkwood) = (F3_Kirkwood ∘ M_witness))

/-- S1 (reading A): for flows, failure of `M ∘ F₄ = F₃ ∘ M` implies failure of trajectory
marginalisation. -/
@[sa_shadow "MarginalisationFunctor.RM4b" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ →
      ¬ ((⇑M ∘ F₄) = (F₃ ∘ ⇑M)) → ¬ ∀ (w : V₄) (t : ℝ), M (φ₄ w t) = φ₃ (M w) t

/-- S2 (reading B): the same under the additional standing hypothesis `UniqueFlow F₃`. -/
@[sa_shadow "MarginalisationFunctor.RM4b" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) {F₄ : V₄ → V₄} {F₃ : V₃ → V₃}
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → UniqueFlow F₃ →
      ¬ ((⇑M ∘ F₄) = (F₃ ∘ ⇑M)) → ¬ ∀ (w : V₄) (t : ℝ), M (φ₄ w t) = φ₃ (M w) t

/-- S3: the algebraic failure checked by Theorem T2: the Kirkwood order-4 / order-3 witness
does not satisfy `M ∘ F₄ = F₃ ∘ M`. -/
@[sa_shadow "MarginalisationFunctor.RM4b" 3]
def S3 : Prop := ¬ ((M_witness ∘ F4_Kirkwood) = (F3_Kirkwood ∘ M_witness))

@[sa_ref_forward "MarginalisationFunctor.RM4b" 1]
theorem ref_fwd1 : T.{u, v} → S1.{u, v} := fun t => t.1

@[sa_ref_forward "MarginalisationFunctor.RM4b" 2]
theorem ref_fwd2 : T.{u, v} → S2.{u, v} := fun t => t.2.1

@[sa_ref_forward "MarginalisationFunctor.RM4b" 3]
theorem ref_fwd3 : T.{u, v} → S3 := fun t => t.2.2

@[sa_complete "MarginalisationFunctor.RM4b"]
theorem complete (s1 : S1.{u, v}) (s2 : S2.{u, v}) (s3 : S3) : T.{u, v} := ⟨s1, s2, s3⟩

end Alignment.Shadows.MarginalisationFunctor.RM4b

noncomputable section

/-! ## `MarginalisationFunctor.RM1` (re-authored blind)

Text: "**Result M1.** Pushing a flow of `F₄` through a continuous linear `M` gives a solution of
`F₃` through `M u` whenever the RHS commute. It is *the* solution only if solutions of `F₃` are
unique."

Vocabulary: `IsFlow`, `IsSolution`, `UniqueFlow`; "the RHS commute" = `M (F₄ w) = F₃ (M w)` for all
`w`. -- AMBIGUITY: "It is *the* solution only if solutions of F₃ are unique" is read as two
requirements: with `UniqueFlow F₃` every solution of `F₃` through `M u` is the pushforward (S2);
without uniqueness another solution through `M u` can exist (S3, an example). -/
namespace Alignment.Shadows.MarginalisationFunctor.RM1

universe u v

@[sa_reference "MarginalisationFunctor.RM1"]
def T : Prop :=
  (∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
      [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄),
      IsFlow F₄ φ₄ → (∀ w, M (F₄ w) = F₃ (M w)) →
        ∀ w, IsSolution F₃ (M w) (fun t => M (φ₄ w t))) ∧
  (∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
      [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄),
      IsFlow F₄ φ₄ → (∀ w, M (F₄ w) = F₃ (M w)) → UniqueFlow F₃ →
        ∀ (w : V₄) (ψ : ℝ → V₃), IsSolution F₃ (M w) ψ → ψ = fun t => M (φ₄ w t)) ∧
  (∃ (V₄ V₃ : Type) (_ : NormedAddCommGroup V₄) (_ : NormedSpace ℝ V₄) (_ : NormedAddCommGroup V₃)
      (_ : NormedSpace ℝ V₃) (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
      (φ₄ : V₄ → ℝ → V₄) (w : V₄) (ψ : ℝ → V₃),
      IsFlow F₄ φ₄ ∧ (∀ x, M (F₄ x) = F₃ (M x)) ∧ IsSolution F₃ (M w) ψ ∧
        ψ ≠ fun t => M (φ₄ w t))

/-- S1: the pushforward of a flow of `F₄` solves `F₃` through `M w` when the RHS commute. -/
@[sa_shadow "MarginalisationFunctor.RM1" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
    [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄),
    IsFlow F₄ φ₄ → (∀ w, M (F₄ w) = F₃ (M w)) → ∀ w, IsSolution F₃ (M w) (fun t => M (φ₄ w t))
/-- S2: with unique solutions of `F₃`, the pushforward is the solution. -/
@[sa_shadow "MarginalisationFunctor.RM1" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
    [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄),
    IsFlow F₄ φ₄ → (∀ w, M (F₄ w) = F₃ (M w)) → UniqueFlow F₃ →
      ∀ (w : V₄) (ψ : ℝ → V₃), IsSolution F₃ (M w) ψ → ψ = fun t => M (φ₄ w t)
/-- S3: without uniqueness, another solution of `F₃` through `M w` can exist. -/
@[sa_shadow "MarginalisationFunctor.RM1" 3]
def S3 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : NormedAddCommGroup V₄) (_ : NormedSpace ℝ V₄) (_ : NormedAddCommGroup V₃)
    (_ : NormedSpace ℝ V₃) (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    (φ₄ : V₄ → ℝ → V₄) (w : V₄) (ψ : ℝ → V₃),
    IsFlow F₄ φ₄ ∧ (∀ x, M (F₄ x) = F₃ (M x)) ∧ IsSolution F₃ (M w) ψ ∧ ψ ≠ fun t => M (φ₄ w t)

@[sa_ref_forward "MarginalisationFunctor.RM1" 1] theorem ref_fwd1 : T.{u, v} → S1.{u, v} :=
  fun t => t.1
@[sa_ref_forward "MarginalisationFunctor.RM1" 2] theorem ref_fwd2 : T.{u, v} → S2.{u, v} :=
  fun t => t.2.1
@[sa_ref_forward "MarginalisationFunctor.RM1" 3] theorem ref_fwd3 : T.{u, v} → S3 :=
  fun t => t.2.2
@[sa_complete "MarginalisationFunctor.RM1"]
theorem complete (s1 : S1.{u, v}) (s2 : S2.{u, v}) (s3 : S3) : T.{u, v} := ⟨s1, s2, s3⟩

end Alignment.Shadows.MarginalisationFunctor.RM1

/-! ## `MarginalisationFunctor.header.T1` (re-authored blind)

Text: "we prove (Theorem T1) the precise dynamical characterisation, for systems with global flows
`φ₄`, `φ₃` and unique solutions of `F₃`: *Trajectory-level marginalisation*
`M ∘ φ₄(·,t) = φ₃(M·, t)` for all `(u, t)` is **equivalent** to *infinitesimal* marginalisation
`M ∘ F₄ = F₃ ∘ M`." -/
namespace Alignment.Shadows.MarginalisationFunctor.header_T1

universe u v

@[sa_reference "MarginalisationFunctor.header.T1"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
    [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄)
    (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → UniqueFlow F₃ →
      ((∀ w t, M (φ₄ w t) = φ₃ (M w) t) ↔ ∀ w, M (F₄ w) = F₃ (M w))

/-- S1: trajectory-level marginalisation implies infinitesimal marginalisation. -/
@[sa_shadow "MarginalisationFunctor.header.T1" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
    [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄)
    (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → UniqueFlow F₃ →
      (∀ w t, M (φ₄ w t) = φ₃ (M w) t) → ∀ w, M (F₄ w) = F₃ (M w)
/-- S2: infinitesimal marginalisation implies trajectory-level marginalisation. -/
@[sa_shadow "MarginalisationFunctor.header.T1" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
    [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄)
    (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → UniqueFlow F₃ →
      (∀ w, M (F₄ w) = F₃ (M w)) → ∀ w t, M (φ₄ w t) = φ₃ (M w) t

@[sa_ref_forward "MarginalisationFunctor.header.T1" 1] theorem ref_fwd1 :
    T.{u, v} → S1.{u, v} := by
  intro t V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h4 h3 hu
  exact (t M F₄ F₃ φ₄ φ₃ h4 h3 hu).1
@[sa_ref_forward "MarginalisationFunctor.header.T1" 2] theorem ref_fwd2 :
    T.{u, v} → S2.{u, v} := by
  intro t V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h4 h3 hu
  exact (t M F₄ F₃ φ₄ φ₃ h4 h3 hu).2
@[sa_complete "MarginalisationFunctor.header.T1"]
theorem complete (s1 : S1.{u, v}) (s2 : S2.{u, v}) : T.{u, v} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h4 h3 hu
  exact ⟨s1 M F₄ F₃ φ₄ φ₃ h4 h3 hu, s2 M F₄ F₃ φ₄ φ₃ h4 h3 hu⟩

end Alignment.Shadows.MarginalisationFunctor.header_T1

/-! ## `MarginalisationFunctor.table.M1` (blind)

Text: "| M1 | pushforward of a flow of `F₄` solves `F₃` if the RHS commute |" -/
namespace Alignment.Shadows.MarginalisationFunctor.table_M1

universe u v

@[sa_reference "MarginalisationFunctor.table.M1"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
    [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄),
    IsFlow F₄ φ₄ → (∀ w, M (F₄ w) = F₃ (M w)) → ∀ w, IsSolution F₃ (M w) (fun t => M (φ₄ w t))

/-- S1: the pushforward of a flow of `F₄` solves `F₃` if the RHS commute. -/
@[sa_shadow "MarginalisationFunctor.table.M1" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
    [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄),
    IsFlow F₄ φ₄ → (∀ w, M (F₄ w) = F₃ (M w)) → ∀ w, IsSolution F₃ (M w) (fun t => M (φ₄ w t))

@[sa_ref_forward "MarginalisationFunctor.table.M1" 1] theorem ref_fwd1 : T.{u, v} → S1.{u, v} :=
  fun t => t
@[sa_complete "MarginalisationFunctor.table.M1"]
theorem complete (s1 : S1.{u, v}) : T.{u, v} := s1

end Alignment.Shadows.MarginalisationFunctor.table_M1

/-! ## `MarginalisationFunctor.rhsCommuteOfLocalTrajCommute` (blind)

Text: "**Result M3, local form.** If local solutions `ψ₄` of `F₄` through `u` and `ψ₃` of `F₃`
through `M u` satisfy `M (ψ₄ t) = ψ₃ t` for all `|t| < δ` (with `δ > 0`), then
`M (F₄ u) = F₃ (M u)`. No global flow and no uniqueness is assumed."

A local solution through `v` on `|t| < δ`: `ψ 0 = v` and `ψ` has derivative `F (ψ t)` at every
`t` with `|t| < δ` (primitive terms; no flow or uniqueness hypothesis). -/
namespace Alignment.Shadows.MarginalisationFunctor.rhsCommuteOfLocalTrajCommute

universe u v

@[sa_reference "MarginalisationFunctor.rhsCommuteOfLocalTrajCommute"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
    [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (u : V₄)
    (ψ₄ : ℝ → V₄) (ψ₃ : ℝ → V₃) (δ : ℝ), 0 < δ → ψ₄ 0 = u → ψ₃ 0 = M u →
    (∀ t, |t| < δ → HasDerivAt ψ₄ (F₄ (ψ₄ t)) t) → (∀ t, |t| < δ → HasDerivAt ψ₃ (F₃ (ψ₃ t)) t) →
    (∀ t, |t| < δ → M (ψ₄ t) = ψ₃ t) → M (F₄ u) = F₃ (M u)

/-- S1: agreement of local solutions near 0 forces the RHS to commute at `u`. -/
@[sa_shadow "MarginalisationFunctor.rhsCommuteOfLocalTrajCommute" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
    [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (u : V₄)
    (ψ₄ : ℝ → V₄) (ψ₃ : ℝ → V₃) (δ : ℝ), 0 < δ → ψ₄ 0 = u → ψ₃ 0 = M u →
    (∀ t, |t| < δ → HasDerivAt ψ₄ (F₄ (ψ₄ t)) t) → (∀ t, |t| < δ → HasDerivAt ψ₃ (F₃ (ψ₃ t)) t) →
    (∀ t, |t| < δ → M (ψ₄ t) = ψ₃ t) → M (F₄ u) = F₃ (M u)

@[sa_ref_forward "MarginalisationFunctor.rhsCommuteOfLocalTrajCommute" 1] theorem ref_fwd1 :
    T.{u, v} → S1.{u, v} := fun t => t
@[sa_complete "MarginalisationFunctor.rhsCommuteOfLocalTrajCommute"]
theorem complete (s1 : S1.{u, v}) : T.{u, v} := s1

end Alignment.Shadows.MarginalisationFunctor.rhsCommuteOfLocalTrajCommute

end
