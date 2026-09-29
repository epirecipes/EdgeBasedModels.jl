import Alignment.Registry
import EBCMCategory.MarginalisationCharacterization
import EBCMCategory.MarginalisationDynamicalGap   -- F3Kℝ, MℝLinCLM (DataTypes/MarginalisationDynamicalGap.md)

/-!
# Blind shadow sets: group `MarginalisationCharacterization`

Written blind: the author read only the claim entries in `Alignment/claims_blind.yaml`,
`Alignment/DataTypes/MarginalisationCharacterization.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean` and `SA-PASS_SKILL.md`, and used `#check` only on the
data types and operations listed in the DataTypes file.

Conventions used throughout (from the DataTypes file):

* "closure diagram commutes" / "marginalisation-equivariant" is `Equivariant M F₄ F₃`;
* a "Kirkwood-form" (nontrivial multiplicative-rational) closure is a `ClosureFamily`
  satisfying `IsKirkwoodForm`; a "linear closure" is one satisfying `IsLinear`;
* the "KKR pairwise-exactness criterion" is `closureKappa ψ = 1`.

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace). Ids of that pass not formalised (remarks on proof status, on which notions the library
defines, or cited results needing models the vocabulary lacks): `header.kkrCharacterization`,
`header.kkrNecessary`, `kkrNecessaryNotSufficient.necessary`.
-/

-- VOCAB-GAP: the DataTypes do not say how a closure family generates the closed RHS. The closed
-- order-4 RHS of a closure family `C₄` is taken to be `C₄.C` (a `ClosureFamily` is just a map
-- `C : V → V`), consistent with "closure diagram commutes" = `Equivariant M F₄ F₃`.

open EBCMCategory.Marginalisation
open EBCMCategory.MarginalisationCharacterization
open MarginalisationObstruction

universe u v

/-! ## `MarginalisationCharacterization.header.T2witness`

Text: "the witness there shows the diagram fails for one specific Kirkwood-style closure," -/

namespace Alignment.Shadows.MarginalisationCharacterization.header_T2witness

-- AMBIGUITY: "the diagram fails" is read as the negation of commutation of the T2 witness
-- diagram of `Obstructions` (M_witness, F4_Kirkwood, F3_Kirkwood):
-- ¬ ∀ u, M(F₄ u) = F₃(M u). "one specific Kirkwood-style closure" fixes both closed RHSs
-- (F4_Kirkwood, F3_Kirkwood), so the stronger reading "no order-3 field makes it commute" is not
-- required. The presupposition that the closure is "Kirkwood-style" is descriptive and is not a
-- separate requirement (the T2 data are not a `ClosureFamily` in the DataTypes).

/-- Intended statement: the T2 witness diagram `M ∘ F₄ = F₃ ∘ M` does not commute. -/
@[sa_reference "MarginalisationCharacterization.header.T2witness"]
def T : Prop := ¬ ∀ w : U4, M_witness (F4_Kirkwood w) = F3_Kirkwood (M_witness w)

/-- S1: the witness diagram fails (not every point commutes). -/
@[sa_shadow "MarginalisationCharacterization.header.T2witness" 1]
def S1 : Prop := ¬ ∀ w : U4, M_witness (F4_Kirkwood w) = F3_Kirkwood (M_witness w)

@[sa_ref_forward "MarginalisationCharacterization.header.T2witness" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MarginalisationCharacterization.header.T2witness"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MarginalisationCharacterization.header_T2witness

/-! ## `MarginalisationCharacterization.linearClosureEquivariant.a`

Text: "A linear closure paired with an `M`-compatible linear `L₃` at order 3 yields an equivariant
closed RHS" -/

namespace Alignment.Shadows.MarginalisationCharacterization.linearClosureEquivariant_a

-- AMBIGUITY: "`M`-compatible" is read as intertwining in primitive terms:
-- ∀ v, M (C₄.C v) = L₃ (M v). "linear `L₃`" is a linear map `V₃ →ₗ[ℝ] V₃`. "yields an
-- equivariant closed RHS" is `Equivariant M C₄.C L₃` (the order-3 closed RHS is `L₃`).

/-- Intended statement: a linear closure `C₄` with an `M`-compatible linear `L₃` gives
`Equivariant M C₄.C L₃`. -/
@[sa_reference "MarginalisationCharacterization.linearClosureEquivariant.a"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [Module ℝ V₄] [AddCommGroup V₃] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄) (L₃ : V₃ →ₗ[ℝ] V₃),
    C₄.IsLinear → (∀ w : V₄, M (C₄.C w) = L₃ (M w)) → Equivariant M C₄.C L₃

/-- S1: the whole implication (one atomic requirement). -/
@[sa_shadow "MarginalisationCharacterization.linearClosureEquivariant.a" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [Module ℝ V₄] [AddCommGroup V₃] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄) (L₃ : V₃ →ₗ[ℝ] V₃),
    C₄.IsLinear → (∀ w : V₄, M (C₄.C w) = L₃ (M w)) → Equivariant M C₄.C L₃

@[sa_ref_forward "MarginalisationCharacterization.linearClosureEquivariant.a" 1]
theorem ref_fwd1 : T.{u, v} → S1.{u, v} := fun t => t

@[sa_complete "MarginalisationCharacterization.linearClosureEquivariant.a"]
theorem complete (s1 : S1.{u, v}) : T.{u, v} := s1

end Alignment.Shadows.MarginalisationCharacterization.linearClosureEquivariant_a

/-! ## `MarginalisationCharacterization.c4RealIsKirkwoodForm`

Text: "The Kirkwood-form predicate holds for `C4ℝ`: the bilinear `a·b` component is non-additive.
Witnessed by `u = (1,0)`, `v = (0,1)`: `F₄(u+v) = (1,1)` while `F₄(u) + F₄(v) = (0,1)`." -/

namespace Alignment.Shadows.MarginalisationCharacterization.c4RealIsKirkwoodForm

/-- The point `(x, y)` of `U4ℝ = Idx4 → ℝ`, i.e. `a ↦ x`, `b ↦ y` (the DataTypes write
`u₁ = (a ↦ 1, b ↦ 3)` in the same order). -/
def pt (x y : ℝ) : U4ℝ := fun i =>
  match i with
  | Idx4.a => x
  | Idx4.b => y

-- AMBIGUITY: pairs `(x, y)` are read as `(a ↦ x, b ↦ y)`.
-- AMBIGUITY: "the bilinear `a·b` component" is read as: some output component of `C4ℝ.C` equals
-- the product of the `a` and `b` coordinates (S3); "is non-additive" as `C4ℝ.C` failing
-- additivity at some pair of points (S2).
-- AMBIGUITY: the text's `F₄` may denote the map of the closure family `C4ℝ` (S4, S5) or the
-- Kirkwood-closed order-4 RHS `F4Kℝ` (S6, S7); both readings are required.

/-- Intended statement: `C4ℝ` is Kirkwood-form, non-additive, has an `a·b` component, and the
stated witness values hold (for `C4ℝ.C` and for `F4Kℝ`). -/
@[sa_reference "MarginalisationCharacterization.c4RealIsKirkwoodForm"]
def T : Prop :=
  C4ℝ.IsKirkwoodForm ∧
  (∃ w₁ w₂ : U4ℝ, C4ℝ.C (w₁ + w₂) ≠ C4ℝ.C w₁ + C4ℝ.C w₂) ∧
  (∃ i : Idx4, ∀ w : U4ℝ, C4ℝ.C w i = w Idx4.a * w Idx4.b) ∧
  C4ℝ.C (pt 1 0 + pt 0 1) = pt 1 1 ∧
  C4ℝ.C (pt 1 0) + C4ℝ.C (pt 0 1) = pt 0 1 ∧
  F4Kℝ (pt 1 0 + pt 0 1) = pt 1 1 ∧
  F4Kℝ (pt 1 0) + F4Kℝ (pt 0 1) = pt 0 1

/-- S1: the Kirkwood-form predicate holds for `C4ℝ`. -/
@[sa_shadow "MarginalisationCharacterization.c4RealIsKirkwoodForm" 1]
def S1 : Prop := C4ℝ.IsKirkwoodForm

/-- S2: the closure map of `C4ℝ` is non-additive. -/
@[sa_shadow "MarginalisationCharacterization.c4RealIsKirkwoodForm" 2]
def S2 : Prop := ∃ w₁ w₂ : U4ℝ, C4ℝ.C (w₁ + w₂) ≠ C4ℝ.C w₁ + C4ℝ.C w₂

/-- S3: `C4ℝ.C` has a bilinear `a·b` component. -/
@[sa_shadow "MarginalisationCharacterization.c4RealIsKirkwoodForm" 3]
def S3 : Prop := ∃ i : Idx4, ∀ w : U4ℝ, C4ℝ.C w i = w Idx4.a * w Idx4.b

/-- S4: `F₄(u+v) = (1,1)` for `F₄ = C4ℝ.C`, `u = (1,0)`, `v = (0,1)`. -/
@[sa_shadow "MarginalisationCharacterization.c4RealIsKirkwoodForm" 4]
def S4 : Prop := C4ℝ.C (pt 1 0 + pt 0 1) = pt 1 1

/-- S5: `F₄(u) + F₄(v) = (0,1)` for `F₄ = C4ℝ.C`. -/
@[sa_shadow "MarginalisationCharacterization.c4RealIsKirkwoodForm" 5]
def S5 : Prop := C4ℝ.C (pt 1 0) + C4ℝ.C (pt 0 1) = pt 0 1

/-- S6: `F₄(u+v) = (1,1)` for `F₄ = F4Kℝ`. -/
@[sa_shadow "MarginalisationCharacterization.c4RealIsKirkwoodForm" 6]
def S6 : Prop := F4Kℝ (pt 1 0 + pt 0 1) = pt 1 1

/-- S7: `F₄(u) + F₄(v) = (0,1)` for `F₄ = F4Kℝ`. -/
@[sa_shadow "MarginalisationCharacterization.c4RealIsKirkwoodForm" 7]
def S7 : Prop := F4Kℝ (pt 1 0) + F4Kℝ (pt 0 1) = pt 0 1

@[sa_ref_forward "MarginalisationCharacterization.c4RealIsKirkwoodForm" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MarginalisationCharacterization.c4RealIsKirkwoodForm" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MarginalisationCharacterization.c4RealIsKirkwoodForm" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1

@[sa_ref_forward "MarginalisationCharacterization.c4RealIsKirkwoodForm" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1

@[sa_ref_forward "MarginalisationCharacterization.c4RealIsKirkwoodForm" 5]
theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2.1

@[sa_ref_forward "MarginalisationCharacterization.c4RealIsKirkwoodForm" 6]
theorem ref_fwd6 : T → S6 := fun t => t.2.2.2.2.2.1

@[sa_ref_forward "MarginalisationCharacterization.c4RealIsKirkwoodForm" 7]
theorem ref_fwd7 : T → S7 := fun t => t.2.2.2.2.2.2

@[sa_complete "MarginalisationCharacterization.c4RealIsKirkwoodForm"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7) : T :=
  ⟨s1, s2, s3, s4, s5, s6, s7⟩

end Alignment.Shadows.MarginalisationCharacterization.c4RealIsKirkwoodForm

/-! ## `MarginalisationCharacterization.kirkwoodFormNotEquivariant`

Text: "**Theorem T3b (Kirkwood obstruction, concrete form).** There exist concrete real vector
spaces `V₄`, `V₃`, a surjective linear marginalisation `M`, and a Kirkwood-form order-4 closure
`C₄` such that no order-3 closure family `C₃` makes the closure diagram commute." -/

namespace Alignment.Shadows.MarginalisationCharacterization.kirkwoodFormNotEquivariant

-- AMBIGUITY: "concrete real vector spaces" is read as "some real vector spaces in `Type`"
-- (`AddCommGroup` + `Module ℝ`); no finite-dimensionality is required. The witnesses are shared
-- by all conjuncts, so the existential is one atomic requirement.

/-- Intended statement: there are real vector spaces, a surjective linear `M` and a Kirkwood-form
closure family `C₄` such that no order-3 closure family `C₃` gives `Equivariant M C₄.C C₃.C`. -/
@[sa_reference "MarginalisationCharacterization.kirkwoodFormNotEquivariant"]
def T : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : Module ℝ V₄) (_ : AddCommGroup V₃)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    Function.Surjective M ∧ C₄.IsKirkwoodForm ∧
      ¬ ∃ C₃ : ClosureFamily V₃, Equivariant M C₄.C C₃.C

/-- S1: the whole existential (one atomic requirement). -/
@[sa_shadow "MarginalisationCharacterization.kirkwoodFormNotEquivariant" 1]
def S1 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : Module ℝ V₄) (_ : AddCommGroup V₃)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    Function.Surjective M ∧ C₄.IsKirkwoodForm ∧
      ¬ ∃ C₃ : ClosureFamily V₃, Equivariant M C₄.C C₃.C

@[sa_ref_forward "MarginalisationCharacterization.kirkwoodFormNotEquivariant" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MarginalisationCharacterization.kirkwoodFormNotEquivariant"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MarginalisationCharacterization.kirkwoodFormNotEquivariant

/-! ## `MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient`

Text: "**Theorem T3c.** The Kiss–Kenah–Rempala pairwise-closure exactness conditions (cf.
`ClosureTheorem.lean`, Results 51–59) [...] **not sufficient** for marginalisation equivariance
with the order-4 closed system used to generate `F₄`." -/

namespace Alignment.Shadows.MarginalisationCharacterization.kkrNecessaryNotSufficient_notSufficient

-- VOCAB-GAP: "the KKR pairwise-closure exactness conditions" = `closureKappa ψ = 1` (DataTypes);
-- the dependence of the order-4 closed system on ψ is not expressible, so "not sufficient" is
-- the conjunction "the conditions can hold" (S1) and "equivariance fails" (S2/S3).
-- AMBIGUITY: "the order-4 closed system used to generate `F₄`" is the concrete ℝ surrogate with
-- marginalisation `MℝLin`; its RHS is read either as `F4Kℝ` (S2) or as the map of the packaged
-- closure family `C4ℝ` (S3). Both readings are required. "Equivariance fails" means that no
-- order-3 closed RHS `F₃` makes the diagram commute.

/-- Intended statement: KKR exactness can hold, while the concrete order-4 closed system is not
marginalisation-equivariant for `MℝLin` with any order-3 RHS. -/
@[sa_reference "MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient"]
def T : Prop :=
  (∃ ψ : PGFData, ψ.closureKappa = 1) ∧
    (¬ ∃ F₃ : U3ℝ → U3ℝ, Equivariant MℝLin F4Kℝ F₃) ∧
    (¬ ∃ F₃ : U3ℝ → U3ℝ, Equivariant MℝLin C4ℝ.C F₃)

/-- S1: the KKR exactness conditions can be met. -/
@[sa_shadow "MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient" 1]
def S1 : Prop := ∃ ψ : PGFData, ψ.closureKappa = 1

/-- S2: no order-3 RHS makes `MℝLin` intertwine `F4Kℝ`. -/
@[sa_shadow "MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient" 2]
def S2 : Prop := ¬ ∃ F₃ : U3ℝ → U3ℝ, Equivariant MℝLin F4Kℝ F₃

/-- S3: no order-3 RHS makes `MℝLin` intertwine the closure map of `C4ℝ`. -/
@[sa_shadow "MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient" 3]
def S3 : Prop := ¬ ∃ F₃ : U3ℝ → U3ℝ, Equivariant MℝLin C4ℝ.C F₃

@[sa_ref_forward "MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2

@[sa_complete "MarginalisationCharacterization.kkrNecessaryNotSufficient.notSufficient"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.MarginalisationCharacterization.kkrNecessaryNotSufficient_notSufficient

/-! ## `MarginalisationCharacterization.kkrNecessaryNotSufficient.formal`

Text: "The formal statement: there exists a degree distribution `ψ` whose `closureKappa` is `1`
(so the KKR pairwise-exactness criterion of Result 52 is met) together with concrete `V₄`/`V₃`
and a Kirkwood-form order-4 closure `C₄` for which marginalisation equivariance against `M` still
fails." -/

namespace Alignment.Shadows.MarginalisationCharacterization.kkrNecessaryNotSufficient_formal

-- AMBIGUITY: "concrete `V₄`/`V₃`" is read as "some real vector spaces in `Type`"; "against `M`"
-- as some linear `M : V₄ →ₗ[ℝ] V₃` (the text does not say surjective); "marginalisation
-- equivariance fails" as ¬ ∃ F₃, Equivariant M C₄.C F₃. The ψ witness is independent of the
-- vector-space witnesses, so the statement splits into S1 and S2.

/-- Intended statement: some ψ has `closureKappa ψ = 1`, and there are real spaces, a linear `M`
and a Kirkwood-form `C₄` that no order-3 RHS makes equivariant. -/
@[sa_reference "MarginalisationCharacterization.kkrNecessaryNotSufficient.formal"]
def T : Prop :=
  ∃ ψ : PGFData, ψ.closureKappa = 1 ∧
    ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : Module ℝ V₄) (_ : AddCommGroup V₃)
      (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      C₄.IsKirkwoodForm ∧ ¬ ∃ F₃ : V₃ → V₃, Equivariant M C₄.C F₃

/-- S1: some degree distribution meets the KKR criterion `closureKappa ψ = 1`. -/
@[sa_shadow "MarginalisationCharacterization.kkrNecessaryNotSufficient.formal" 1]
def S1 : Prop := ∃ ψ : PGFData, ψ.closureKappa = 1

/-- S2: some Kirkwood-form order-4 closure fails marginalisation equivariance against some `M`. -/
@[sa_shadow "MarginalisationCharacterization.kkrNecessaryNotSufficient.formal" 2]
def S2 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : Module ℝ V₄) (_ : AddCommGroup V₃)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    C₄.IsKirkwoodForm ∧ ¬ ∃ F₃ : V₃ → V₃, Equivariant M C₄.C F₃

@[sa_ref_forward "MarginalisationCharacterization.kkrNecessaryNotSufficient.formal" 1]
theorem ref_fwd1 : T → S1 := fun ⟨ψ, hψ, _⟩ => ⟨ψ, hψ⟩

@[sa_ref_forward "MarginalisationCharacterization.kkrNecessaryNotSufficient.formal" 2]
theorem ref_fwd2 : T → S2 := fun ⟨_, _, h⟩ => h

@[sa_complete "MarginalisationCharacterization.kkrNecessaryNotSufficient.formal"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  match s1 with
  | ⟨ψ, hψ⟩ => ⟨ψ, hψ, s2⟩

end Alignment.Shadows.MarginalisationCharacterization.kkrNecessaryNotSufficient_formal

noncomputable section

/-! ## `MarginalisationCharacterization.closureFamilies.linear` (blind)

Text: "* **Linear** closures: `C(u) = L u` for some linear `L`. (Includes truncation and moment-zero
closures. Exact closures of the unclosed CTMC are in general nonlinear: the KKR-exact pairwise
closure `[ASI] = κ·[AS][SI]/[S]` is rational.)"

S1, S2: `ClosureFamily.IsLinear` means `C(u) = L u` for a linear `L`. S3: the moment-zero closure
`C(u) = 0` is linear. S4: the KKR pairwise closure `([AS], [SI], [S]) ↦ κ[AS][SI]/[S]` (κ ≠ 0) is
not linear on states with `[S] > 0`. -- AMBIGUITY: "truncation" closures are not specified in the
text and are not formalised. -/
namespace Alignment.Shadows.MarginalisationCharacterization.closureFamilies_linear

@[sa_reference "MarginalisationCharacterization.closureFamilies.linear"]
def T : Prop :=
  (∀ {V : Type u} [AddCommGroup V] [Module ℝ V] (C : ClosureFamily V),
      C.IsLinear → ∃ L : V →ₗ[ℝ] V, ∀ x, C.C x = L x) ∧
  (∀ {V : Type u} [AddCommGroup V] [Module ℝ V] (C : ClosureFamily V),
      (∃ L : V →ₗ[ℝ] V, ∀ x, C.C x = L x) → C.IsLinear) ∧
  (∀ {V : Type u} [AddCommGroup V] [Module ℝ V], (ClosureFamily.mk (fun _ : V => 0)).IsLinear) ∧
  (∀ κ : ℝ, κ ≠ 0 → ¬ ∃ L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ,
      ∀ x : Fin 3 → ℝ, 0 < x 2 → κ * x 0 * x 1 / x 2 = L x)

/-- S1: a linear closure is `C(u) = L u` for some linear `L`. -/
@[sa_shadow "MarginalisationCharacterization.closureFamilies.linear" 1]
def S1 : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] (C : ClosureFamily V),
    C.IsLinear → ∃ L : V →ₗ[ℝ] V, ∀ x, C.C x = L x
/-- S2: a closure of the form `C(u) = L u` is linear. -/
@[sa_shadow "MarginalisationCharacterization.closureFamilies.linear" 2]
def S2 : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V] (C : ClosureFamily V),
    (∃ L : V →ₗ[ℝ] V, ∀ x, C.C x = L x) → C.IsLinear
/-- S3: the moment-zero closure is linear. -/
@[sa_shadow "MarginalisationCharacterization.closureFamilies.linear" 3]
def S3 : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module ℝ V], (ClosureFamily.mk (fun _ : V => 0)).IsLinear
/-- S4: the KKR pairwise closure is not linear. -/
@[sa_shadow "MarginalisationCharacterization.closureFamilies.linear" 4]
def S4 : Prop :=
  ∀ κ : ℝ, κ ≠ 0 → ¬ ∃ L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ,
    ∀ x : Fin 3 → ℝ, 0 < x 2 → κ * x 0 * x 1 / x 2 = L x

@[sa_ref_forward "MarginalisationCharacterization.closureFamilies.linear" 1] theorem ref_fwd1 :
    T.{u} → S1.{u} := fun t => t.1
@[sa_ref_forward "MarginalisationCharacterization.closureFamilies.linear" 2] theorem ref_fwd2 :
    T.{u} → S2.{u} := fun t => t.2.1
@[sa_ref_forward "MarginalisationCharacterization.closureFamilies.linear" 3] theorem ref_fwd3 :
    T.{u} → S3.{u} := fun t => t.2.2.1
@[sa_ref_forward "MarginalisationCharacterization.closureFamilies.linear" 4] theorem ref_fwd4 :
    T.{u} → S4 := fun t => t.2.2.2
@[sa_complete "MarginalisationCharacterization.closureFamilies.linear"]
theorem complete (s1 : S1.{u}) (s2 : S2.{u}) (s3 : S3.{u}) (s4 : S4) : T.{u} := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.MarginalisationCharacterization.closureFamilies_linear

/-! ## `MarginalisationCharacterization.header.T1forces` (re-authored blind)

Text: "and Theorem T1 (`MarginalisationFunctor.lean`) shows that, for systems with global flows, any
such algebraic failure forces a dynamical failure of subgraph marginalisation. The T2 witness has
no global order-3 flow, so there the local form `rhs_commute_of_local_traj_commute` is the one that
applies."

S1: with global flows `φ₄`, `φ₃`, failure of `M ∘ F₄ = F₃ ∘ M` forces failure of
`M ∘ φ₄(·,t) = φ₃(M·,t)`. S2: the order-3 field of the T2 witness over ℝ (`F3Kℝ`, c ↦ c²/4) has no
global flow. -- AMBIGUITY: "the local form is the one that applies" is read as its consequence at
the witness: local solutions of `F4Kℝ` from `u₁` and of `F3Kℝ` from `M u₁` never agree on a
neighbourhood of t = 0 (S3). -/
namespace Alignment.Shadows.MarginalisationCharacterization.header_T1forces

open EBCMCategory.MarginalisationDynamicalGap

@[sa_reference "MarginalisationCharacterization.header.T1forces"]
def T : Prop :=
  (∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
      [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄)
      (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ →
      ¬ (∀ w, M (F₄ w) = F₃ (M w)) → ¬ ∀ w t, M (φ₄ w t) = φ₃ (M w) t) ∧
  (∀ φ₃ : U3ℝ → ℝ → U3ℝ, ¬ IsFlow F3Kℝ φ₃) ∧
  (∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ) (δ : ℝ), 0 < δ → ψ₄ 0 = u₁ → ψ₃ 0 = MℝLinCLM u₁ →
      (∀ t, |t| < δ → HasDerivAt ψ₄ (F4Kℝ (ψ₄ t)) t) →
      (∀ t, |t| < δ → HasDerivAt ψ₃ (F3Kℝ (ψ₃ t)) t) →
      ¬ ∀ t, |t| < δ → MℝLinCLM (ψ₄ t) = ψ₃ t)

/-- S1: with global flows, an algebraic failure forces a trajectory failure. -/
@[sa_shadow "MarginalisationCharacterization.header.T1forces" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄)
    (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ →
    ¬ (∀ w, M (F₄ w) = F₃ (M w)) → ¬ ∀ w t, M (φ₄ w t) = φ₃ (M w) t
/-- S2: the T2 witness has no global order-3 flow. -/
@[sa_shadow "MarginalisationCharacterization.header.T1forces" 2]
def S2 : Prop := ∀ φ₃ : U3ℝ → ℝ → U3ℝ, ¬ IsFlow F3Kℝ φ₃
/-- S3: at the witness, local solutions do not agree near t = 0. -/
@[sa_shadow "MarginalisationCharacterization.header.T1forces" 3]
def S3 : Prop :=
  ∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ) (δ : ℝ), 0 < δ → ψ₄ 0 = u₁ → ψ₃ 0 = MℝLinCLM u₁ →
    (∀ t, |t| < δ → HasDerivAt ψ₄ (F4Kℝ (ψ₄ t)) t) →
    (∀ t, |t| < δ → HasDerivAt ψ₃ (F3Kℝ (ψ₃ t)) t) →
    ¬ ∀ t, |t| < δ → MℝLinCLM (ψ₄ t) = ψ₃ t

@[sa_ref_forward "MarginalisationCharacterization.header.T1forces" 1] theorem ref_fwd1 :
    T.{u, v} → S1.{u, v} := fun t => t.1
@[sa_ref_forward "MarginalisationCharacterization.header.T1forces" 2] theorem ref_fwd2 :
    T.{u, v} → S2 := fun t => t.2.1
@[sa_ref_forward "MarginalisationCharacterization.header.T1forces" 3] theorem ref_fwd3 :
    T.{u, v} → S3 := fun t => t.2.2
@[sa_complete "MarginalisationCharacterization.header.T1forces"]
theorem complete (s1 : S1.{u, v}) (s2 : S2) (s3 : S3) : T.{u, v} := ⟨s1, s2, s3⟩

end Alignment.Shadows.MarginalisationCharacterization.header_T1forces

/-! ## `MarginalisationCharacterization.header.T3` (re-authored blind)

Text: "T3 — proved here — is an **existential** statement (T3b): *There is a linear marginalisation
`M` and a non-additive order-4 closure `C₄` such that no order-3 closure `C₃` makes the diagram
commute.*"

"Makes the diagram commute" = `Equivariant M C₄.C C₃.C`. -- AMBIGUITY: "non-additive" is read both
as the vocabulary's marker `IsKirkwoodForm` (S1) and literally, `C₄` not additive (S2). "Proved
here" is a remark. -/
namespace Alignment.Shadows.MarginalisationCharacterization.header_T3

@[sa_reference "MarginalisationCharacterization.header.T3"]
def T : Prop :=
  (∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
      (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      C₄.IsKirkwoodForm ∧ ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M C₄.C C₃.C) ∧
  (∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
      (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      (¬ ∀ x y, C₄.C (x + y) = C₄.C x + C₄.C y) ∧
        ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M C₄.C C₃.C)

/-- S1: some linear `M` and Kirkwood-form `C₄` admit no commuting `C₃`. -/
@[sa_shadow "MarginalisationCharacterization.header.T3" 1]
def S1 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    C₄.IsKirkwoodForm ∧ ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M C₄.C C₃.C
/-- S2: some linear `M` and non-additive `C₄` admit no commuting `C₃`. -/
@[sa_shadow "MarginalisationCharacterization.header.T3" 2]
def S2 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    (¬ ∀ x y, C₄.C (x + y) = C₄.C x + C₄.C y) ∧ ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M C₄.C C₃.C

@[sa_ref_forward "MarginalisationCharacterization.header.T3" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "MarginalisationCharacterization.header.T3" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "MarginalisationCharacterization.header.T3"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MarginalisationCharacterization.header_T3

/-! ## `MarginalisationCharacterization.header.interLevel` (re-authored blind)

Text: "T3 below is a different statement: a closure that is exact at the pairwise level constrains
nothing at order 4, and the **inter-level marginalisation diagram need not commute**. The formal
witness (T3c) only pairs a Poisson record, whose `closureKappa` is 1, with the unrelated surrogate
of T3b."

S1: the Poisson record has `closureKappa = 1`; S2: the T3b surrogate (`C4ℝ` under `MℝLin`) admits
no commuting order-3 closure, so the inter-level diagram need not commute. "Constrains nothing"
is informal. -/
namespace Alignment.Shadows.MarginalisationCharacterization.header_interLevel

@[sa_reference "MarginalisationCharacterization.header.interLevel"]
def T : Prop :=
  (∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).closureKappa = 1) ∧
  (∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin C4ℝ.C C₃.C)

/-- S1: a Poisson record has `closureKappa = 1`. -/
@[sa_shadow "MarginalisationCharacterization.header.interLevel" 1]
def S1 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).closureKappa = 1
/-- S2: the T3b surrogate's inter-level diagram does not commute for any `C₃`. -/
@[sa_shadow "MarginalisationCharacterization.header.interLevel" 2]
def S2 : Prop := ∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin C4ℝ.C C₃.C

@[sa_ref_forward "MarginalisationCharacterization.header.interLevel" 1] theorem ref_fwd1 :
    T → S1 := fun t => t.1
@[sa_ref_forward "MarginalisationCharacterization.header.interLevel" 2] theorem ref_fwd2 :
    T → S2 := fun t => t.2
@[sa_complete "MarginalisationCharacterization.header.interLevel"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MarginalisationCharacterization.header_interLevel

/-! ## `MarginalisationCharacterization.header.kkrNotSufficient` (re-authored blind)

Text: "T3c shows only that a KKR-exact degree record can be paired with an order-4 closure that is
**not** equivariant."

KKR-exact record: `closureKappa = 1` (DataTypes); "not equivariant": no order-3 closure makes the
diagram commute. -/
namespace Alignment.Shadows.MarginalisationCharacterization.header_kkrNotSufficient

@[sa_reference "MarginalisationCharacterization.header.kkrNotSufficient"]
def T : Prop :=
  (∃ ψ : PGFData, ψ.closureKappa = 1) ∧
  (∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
      (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M C₄.C C₃.C)

/-- S1: a KKR-exact degree record exists. -/
@[sa_shadow "MarginalisationCharacterization.header.kkrNotSufficient" 1]
def S1 : Prop := ∃ ψ : PGFData, ψ.closureKappa = 1
/-- S2: a non-equivariant order-4 closure exists. -/
@[sa_shadow "MarginalisationCharacterization.header.kkrNotSufficient" 2]
def S2 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M C₄.C C₃.C

@[sa_ref_forward "MarginalisationCharacterization.header.kkrNotSufficient" 1] theorem ref_fwd1 :
    T → S1 := fun t => t.1
@[sa_ref_forward "MarginalisationCharacterization.header.kkrNotSufficient" 2] theorem ref_fwd2 :
    T → S2 := fun t => t.2
@[sa_complete "MarginalisationCharacterization.header.kkrNotSufficient"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MarginalisationCharacterization.header_kkrNotSufficient

/-! ## `MarginalisationCharacterization.header.onlyTrivial` (blind)

Text: "Non-additive closures can escape the obstruction: some `C₃` makes the diagram commute iff
`C₄` maps each fibre of `M` into a single fibre (`exists_equivariant_iff_fibrewise`)."

-- AMBIGUITY: "non-additive" read both literally (S1) and as `IsKirkwoodForm` (S2). S3, S4: the
fibre criterion, both directions, for every linear `M` and closure `C₄`. -/
namespace Alignment.Shadows.MarginalisationCharacterization.header_onlyTrivial

@[sa_reference "MarginalisationCharacterization.header.onlyTrivial"]
def T : Prop :=
  (∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
      (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      (¬ ∀ x y, C₄.C (x + y) = C₄.C x + C₄.C y) ∧
        ∃ C₃ : ClosureFamily V₃, Equivariant M C₄.C C₃.C) ∧
  (∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
      (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      C₄.IsKirkwoodForm ∧ ∃ C₃ : ClosureFamily V₃, Equivariant M C₄.C C₃.C) ∧
  (∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
      (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      (∃ C₃ : ClosureFamily V₃, Equivariant M C₄.C C₃.C) →
        ∀ w w', M w = M w' → M (C₄.C w) = M (C₄.C w')) ∧
  (∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
      (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      (∀ w w', M w = M w' → M (C₄.C w) = M (C₄.C w')) →
        ∃ C₃ : ClosureFamily V₃, Equivariant M C₄.C C₃.C)

/-- S1: some non-additive closure admits a commuting `C₃`. -/
@[sa_shadow "MarginalisationCharacterization.header.onlyTrivial" 1]
def S1 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    (¬ ∀ x y, C₄.C (x + y) = C₄.C x + C₄.C y) ∧ ∃ C₃ : ClosureFamily V₃, Equivariant M C₄.C C₃.C
/-- S2: some Kirkwood-form closure admits a commuting `C₃`. -/
@[sa_shadow "MarginalisationCharacterization.header.onlyTrivial" 2]
def S2 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    C₄.IsKirkwoodForm ∧ ∃ C₃ : ClosureFamily V₃, Equivariant M C₄.C C₃.C
/-- S3: a commuting `C₃` forces `C₄` to map fibres into fibres. -/
@[sa_shadow "MarginalisationCharacterization.header.onlyTrivial" 3]
def S3 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    (∃ C₃ : ClosureFamily V₃, Equivariant M C₄.C C₃.C) →
      ∀ w w', M w = M w' → M (C₄.C w) = M (C₄.C w')
/-- S4: mapping fibres into fibres gives a commuting `C₃`. -/
@[sa_shadow "MarginalisationCharacterization.header.onlyTrivial" 4]
def S4 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    (∀ w w', M w = M w' → M (C₄.C w) = M (C₄.C w')) →
      ∃ C₃ : ClosureFamily V₃, Equivariant M C₄.C C₃.C

@[sa_ref_forward "MarginalisationCharacterization.header.onlyTrivial" 1] theorem ref_fwd1 :
    T.{u, v} → S1 := fun t => t.1
@[sa_ref_forward "MarginalisationCharacterization.header.onlyTrivial" 2] theorem ref_fwd2 :
    T.{u, v} → S2 := fun t => t.2.1
@[sa_ref_forward "MarginalisationCharacterization.header.onlyTrivial" 3] theorem ref_fwd3 :
    T.{u, v} → S3.{u, v} := fun t => t.2.2.1
@[sa_ref_forward "MarginalisationCharacterization.header.onlyTrivial" 4] theorem ref_fwd4 :
    T.{u, v} → S4.{u, v} := fun t => t.2.2.2
@[sa_complete "MarginalisationCharacterization.header.onlyTrivial"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3.{u, v}) (s4 : S4.{u, v}) : T.{u, v} :=
  ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.MarginalisationCharacterization.header_onlyTrivial

/-! ## `MarginalisationCharacterization.isLinearAdmitsEquivariant` (re-authored blind)

Text: "**Vacuous; kept for compatibility.** The statement is `∃ F₃, Equivariant M C₄.C F₃ ∨ True`,
which holds because of the disjunct `True`; it does not show that an `IsLinear` closure admits an
equivariant `F₃`. The correct criterion is `linear_admits_equivariant_iff`: a linear `L₄` admits an
equivariant `F₃` iff `L₄` maps `ker M` into `ker M`."

The quoted Lean statement is a tautology and is not a requirement. S1: it is false that every
`IsLinear` closure admits an equivariant `F₃`; S2, S3: the criterion, both directions. -/
namespace Alignment.Shadows.MarginalisationCharacterization.isLinearAdmitsEquivariant

@[sa_reference "MarginalisationCharacterization.isLinearAdmitsEquivariant"]
def T : Prop :=
  (∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
      (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      C₄.IsLinear ∧ ¬ ∃ F₃ : V₃ → V₃, Equivariant M C₄.C F₃) ∧
  (∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
      (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
      (∃ F₃ : V₃ → V₃, Equivariant M L₄ F₃) → ∀ x ∈ LinearMap.ker M, L₄ x ∈ LinearMap.ker M) ∧
  (∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
      (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
      (∀ x ∈ LinearMap.ker M, L₄ x ∈ LinearMap.ker M) → ∃ F₃ : V₃ → V₃, Equivariant M L₄ F₃)

/-- S1: some `IsLinear` closure admits no equivariant `F₃`. -/
@[sa_shadow "MarginalisationCharacterization.isLinearAdmitsEquivariant" 1]
def S1 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    C₄.IsLinear ∧ ¬ ∃ F₃ : V₃ → V₃, Equivariant M C₄.C F₃
/-- S2: an equivariant `F₃` for linear `L₄` forces `L₄(ker M) ⊆ ker M`. -/
@[sa_shadow "MarginalisationCharacterization.isLinearAdmitsEquivariant" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
    (∃ F₃ : V₃ → V₃, Equivariant M L₄ F₃) → ∀ x ∈ LinearMap.ker M, L₄ x ∈ LinearMap.ker M
/-- S3: `L₄(ker M) ⊆ ker M` gives an equivariant `F₃`. -/
@[sa_shadow "MarginalisationCharacterization.isLinearAdmitsEquivariant" 3]
def S3 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
    (∀ x ∈ LinearMap.ker M, L₄ x ∈ LinearMap.ker M) → ∃ F₃ : V₃ → V₃, Equivariant M L₄ F₃

@[sa_ref_forward "MarginalisationCharacterization.isLinearAdmitsEquivariant" 1] theorem ref_fwd1 :
    T.{u, v} → S1 := fun t => t.1
@[sa_ref_forward "MarginalisationCharacterization.isLinearAdmitsEquivariant" 2] theorem ref_fwd2 :
    T.{u, v} → S2.{u, v} := fun t => t.2.1
@[sa_ref_forward "MarginalisationCharacterization.isLinearAdmitsEquivariant" 3] theorem ref_fwd3 :
    T.{u, v} → S3.{u, v} := fun t => t.2.2
@[sa_complete "MarginalisationCharacterization.isLinearAdmitsEquivariant"]
theorem complete (s1 : S1) (s2 : S2.{u, v}) (s3 : S3.{u, v}) : T.{u, v} := ⟨s1, s2, s3⟩

end Alignment.Shadows.MarginalisationCharacterization.isLinearAdmitsEquivariant

/-! ## `MarginalisationCharacterization.kkrNecessaryNotSufficient.concretely` (blind)

Text: "The order-4 closure `C₄` is independent data: a degree record that meets the KKR criterion
(`closureKappa = 1` for Poisson) can be paired with the non-equivariant surrogate of T3b. It is
false that T3b applies to every Kirkwood-form `C₄`: with `M = id`, `x ↦ x²` is Kirkwood-form and
equivariant (`exists_kirkwoodForm_equivariant`)."

S1: Poisson records meet the KKR criterion; S2: the T3b surrogate `C4ℝ` is non-equivariant under
`MℝLin` (the pairing is the conjunction); S3, S4: on ℝ with `M = id`, `x ↦ x²` is Kirkwood-form
and equivariant. -/
namespace Alignment.Shadows.MarginalisationCharacterization.kkrNecessaryNotSufficient_concretely

@[sa_reference "MarginalisationCharacterization.kkrNecessaryNotSufficient.concretely"]
def T : Prop :=
  (∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).closureKappa = 1) ∧
  (∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin C4ℝ.C C₃.C) ∧
  (ClosureFamily.mk (fun x : ℝ => x ^ 2)).IsKirkwoodForm ∧
  Equivariant (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (fun x => x ^ 2) (fun x => x ^ 2)

/-- S1: Poisson records have `closureKappa = 1`. -/
@[sa_shadow "MarginalisationCharacterization.kkrNecessaryNotSufficient.concretely" 1]
def S1 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).closureKappa = 1
/-- S2: the T3b surrogate is non-equivariant. -/
@[sa_shadow "MarginalisationCharacterization.kkrNecessaryNotSufficient.concretely" 2]
def S2 : Prop := ∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin C4ℝ.C C₃.C
/-- S3: `x ↦ x²` on ℝ is Kirkwood-form. -/
@[sa_shadow "MarginalisationCharacterization.kkrNecessaryNotSufficient.concretely" 3]
def S3 : Prop := (ClosureFamily.mk (fun x : ℝ => x ^ 2)).IsKirkwoodForm
/-- S4: `x ↦ x²` is equivariant under `M = id`. -/
@[sa_shadow "MarginalisationCharacterization.kkrNecessaryNotSufficient.concretely" 4]
def S4 : Prop := Equivariant (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (fun x => x ^ 2) (fun x => x ^ 2)

@[sa_ref_forward "MarginalisationCharacterization.kkrNecessaryNotSufficient.concretely" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MarginalisationCharacterization.kkrNecessaryNotSufficient.concretely" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "MarginalisationCharacterization.kkrNecessaryNotSufficient.concretely" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "MarginalisationCharacterization.kkrNecessaryNotSufficient.concretely" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "MarginalisationCharacterization.kkrNecessaryNotSufficient.concretely"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.MarginalisationCharacterization.kkrNecessaryNotSufficient_concretely

/-! ## `MarginalisationCharacterization.linearClosureEquivariant.b` (blind)

Text: "It is not the only case in which the diagram commutes: see `exists_equivariant_iff_fibrewise`
and `exists_kirkwoodForm_equivariant`."

"It" is the linear case (linear closures preserving `ker M`). S1: some closure that is not linear
has a commuting diagram. -/
namespace Alignment.Shadows.MarginalisationCharacterization.linearClosureEquivariant_b

@[sa_reference "MarginalisationCharacterization.linearClosureEquivariant.b"]
def T : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    ¬ C₄.IsLinear ∧ ∃ C₃ : ClosureFamily V₃, Equivariant M C₄.C C₃.C

/-- S1: a non-linear closure can make the diagram commute. -/
@[sa_shadow "MarginalisationCharacterization.linearClosureEquivariant.b" 1]
def S1 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    ¬ C₄.IsLinear ∧ ∃ C₃ : ClosureFamily V₃, Equivariant M C₄.C C₃.C

@[sa_ref_forward "MarginalisationCharacterization.linearClosureEquivariant.b" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "MarginalisationCharacterization.linearClosureEquivariant.b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MarginalisationCharacterization.linearClosureEquivariant_b

/-! ## `MarginalisationCharacterization.table.T3a` (re-authored blind)

Text: "| T3a | A linear `L₄` admits an equivariant `F₃` iff `L₄(ker M) ⊆ ker M` |" -/
namespace Alignment.Shadows.MarginalisationCharacterization.table_T3a

@[sa_reference "MarginalisationCharacterization.table.T3a"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
    (∃ F₃ : V₃ → V₃, Equivariant M L₄ F₃) ↔ (LinearMap.ker M).map L₄ ≤ LinearMap.ker M

/-- S1 (→). -/
@[sa_shadow "MarginalisationCharacterization.table.T3a" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
    (∃ F₃ : V₃ → V₃, Equivariant M L₄ F₃) → (LinearMap.ker M).map L₄ ≤ LinearMap.ker M
/-- S2 (←). -/
@[sa_shadow "MarginalisationCharacterization.table.T3a" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
    (LinearMap.ker M).map L₄ ≤ LinearMap.ker M → ∃ F₃ : V₃ → V₃, Equivariant M L₄ F₃

@[sa_ref_forward "MarginalisationCharacterization.table.T3a" 1] theorem ref_fwd1 :
    T.{u, v} → S1.{u, v} := by
  intro t V₄ V₃ _ _ _ _ M L₄
  exact (t M L₄).1
@[sa_ref_forward "MarginalisationCharacterization.table.T3a" 2] theorem ref_fwd2 :
    T.{u, v} → S2.{u, v} := by
  intro t V₄ V₃ _ _ _ _ M L₄
  exact (t M L₄).2
@[sa_complete "MarginalisationCharacterization.table.T3a"]
theorem complete (s1 : S1.{u, v}) (s2 : S2.{u, v}) : T.{u, v} := by
  intro V₄ V₃ _ _ _ _ M L₄
  exact ⟨s1 M L₄, s2 M L₄⟩

end Alignment.Shadows.MarginalisationCharacterization.table_T3a

/-! ## `MarginalisationCharacterization.table.T3b` (re-authored blind)

Text: "| T3b | Some linear `M` and non-additive `C₄` admit no equivariant `C₃` | [...] | |
(existential; no `sorry`) |"

-- AMBIGUITY: "non-additive" read as `IsKirkwoodForm` (S1) and literally (S2). "No `sorry`" is a
remark about the proof. -/
namespace Alignment.Shadows.MarginalisationCharacterization.table_T3b

@[sa_reference "MarginalisationCharacterization.table.T3b"]
def T : Prop :=
  (∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
      (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      C₄.IsKirkwoodForm ∧ ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M C₄.C C₃.C) ∧
  (∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
      (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      (¬ ∀ x y, C₄.C (x + y) = C₄.C x + C₄.C y) ∧
        ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M C₄.C C₃.C)

/-- S1: Kirkwood-form reading. -/
@[sa_shadow "MarginalisationCharacterization.table.T3b" 1]
def S1 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    C₄.IsKirkwoodForm ∧ ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M C₄.C C₃.C
/-- S2: literal non-additivity reading. -/
@[sa_shadow "MarginalisationCharacterization.table.T3b" 2]
def S2 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    (¬ ∀ x y, C₄.C (x + y) = C₄.C x + C₄.C y) ∧ ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M C₄.C C₃.C

@[sa_ref_forward "MarginalisationCharacterization.table.T3b" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "MarginalisationCharacterization.table.T3b" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "MarginalisationCharacterization.table.T3b"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MarginalisationCharacterization.table_T3b

/-! ## `MarginalisationCharacterization.table.T3c.b` (re-authored blind)

Text: "Corollary: KKR-exactness [...] | | a KKR-exact record pairs with a non-equivariant order-4
closure |" -/
namespace Alignment.Shadows.MarginalisationCharacterization.table_T3c_b

@[sa_reference "MarginalisationCharacterization.table.T3c.b"]
def T : Prop :=
  (∃ ψ : PGFData, ψ.closureKappa = 1) ∧
  (∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
      (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M C₄.C C₃.C)

/-- S1: a KKR-exact record exists. -/
@[sa_shadow "MarginalisationCharacterization.table.T3c.b" 1]
def S1 : Prop := ∃ ψ : PGFData, ψ.closureKappa = 1
/-- S2: a non-equivariant order-4 closure exists. -/
@[sa_shadow "MarginalisationCharacterization.table.T3c.b" 2]
def S2 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M C₄.C C₃.C

@[sa_ref_forward "MarginalisationCharacterization.table.T3c.b" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "MarginalisationCharacterization.table.T3c.b" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "MarginalisationCharacterization.table.T3c.b"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MarginalisationCharacterization.table_T3c_b

/-! ## `MarginalisationCharacterization.existsEquivariantIffFibrewise` (blind)

Text: "**Fibre criterion.** For any field `F` on `V₄`, some order-3 field `F₃` satisfies
`M ∘ F = F₃ ∘ M` iff `F` maps each fibre of `M` into a single fibre:
`M u = M u' → M (F u) = M (F u')`." -/
namespace Alignment.Shadows.MarginalisationCharacterization.existsEquivariantIffFibrewise

@[sa_reference "MarginalisationCharacterization.existsEquivariantIffFibrewise"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (F : V₄ → V₄),
    (∃ F₃ : V₃ → V₃, ∀ w, M (F w) = F₃ (M w)) ↔ ∀ w w', M w = M w' → M (F w) = M (F w')

/-- S1 (→). -/
@[sa_shadow "MarginalisationCharacterization.existsEquivariantIffFibrewise" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (F : V₄ → V₄),
    (∃ F₃ : V₃ → V₃, ∀ w, M (F w) = F₃ (M w)) → ∀ w w', M w = M w' → M (F w) = M (F w')
/-- S2 (←). -/
@[sa_shadow "MarginalisationCharacterization.existsEquivariantIffFibrewise" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (F : V₄ → V₄),
    (∀ w w', M w = M w' → M (F w) = M (F w')) → ∃ F₃ : V₃ → V₃, ∀ w, M (F w) = F₃ (M w)

@[sa_ref_forward "MarginalisationCharacterization.existsEquivariantIffFibrewise" 1]
theorem ref_fwd1 : T.{u, v} → S1.{u, v} := by
  intro t V₄ V₃ _ _ _ _ M F
  exact (t M F).1
@[sa_ref_forward "MarginalisationCharacterization.existsEquivariantIffFibrewise" 2]
theorem ref_fwd2 : T.{u, v} → S2.{u, v} := by
  intro t V₄ V₃ _ _ _ _ M F
  exact (t M F).2
@[sa_complete "MarginalisationCharacterization.existsEquivariantIffFibrewise"]
theorem complete (s1 : S1.{u, v}) (s2 : S2.{u, v}) : T.{u, v} := by
  intro V₄ V₃ _ _ _ _ M F
  exact ⟨s1 M F, s2 M F⟩

end Alignment.Shadows.MarginalisationCharacterization.existsEquivariantIffFibrewise

/-! ## `MarginalisationCharacterization.linearAdmitsEquivariantIff` (blind)

Text: "**Theorem T3a (corrected).** A linear field `L₄` admits an order-3 field `F₃` with
`M ∘ L₄ = F₃ ∘ M` iff `L₄` maps `ker M` into `ker M`. So linear closures are *not* equivariant for
every linear `M`." -/
namespace Alignment.Shadows.MarginalisationCharacterization.linearAdmitsEquivariantIff

@[sa_reference "MarginalisationCharacterization.linearAdmitsEquivariantIff"]
def T : Prop :=
  (∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
      (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
      (∃ F₃ : V₃ → V₃, ∀ w, M (L₄ w) = F₃ (M w)) →
        ∀ x ∈ LinearMap.ker M, L₄ x ∈ LinearMap.ker M) ∧
  (∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
      (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
      (∀ x ∈ LinearMap.ker M, L₄ x ∈ LinearMap.ker M) →
        ∃ F₃ : V₃ → V₃, ∀ w, M (L₄ w) = F₃ (M w)) ∧
  (∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
      (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
      ¬ ∃ F₃ : V₃ → V₃, ∀ w, M (L₄ w) = F₃ (M w))

/-- S1 (→): an order-3 field with `M ∘ L₄ = F₃ ∘ M` forces `L₄(ker M) ⊆ ker M`. -/
@[sa_shadow "MarginalisationCharacterization.linearAdmitsEquivariantIff" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
    (∃ F₃ : V₃ → V₃, ∀ w, M (L₄ w) = F₃ (M w)) → ∀ x ∈ LinearMap.ker M, L₄ x ∈ LinearMap.ker M
/-- S2 (←). -/
@[sa_shadow "MarginalisationCharacterization.linearAdmitsEquivariantIff" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
    (∀ x ∈ LinearMap.ker M, L₄ x ∈ LinearMap.ker M) → ∃ F₃ : V₃ → V₃, ∀ w, M (L₄ w) = F₃ (M w)
/-- S3: some linear field admits no such `F₃` for some linear `M`. -/
@[sa_shadow "MarginalisationCharacterization.linearAdmitsEquivariantIff" 3]
def S3 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
    ¬ ∃ F₃ : V₃ → V₃, ∀ w, M (L₄ w) = F₃ (M w)

@[sa_ref_forward "MarginalisationCharacterization.linearAdmitsEquivariantIff" 1]
theorem ref_fwd1 : T.{u, v} → S1.{u, v} := fun t => t.1
@[sa_ref_forward "MarginalisationCharacterization.linearAdmitsEquivariantIff" 2]
theorem ref_fwd2 : T.{u, v} → S2.{u, v} := fun t => t.2.1
@[sa_ref_forward "MarginalisationCharacterization.linearAdmitsEquivariantIff" 3]
theorem ref_fwd3 : T.{u, v} → S3 := fun t => t.2.2
@[sa_complete "MarginalisationCharacterization.linearAdmitsEquivariantIff"]
theorem complete (s1 : S1.{u, v}) (s2 : S2.{u, v}) (s3 : S3) : T.{u, v} := ⟨s1, s2, s3⟩

end Alignment.Shadows.MarginalisationCharacterization.linearAdmitsEquivariantIff

/-! ## `MarginalisationCharacterization.existsKirkwoodFormEquivariant` (blind)

Text: "A non-additive (`IsKirkwoodForm`) closure can be equivariant: with `M = id` on `ℝ`, the field
`x ↦ x²` is non-additive and commutes with itself." -/
namespace Alignment.Shadows.MarginalisationCharacterization.existsKirkwoodFormEquivariant

@[sa_reference "MarginalisationCharacterization.existsKirkwoodFormEquivariant"]
def T : Prop :=
  (ClosureFamily.mk (fun x : ℝ => x ^ 2)).IsKirkwoodForm ∧
    Equivariant (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (fun x => x ^ 2) (fun x => x ^ 2)

/-- S1: `x ↦ x²` is Kirkwood-form (non-additive). -/
@[sa_shadow "MarginalisationCharacterization.existsKirkwoodFormEquivariant" 1]
def S1 : Prop := (ClosureFamily.mk (fun x : ℝ => x ^ 2)).IsKirkwoodForm
/-- S2: with `M = id`, `x ↦ x²` commutes with itself. -/
@[sa_shadow "MarginalisationCharacterization.existsKirkwoodFormEquivariant" 2]
def S2 : Prop := Equivariant (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (fun x => x ^ 2) (fun x => x ^ 2)

@[sa_ref_forward "MarginalisationCharacterization.existsKirkwoodFormEquivariant" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MarginalisationCharacterization.existsKirkwoodFormEquivariant" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "MarginalisationCharacterization.existsKirkwoodFormEquivariant"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MarginalisationCharacterization.existsKirkwoodFormEquivariant

end
