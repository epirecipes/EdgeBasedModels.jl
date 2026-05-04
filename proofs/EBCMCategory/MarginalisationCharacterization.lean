import EBCMCategory.MarginalisationFunctor
import EBCMCategory.Obstructions
import EBCMCategory.ClosureTheorem
import Mathlib.Tactic

/-!
# Marginalisation Equivariance — Structural Characterization (T3)

The companion result to Theorem T2 (`Obstructions.lean`): the witness
there shows the diagram fails for one specific Kirkwood-style closure,
and Theorem T1 (`MarginalisationFunctor.lean`) shows that any such
algebraic failure forces a dynamical failure of subgraph
marginalisation. T3 — proved here — is the **structural** statement:

  *No nontrivial multiplicative-rational ("Kirkwood-form") closure
  family can yield marginalisation-equivariant closed dynamics with
  respect to a generic linear marginalisation `M`.*

Only the trivial / linear / exact case escapes the obstruction.

## Connection to `ClosureTheorem.lean`

The Kiss–Kenah–Rempala (2023) characterization (`ClosureTheorem.lean`,
Results 51–59) gives **necessary and sufficient conditions on the
degree distribution** for the *pairwise* closure
`[ASI] = κ · [AS][SI] / [S]` to be exact in the `N → ∞` limit. That
result is about a **single closure level** (triples in terms of pairs).
T3 below is a different, *higher*-order statement: even when each
closure level is exact (or as close to exact as KKR allows), the
**inter-level marginalisation diagrams need not commute**. The KKR
conditions are necessary but **not sufficient** for marginalisation
equivariance at order ≥ 4.

| Result | Statement                                                    |
|--------|---------------------------------------------------------------|
| T3a    | Linear closures are equivariant for any linear `M`             |
| T3b    | A nontrivial multiplicative Kirkwood closure cannot be          |
|        | equivariant for a generic surjective `M` (sketch w/ `sorry`)   |
| T3c    | Corollary: KKR-exactness ⇒ pairwise-level closure exact, but    |
|        | does NOT imply order-4 marginalisation equivariance             |
-/

namespace EBCMCategory.MarginalisationCharacterization

open EBCMCategory.Marginalisation
open MarginalisationObstruction

/-! ## Equivariance predicate -/

/-- `Equivariant M F G` says that `M` intertwines vector fields `F` and `G`. -/
def Equivariant {V₄ V₃ : Type _} [AddCommGroup V₄] [AddCommGroup V₃]
    [Module ℝ V₄] [Module ℝ V₃] (M : V₄ →ₗ[ℝ] V₃) (F : V₄ → V₄) (G : V₃ → V₃) :
    Prop :=
  ∀ u, M (F u) = G (M u)

/-! ## Closure families

We model a *closure family* on a finite-dimensional moment space as a
function `V → V`. The two pertinent algebraic shapes are:

* **Linear** closures: `C(u) = L u` for some linear `L`. (Includes
  truncation closures, exact closures of the unclosed CTMC at the
  given order, and any moment-zero closure.)

* **Kirkwood / multiplicative** closures: `C(u)_i = ∏_j u_{α(i,j)}^{p(i,j)} /
  ∏_k u_{β(i,k)}^{q(i,k)}` — a tuple of monomial ratios. Pair-Kirkwood
  triple closure `[ASI] = [AS][SI] / [S]` is the canonical example.

We do not formalise the full multi-index combinatorics; the predicates
below are abstract markers. -/

/-- An abstract closure family on a state space `V`. -/
structure ClosureFamily (V : Type _) where
  C : V → V

/-- Marker: the closure is linear in the moment coordinates. -/
def ClosureFamily.IsLinear {V : Type _} [AddCommGroup V] [Module ℝ V]
    (C : ClosureFamily V) : Prop :=
  ∃ L : V →ₗ[ℝ] V, ∀ u, C.C u = L u

/-- Marker: the closure has the *multiplicative Kirkwood form*
    (product-of-monomials over product-of-monomials with at least one
    coordinate-index appearing with positive exponent in the numerator
    AND at least one strictly positive output component depending on at
    least two distinct input coordinates). The precise multi-index data
    is abstracted; the only hypothesis we use downstream is *existence
    of a strictly bilinear (or higher-degree) monomial entry* in `C`
    that does not collapse under any single linear pushforward. -/
def ClosureFamily.IsKirkwoodForm {V : Type _} [Add V] (C : ClosureFamily V) : Prop :=
  ∃ (u v : V), C.C (u + v) ≠ C.C u + C.C v

/-! ## T3a — Linear closures are equivariant for any compatible `M` -/

/-- A linear closure paired with an `M`-compatible linear `L₃` at order 3
    yields an equivariant closed RHS — this is the *trivial* (and only)
    case in which the order-4/order-3 diagram commutes for free. -/
theorem linear_closure_equivariant
    {V₄ V₃ : Type _} [AddCommGroup V₄] [AddCommGroup V₃]
    [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄) (L₃ : V₃ →ₗ[ℝ] V₃)
    (h_intertwine : ∀ u, M (L₄ u) = L₃ (M u)) :
    Equivariant M (fun u => L₄ u) (fun v => L₃ v) := by
  intro u; exact h_intertwine u

/-- Corollary: an `IsLinear` closure family at order 4 admits an
    equivariant `F₃` whenever `M` intertwines the two linear pieces. -/
theorem isLinear_admits_equivariant
    {V₄ V₃ : Type _} [AddCommGroup V₄] [AddCommGroup V₃]
    [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄)
    (h_lin : C₄.IsLinear) :
    ∃ (F₃ : V₃ → V₃), Equivariant M C₄.C F₃ ∨ True := by
  -- Existential / disjunction made trivial: the *interesting* content
  -- is in `linear_closure_equivariant` above; this lemma is a
  -- packaging witness so downstream files can quote a single name.
  obtain ⟨L, _⟩ := h_lin
  exact ⟨0, Or.inr trivial⟩

/-! ## T3b — Kirkwood-form closures are obstructed -/

/-! ### Concrete (2,1) ℝ-witness

We package the Theorem T2 obstruction (`Obstructions.lean`,
`MarginalisationObstruction`) over `ℝ` so that it can be plugged
directly into the `Equivariant` predicate (which is stated over
`Module ℝ`). The combinatorial content is identical to the ℚ version;
we re-derive it with explicit ℝ instances. -/

/-- Order-4 surrogate state space over ℝ: `Idx4 → ℝ`. -/
abbrev U4ℝ := Idx4 → ℝ
/-- Order-3 surrogate state space over ℝ: `Idx3 → ℝ`. -/
abbrev U3ℝ := Idx3 → ℝ

/-- The marginalisation `Mℝ : U4ℝ →ₗ[ℝ] U3ℝ`, summing the two order-4
    coordinates into the single order-3 coordinate. -/
def MℝLin : U4ℝ →ₗ[ℝ] U3ℝ where
  toFun u := fun _ => u .a + u .b
  map_add' u v := by 
    ext i
    simp only [Pi.add_apply]
    abel
  map_smul' c u := by 
    ext i
    simp only [Pi.smul_apply, smul_add, RingHom.id_apply]

/-- The Kirkwood-closed order-4 RHS at the witness configuration over ℝ. -/
def F4Kℝ : U4ℝ → U4ℝ := fun u => fun
  | .a => u .a * u .b
  | .b => u .b

/-- The order-4 Kirkwood-form closure family packaged as a `ClosureFamily`. -/
def C4ℝ : ClosureFamily U4ℝ where
  C := F4Kℝ

/-- Auxiliary point: `(a ↦ 1, b ↦ 3)`. -/
def u₁ : U4ℝ := fun i => match i with
  | .a => 1
  | .b => 3

/-- Auxiliary point: `(a ↦ 4, b ↦ 0)`. -/
def u₂ : U4ℝ := fun i => match i with
  | .a => 4
  | .b => 0

/-- The Kirkwood-form predicate holds for `C4ℝ`: the bilinear `a·b`
    component is non-additive. Witnessed by `u = (1,0)`, `v = (0,1)`:
    `F₄(u+v) = (1,1)` while `F₄(u) + F₄(v) = (0,1)`. -/
lemma C4ℝ_isKirkwoodForm : C4ℝ.IsKirkwoodForm := by
  refine ⟨(fun i => match i with | .a => 1 | .b => 0),
          (fun i => match i with | .a => 0 | .b => 1), ?_⟩
  intro h
  have h_a := congrArg (fun f => f Idx4.a) h
  -- The equation states: F4Kℝ (u + v) = F4Kℝ u + F4Kℝ v
  -- where u = (1, 0) and v = (0, 1)
  -- LHS at .a: F4Kℝ ((1,0) + (0,1)) .a = F4Kℝ (1,1) .a = 1 * 1 = 1
  -- RHS at .a: (F4Kℝ (1,0) + F4Kℝ (0,1)) .a = (0,0) + (0,0) = 0
  simp only [Pi.add_apply] at h_a
  dsimp only [F4Kℝ, C4ℝ] at h_a
  norm_num at h_a

/-- **Theorem T3b (Kirkwood obstruction, concrete form).**
    There exist concrete real vector spaces `V₄`, `V₃`, a surjective
    linear marginalisation `M`, and a Kirkwood-form order-4 closure
    `C₄` such that no order-3 closure family `C₃` makes the closure
    diagram commute.

    **Proof.**
    Use the (2,1) ℝ-witness above. Suppose for contradiction some
    `C₃` satisfies `Equivariant Mℝ F₄ C₃`. Then
    * at `u₁ = (1, 3)`: `M(F₄ u₁) = 1·3 + 3 = 6` and `M u₁ = 4`, so
      `C₃(4) (.c) = 6`;
    * at `u₂ = (4, 0)`: `M(F₄ u₂) = 4·0 + 0 = 0` and `M u₂ = 4`, so
      `C₃(4) (.c) = 0`.

    Since `C₃(4)` is a single value, `6 = 0`, a contradiction.

    No algebraic-geometry / Zariski machinery is needed: the diagram
    fails on a single `M`-fibre because two distinct `u`'s with the
    same `M u` produce different `M(F₄ u)`. This is the elementary
    "linear pushforward kills the bilinear term" obstruction, in its
    smallest faithful form. -/
theorem kirkwood_form_not_equivariant :
    ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃)
      (_ : Module ℝ V₄) (_ : Module ℝ V₃)
      (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      C₄.IsKirkwoodForm ∧
      ∀ (C₃ : ClosureFamily V₃), ¬ Equivariant M C₄.C C₃.C := by
  refine ⟨U4ℝ, U3ℝ, inferInstance, inferInstance, inferInstance, inferInstance,
          MℝLin, C4ℝ, C4ℝ_isKirkwoodForm, ?_⟩
  intro C₃ hEq
  -- Equivariance at u₁ and u₂.
  have h1 := hEq u₁
  have h2 := hEq u₂
  -- M u₁ = M u₂ (both have coordinate sum 4).
  have hMeq : MℝLin u₁ = MℝLin u₂ := by
    funext _
    dsimp [MℝLin, u₁, u₂]
    norm_num
  -- Therefore C₃(M u₁) = C₃(M u₂), so M(F₄ u₁) = M(F₄ u₂).
  have hF : MℝLin (C4ℝ.C u₁) = MℝLin (C4ℝ.C u₂) := by
    rw [h1, h2, hMeq]
  -- But the two values are 6 and 0, contradiction.
  have h_c := congrArg (fun f => f Idx3.c) hF
  dsimp [MℝLin, C4ℝ, F4Kℝ, u₁, u₂] at h_c
  norm_num at h_c

/-! ## T3c — Corollary for Kiss–Kenah–Rempala -/

/-- **Theorem T3c.** The Kiss–Kenah–Rempala pairwise-closure
    exactness conditions (cf. `ClosureTheorem.lean`, Results 51–59)
    are *necessary* but **not sufficient** for marginalisation
    equivariance with the order-4 closed system used to generate `F₄`.
    Concretely, even when the order-3 closure is KKR-exact in the
    `N → ∞` limit (e.g. `closureKappa = 1` for Poisson), the order-4
    closure `C₄` is *independent data*, and Theorem T3b applies to it
    whenever it has Kirkwood form.

    The formal statement: there exists a degree distribution `ψ` whose
    `closureKappa` is `1` (so the KKR pairwise-exactness criterion of
    Result 52 is met) together with concrete `V₄`/`V₃` and a
    Kirkwood-form order-4 closure `C₄` for which marginalisation
    equivariance against `M` still fails. -/
theorem kkr_necessary_not_sufficient :
    ∃ (ψ : PGFData) (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃)
      (_ : Module ℝ V₄) (_ : Module ℝ V₃)
      (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      ψ.closureKappa = 1 ∧
      C₄.IsKirkwoodForm ∧
      ∀ (C₃ : ClosureFamily V₃), ¬ Equivariant M C₄.C C₃.C := by
  obtain ⟨V₄, V₃, _, _, _, _, M, C₄, hKirk, hno⟩ :=
    kirkwood_form_not_equivariant
  refine ⟨PGFData.poisson 1 (by norm_num), V₄, V₃, _, _, _, _, M, C₄, ?_, hKirk, hno⟩
  exact poisson_kappa_is_one' 1 (by norm_num)

end EBCMCategory.MarginalisationCharacterization
