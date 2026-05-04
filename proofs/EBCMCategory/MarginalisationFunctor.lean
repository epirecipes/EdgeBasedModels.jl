import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Marginalisation as a Functor on Closed Moment Dynamics

This file formalises the categorical/dynamical question raised by the
NodeBasedModels.jl experiments:

> When does a linear marginalisation `M : V₄ → V₃` between subgraph-moment
> state spaces commute with closed dynamics `F₄`, `F₃` derived from a
> moment-closure prescription?

For the **exact** (unclosed) CTMC moments, one always has
`M · x₄_exact(t) = x₃_exact(t)` by definition of induced subgraphs.
For the **closed** dynamics (e.g., Kirkwood at order 4 vs order 3), the
diagram

       F₄
   V₄ ────► V₄
   │         │
 M │         │ M
   ▼         ▼
   V₃ ────► V₃
       F₃

need not commute, and we prove (Theorem T1) the precise dynamical
characterisation:

  *Trajectory-level marginalisation* `M ∘ φ₄(·,t) = φ₃(M·, t)` for all
  `(u, t)` is **equivalent** to *infinitesimal* marginalisation
  `M ∘ F₄ = F₃ ∘ M`.

This file provides the abstract scaffolding (motif shapes, state spaces,
linear marginalisation, closed systems, flow predicate) and the
equivariance theorem T1.

The negative result (T2: explicit Kirkwood obstruction) lives in
`Obstructions.lean`. The structural impossibility result (T3) lives in
`MarginalisationCharacterization.lean`.

| Result | Statement                                                    |
|--------|---------------------------------------------------------------|
| M1     | `IsFlow` predicate                                            |
| M2     | (←) infinitesimal commutation gives trajectory commutation     |
| M3     | (→) trajectory commutation gives infinitesimal commutation     |
| M4     | T1: full equivalence                                          |
-/

namespace EBCMCategory.Marginalisation

/-! ## Motif shapes (opaque) -/

/-- Connected unlabelled subgraph shapes on 3 or 4 vertices that arise
    in the order-3/4 motif moment hierarchy. We do *not* formalise the
    underlying graphs — only the names. -/
inductive MotifShape where
  | P3 | C3
  | P4 | K13 | Paw | C4 | K4e | K4
  deriving DecidableEq, Repr, Fintype

/-- The number of vertices of each shape. -/
def MotifShape.order : MotifShape → ℕ
  | .P3 | .C3 => 3
  | _         => 4

/-- Predicate: the shape is an order-3 motif. -/
def MotifShape.isOrder3 (s : MotifShape) : Prop := s.order = 3
/-- Predicate: the shape is an order-4 motif. -/
def MotifShape.isOrder4 (s : MotifShape) : Prop := s.order = 4

/-! ## State classes (opaque counts)

For each shape `s`, the number of orbits of `{S,I}^V(s)` under `Aut(s)`
is some finite natural number. We keep it abstract: nothing in the
present file needs the actual values. -/

/-- Opaque cardinality of the set of canonical state classes for a shape. -/
opaque stateClassCount : MotifShape → ℕ := fun _ => 1

/-! ## Order-k variable types -/

/-- An order-3 motif variable: a shape (P₃ or C₃) plus a state class. -/
structure Order3Var where
  shape : MotifShape
  is3   : shape.isOrder3
  cls   : Fin (stateClassCount shape)

/-- An order-4 motif variable: a shape (P₄, K₁,₃, Paw, C₄, K₄−e, K₄) plus
    a state class. -/
structure Order4Var where
  shape : MotifShape
  is4   : shape.isOrder4
  cls   : Fin (stateClassCount shape)

/-- The state-space of order-k moment vectors lives in `α → ℝ` for
    `α = Order_k_Var`. We work with this representation throughout. -/
abbrev V3 := Order3Var → ℝ
abbrev V4 := Order4Var → ℝ

/-! ## Closed systems -/

/-- A *closed dynamical system* on a state space `V`: a vector field
    `F : V → V`. The exact (unclosed) RHS that `F` is meant to
    approximate is recorded for documentation but not required by the
    abstract theorems below. -/
structure ClosedSystem (V : Type _) where
  /-- The closed RHS used to integrate the dynamics. -/
  F       : V → V
  /-- The exact RHS this `F` approximates (closure recovers `F_exact`
      when the closure is exact at the given state). -/
  F_exact : V → V

/-! ## Abstract flows -/

section Flow

variable {V : Type _} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `IsFlow F φ` says that `φ : V → ℝ → V` is a (forward) flow of the
    vector field `F`: `φ v 0 = v` and `t ↦ φ v t` is differentiable
    with derivative `F (φ v t)` at every time `t`. -/
def IsFlow (F : V → V) (φ : V → ℝ → V) : Prop :=
  (∀ v, φ v 0 = v) ∧ (∀ v t, HasDerivAt (φ v) (F (φ v t)) t)

/-- A `Solution` of `F` starting at `v₀` is a curve through `v₀` whose
    derivative at every time is `F` of its current value. -/
def IsSolution (F : V → V) (v₀ : V) (ψ : ℝ → V) : Prop :=
  ψ 0 = v₀ ∧ ∀ t, HasDerivAt ψ (F (ψ t)) t

/-- Uniqueness predicate for solutions of a vector field, abstracted as a
    hypothesis to avoid threading Picard–Lindelöf at this level of the
    theory. Holds for `C¹` (in particular polynomial) `F` by
    Mathlib's `ODE_solution_unique`. -/
def UniqueFlow (F : V → V) : Prop :=
  ∀ v₀ ψ₁ ψ₂, IsSolution F v₀ ψ₁ → IsSolution F v₀ ψ₂ → ψ₁ = ψ₂

end Flow

/-! ## The equivariance theorem (T1) -/

section Equivariance

variable {V₄ V₃ : Type _}
  [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
  [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]

/-- **Result M1.** Pushing a flow of `F₄` through a continuous linear
    `M` gives the flow of `F₃` whenever the RHS commute, *provided* a
    flow of `F₃` is already known to exist. -/
theorem pushforward_isSolution
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    (h_comm : ∀ u, M (F₄ u) = F₃ (M u))
    {φ₄ : V₄ → ℝ → V₄} (h₄ : IsFlow F₄ φ₄) (u : V₄) :
    IsSolution F₃ (M u) (fun t => M (φ₄ u t)) := by
  refine ⟨by simp [h₄.1 u], fun t => ?_⟩
  have hφ : HasDerivAt (φ₄ u) (F₄ (φ₄ u t)) t := h₄.2 u t
  have hM : HasDerivAt (fun t => M (φ₄ u t)) (M (F₄ (φ₄ u t))) t :=
    M.hasFDerivAt.comp_hasDerivAt t hφ
  -- rewrite the derivative using the commutation hypothesis
  simpa [h_comm] using hM

/-- **Result M2 (→).** Infinitesimal commutation `M ∘ F₄ = F₃ ∘ M` and
    a unique flow for `F₃` imply trajectory commutation. -/
theorem traj_commute_of_rhs_commute
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃}
    (h₄ : IsFlow F₄ φ₄) (h₃ : IsFlow F₃ φ₃)
    (uniq₃ : UniqueFlow F₃)
    (h_comm : ∀ u, M (F₄ u) = F₃ (M u)) :
    ∀ u t, M (φ₄ u t) = φ₃ (M u) t := by
  intro u
  -- both `t ↦ M (φ₄ u t)` and `t ↦ φ₃ (M u) t` are solutions starting
  -- at `M u`; uniqueness forces them to coincide.
  have h_left  : IsSolution F₃ (M u) (fun t => M (φ₄ u t)) :=
    pushforward_isSolution M F₄ F₃ h_comm h₄ u
  have h_right : IsSolution F₃ (M u) (fun t => φ₃ (M u) t) :=
    ⟨by simp [h₃.1], fun t => h₃.2 (M u) t⟩
  have := uniq₃ (M u) _ _ h_left h_right
  intro t
  exact congrArg (fun f => f t) this

/-- **Result M3 (←).** Trajectory commutation implies infinitesimal
    commutation, by differentiating at `t = 0`. -/
theorem rhs_commute_of_traj_commute
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃}
    (h₄ : IsFlow F₄ φ₄) (h₃ : IsFlow F₃ φ₃)
    (h_traj : ∀ u t, M (φ₄ u t) = φ₃ (M u) t) :
    ∀ u, M (F₄ u) = F₃ (M u) := by
  intro u
  -- `d/dt M (φ₄ u t) |_{t=0}` computed two ways.
  have h_left : HasDerivAt (fun t => M (φ₄ u t)) (M (F₄ u)) 0 := by
    have hφ : HasDerivAt (φ₄ u) (F₄ (φ₄ u 0)) 0 := h₄.2 u 0
    rw [h₄.1 u] at hφ
    exact M.hasFDerivAt.comp_hasDerivAt 0 hφ
  have h_right : HasDerivAt (fun t => M (φ₄ u t)) (F₃ (M u)) 0 := by
    have hψ : HasDerivAt (φ₃ (M u)) (F₃ (φ₃ (M u) 0)) 0 := h₃.2 (M u) 0
    rw [h₃.1 (M u)] at hψ
    -- transport via the trajectory equality
    have hext : (fun t => M (φ₄ u t)) = (fun t => φ₃ (M u) t) :=
      funext (fun t => h_traj u t)
    rw [hext]
    exact hψ
  exact h_left.unique h_right

/-- **Result M4 — Theorem T1 (Equivariance).** The diagram

           F₄
       V₄ ────► V₄
       │         │
     M │         │ M
       ▼         ▼
       V₃ ────► V₃
           F₃

    commutes infinitesimally **iff** it commutes along all trajectories
    (under the standing flow / uniqueness hypotheses).

    The intended use is contrapositive: **failure** of trajectory
    marginalisation `M · u₄(t) = u₃(t)` is detectable from the algebraic
    failure of `M ∘ F₄ = F₃ ∘ M`, which is checked by Theorem T2. -/
theorem dynamic_marginalisation_iff_equivariance
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
    {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃}
    (h₄ : IsFlow F₄ φ₄) (h₃ : IsFlow F₃ φ₃)
    (uniq₃ : UniqueFlow F₃) :
    (∀ u, M (F₄ u) = F₃ (M u)) ↔ (∀ u t, M (φ₄ u t) = φ₃ (M u) t) :=
  ⟨traj_commute_of_rhs_commute M F₄ F₃ h₄ h₃ uniq₃,
   rhs_commute_of_traj_commute M F₄ F₃ h₄ h₃⟩

end Equivariance

end EBCMCategory.Marginalisation
