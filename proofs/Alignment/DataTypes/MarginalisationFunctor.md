# DataTypes — group `MarginalisationFunctor`

Blind-safe vocabulary for shadow authors: imports, data types (fields/constructors +
docstrings) and **opaque signatures plus docstrings** of the definitions the claims mention.
No theorem statements, proofs, definition bodies or instance bodies. Claim texts:
`Alignment/claims_blind.yaml`.

## (a) Imports and namespaces

```lean
import EBCMCategory.MarginalisationFunctor
-- (it imports Mathlib.Tactic, Mathlib.Analysis.Calculus.Deriv.Linear, Mathlib.Analysis.Calculus.Deriv.Comp)
open EBCMCategory.Marginalisation
```

* Declarations live in `namespace EBCMCategory.Marginalisation`.
* The flow notions are stated in a section with
  `variable {V : Type _} [NormedAddCommGroup V] [NormedSpace ℝ V]`, and the marginalisation
  results use two such spaces `V₄`, `V₃` and a **continuous linear** map `M : V₄ →L[ℝ] V₃`.
* Claims that mention "Theorem T2" refer to the module `EBCMCategory.Obstructions`
  (vocabulary in §(c′) below).

## (b) Data types

```lean
/-- Connected unlabelled subgraph shapes on 3 or 4 vertices that arise
    in the order-3/4 motif moment hierarchy. We do *not* formalise the
    underlying graphs — only the names. -/
inductive MotifShape where
  | P3 | C3
  | P4 | K13 | Paw | C4 | K4e | K4
  deriving DecidableEq, Repr, Fintype

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
```

## (c) Operations under test (opaque signatures + docstrings)

| signature | docstring |
|---|---|
| `MotifShape.order : MotifShape → ℕ` | The number of vertices of each shape. |
| `MotifShape.isOrder3 (s : MotifShape) : Prop` | Predicate: the shape is an order-3 motif. |
| `MotifShape.isOrder4 (s : MotifShape) : Prop` | Predicate: the shape is an order-4 motif. |
| `opaque stateClassCount : MotifShape → ℕ` | Opaque cardinality of the set of canonical state classes for a shape. |
| `abbrev V3 : Type` / `abbrev V4 : Type` | The state-space of order-k moment vectors lives in `α → ℝ` for `α = Order_k_Var`. We work with this representation throughout. |
| `IsFlow {V} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → V) (φ : V → ℝ → V) : Prop` | `IsFlow F φ` says that `φ : V → ℝ → V` is a (forward) flow of the vector field `F`: `φ v 0 = v` and `t ↦ φ v t` is differentiable with derivative `F (φ v t)` at every time `t`. |
| `IsSolution {V} [...] (F : V → V) (v₀ : V) (ψ : ℝ → V) : Prop` | A `Solution` of `F` starting at `v₀` is a curve through `v₀` whose derivative at every time is `F` of its current value. |
| `UniqueFlow {V} [...] (F : V → V) : Prop` | Uniqueness predicate for solutions of a vector field, abstracted as a hypothesis to avoid threading Picard–Lindelöf at this level of the theory. Holds for `C¹` (in particular polynomial) `F` by Mathlib's `ODE_solution_unique`. |

Notes: "every time `t`" in `IsFlow`/`IsSolution` ranges over all of `ℝ` (negative times
included). No marginalisation map `V4 → V3` and no CTMC/exact moment dynamics are defined.

## (c′) Vocabulary from `EBCMCategory.Obstructions` (for claims citing Theorem T2)

```lean
import EBCMCategory.Obstructions
-- namespace MarginalisationObstruction
/-- Index type for the order-4 surrogate (a = C₄ SISI, b = C₄ SSSS). -/
inductive Idx4 | a | b      -- deriving DecidableEq, Repr
/-- Index type for the order-3 surrogate (c = P₃ SIS). -/
inductive Idx3 | c          -- deriving DecidableEq, Repr
```

| signature | docstring |
|---|---|
| `abbrev U4 : Type` / `abbrev U3 : Type` | Order-4 state vector. / Order-3 state vector. (functions `Idx4 → ℚ`, `Idx3 → ℚ`) |
| `M_witness (u : U4) : U3` | The marginalisation `M : U4 → U3`, here `M(u)(c) = u(a) + u(b)`. |
| `F4_Kirkwood (u : U4) : U4` | The Kirkwood-closed order-4 RHS at the witness configuration. The bilinear `(a·b, b)` form is the characteristic shape of a pair-Kirkwood closure applied to a 5-vertex moment that decomposes as a product of a "pair" entry (`a`) and a "single" entry (`b`). |
| `F3_Kirkwood (v : U3) : U3` | The Kirkwood-closed order-3 RHS at the witness configuration. The quadratic-rational `c²/4` form is the analogous order-3 Kirkwood closure applied to the collapsed variable. |

## (d) Mathlib notions

* `ContinuousLinearMap` (`V₄ →L[ℝ] V₃`), `LinearMap` (`→ₗ[ℝ]`), `Function.Surjective`.
* `HasDerivAt`, `HasFDerivAt`, `ContinuousLinearMap.hasFDerivAt`, `HasFDerivAt.comp_hasDerivAt`,
  `HasDerivAt.unique` (reference only; checkers must be structural).
* ODE theory: `IsPicardLindelof`, `ODE_solution_unique` and its `…_of_mem_Icc`/local variants,
  `LipschitzWith`, `LipschitzOnWith`, `ContDiff ℝ 1`.
* Local-in-time solutions: `Set.Ioo (-δ) δ`, `HasDerivWithinAt`, `∀ᶠ t in nhds 0, …`.
