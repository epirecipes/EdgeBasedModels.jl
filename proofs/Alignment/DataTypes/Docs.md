# DataTypes — group Docs (blind-safe)

Vocabulary for claims taken from `proofs/categorical_foundations.md`,
`proofs/EBCMCategory/MARGINALISATION_SPEC.md`, the README "Lean proofs" section and
`vignettes/index.qmd`. Signatures are opaque: no definition bodies, instance bodies or
theorem statements. Docstrings are quoted verbatim.

## (a) Imports

```lean
import EBCMCategory   -- root module: imports every EBCMCategory.* module
```

Namespaces: root (EpiCategory, CoarseGrain, GaloisPair, Hierarchy, Obstructions,
DynamicLimits, VolzMeyersEquations, SEIREquations), `InvariantRegion`,
`MarginalisationObstruction`, `EBCMCategory.Marginalisation`,
`EBCMCategory.MarginalisationCharacterization`, `EBCMCategory.MarginalisationDynamicalGap`.

## (b) Shared data types

### Model-level records (see `DataTypes/EpiCategory.md` for full field tables)

* `PGFData` — fields `mean : ℚ`, `secondFactorial : ℚ`, `mean_pos : 0 < mean`,
  `secondFactorial_nonneg : 0 ≤ secondFactorial`. Docstring: "Abstract probability
  generating function data. A PGF ψ of a degree distribution is characterised by:
  `mean` = ψ'(1): the mean degree κ; `secondFactorial` = ψ''(1): the second factorial
  moment; `mean_pos`: the mean degree is positive".
* `SIRParams` — fields `β γ : ℚ`, `β_pos`, `γ_pos`.
* `EpiModel` — fields `dim : ℕ`, `R0 : ℚ`; `Preorder EpiModel` instance = refinement (`≤`).
* `NetworkType`, `TransitionType`, `InitCondType`, `SystemType` — see
  `DataTypes/Obstructions.md`.
* `VMState`, `VMParams` — see `DataTypes/VolzMeyersEquations.md`.
* `InvariantRegion.EBCMParams`, `SEIRState`, `SEIRParams` — see
  `DataTypes/InvariantRegion.md` and `DataTypes/SEIREquations.md` (other groups).

### Marginalisation (namespace `EBCMCategory.Marginalisation`)

* `inductive MotifShape | P3 | C3 | P4 | K13 | Paw | C4 | K4e | K4`
  (deriving `DecidableEq, Repr, Fintype`) — "Connected unlabelled subgraph shapes on 3 or
  4 vertices that arise in the order-3/4 motif moment hierarchy. We do *not* formalise the
  underlying graphs — only the names."
* `structure Order3Var` — "An order-3 motif variable: a shape (P₃ or C₃) plus a state
  class." Fields: `shape : MotifShape`, `is3 : shape.isOrder3`,
  `cls : Fin (stateClassCount shape)`.
* `structure Order4Var` — "An order-4 motif variable: a shape (P₄, K₁,₃, Paw, C₄, K₄−e,
  K₄) plus a state class." Fields: `shape : MotifShape`, `is4 : shape.isOrder4`,
  `cls : Fin (stateClassCount shape)`.
* `abbrev V3 := Order3Var → ℝ`, `abbrev V4 := Order4Var → ℝ` — "The state-space of
  order-k moment vectors lives in `α → ℝ` for `α = Order_k_Var`. We work with this
  representation throughout."
* `structure ClosedSystem (V : Type _)` — "A *closed dynamical system* on a state space
  `V`: a vector field `F : V → V`. The exact (unclosed) RHS that `F` is meant to
  approximate is recorded for documentation but not required by the abstract theorems
  below." Fields: `F : V → V` ("The closed RHS used to integrate the dynamics."),
  `F_exact : V → V` ("The exact RHS this `F` approximates (closure recovers `F_exact`
  when the closure is exact at the given state).").

### Closure families (namespace `EBCMCategory.MarginalisationCharacterization`)

* `structure ClosureFamily (V : Type _)` — "An abstract closure family on a state space
  `V`." Field: `C : V → V`.
* `abbrev U4ℝ := Idx4 → ℝ` — "Order-4 surrogate state space over ℝ: `Idx4 → ℝ`."
* `abbrev U3ℝ := Idx3 → ℝ` — "Order-3 surrogate state space over ℝ: `Idx3 → ℝ`."
  (`Idx4 | a | b`, `Idx3 | c` are from `MarginalisationObstruction`; `Fintype`
  instances for them are provided in `MarginalisationDynamicalGap`, giving the Pi norm.)

### T2 surrogate over ℚ (namespace `MarginalisationObstruction`)

`Idx4`, `Idx3`, `U4 := Idx4 → ℚ`, `U3 := Idx3 → ℚ` — see `DataTypes/Obstructions.md`.

## (c) Operations under test (opaque signatures)

### Model level

| name | signature | docstring |
|---|---|---|
| `coarseGrain` | `EpiModel → EpiModel` | The coarse-graining map F on abstract models. Projects any model to a 3-dimensional node model, preserving R₀. |
| `poissonLift` | `EpiModel → EpiModel` | The Poisson lift G: Node → Edge. Embeds a node model into the canonical 4D edge model with Poisson degree distribution. |
| `nodeModel` | `SIRParams → ℚ → EpiModel` | A node-based SIR model: 3 state variables (S, I, R). |
| `edgeModel` | `SIRParams → PGFData → EpiModel` | An edge-based SIR model: 4 state variables (θ, φ_I, R + algebraic φ_S). |
| `PGFData.poisson` | `(κ : ℚ) → 0 < κ → PGFData` | The Poisson PGF with mean κ. Key property: ψ''(1) = κ². |
| `PGFData.excessDegree` | `PGFData → ℚ` | The excess degree ratio: ψ''(1)/ψ'(1). |
| `PGFData.variance` | `PGFData → ℚ` | Degree variance: Var(k) = ψ''(1) + ψ'(1) - (ψ'(1))². |
| `PGFData.dispersionIndex` | `PGFData → ℚ` | Index of dispersion: σ²/κ. Equals 1 iff Poisson. |
| `PGFData.closureKappa` | `PGFData → ℚ` | The closure parameter κ for a PGF. κ = ψ''(1)·ψ(1) / (ψ'(1))² = secondFactorial / mean² (since ψ(1) = 1 for any proper PGF). This is the ratio of mean excess degree to mean degree. It is constant in θ iff the degree distribution is Poisson-type. |
| `SIRParams.transmissibility` | `SIRParams → ℚ` | Transmissibility across a single edge: T = β/(β+γ). |
| `standardEbcmValid`, `ebcmExists`, `systemRequired`, `extensionDim` | see `DataTypes/Obstructions.md` | |
| `DynamicEBCM.*` | see `DataTypes/DynamicLimits.md` | |
| `VMState.*`, `staticParams`, `vmInitialState` | see `DataTypes/VolzMeyersEquations.md` | |

### Marginalisation (`EBCMCategory.Marginalisation`)

| name | signature | docstring |
|---|---|---|
| `MotifShape.order` | `MotifShape → ℕ` | The number of vertices of each shape. |
| `MotifShape.isOrder3` / `isOrder4` | `MotifShape → Prop` | Predicate: the shape is an order-3 (resp. order-4) motif. |
| `stateClassCount` (opaque) | `MotifShape → ℕ` | Opaque cardinality of the set of canonical state classes for a shape. |
| `IsFlow` | `{V} [NormedAddCommGroup V] [NormedSpace ℝ V] → (F : V → V) → (φ : V → ℝ → V) → Prop` | `IsFlow F φ` says that `φ : V → ℝ → V` is a (forward) flow of the vector field `F`: `φ v 0 = v` and `t ↦ φ v t` is differentiable with derivative `F (φ v t)` at every time `t`. |
| `IsSolution` | `{V} [NormedAddCommGroup V] [NormedSpace ℝ V] → (F : V → V) → (v₀ : V) → (ψ : ℝ → V) → Prop` | A `Solution` of `F` starting at `v₀` is a curve through `v₀` whose derivative at every time is `F` of its current value. |
| `UniqueFlow` | `{V} [NormedAddCommGroup V] [NormedSpace ℝ V] → (F : V → V) → Prop` | Uniqueness predicate for solutions of a vector field, abstracted as a hypothesis to avoid threading Picard–Lindelöf at this level of the theory. Holds for `C¹` (in particular polynomial) `F` by Mathlib's `ODE_solution_unique`. |

### Closure families (`EBCMCategory.MarginalisationCharacterization`)

| name | signature | docstring |
|---|---|---|
| `Equivariant` | `{V₄ V₃} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃] → (M : V₄ →ₗ[ℝ] V₃) → (F : V₄ → V₄) → (G : V₃ → V₃) → Prop` | `Equivariant M F G` says that `M` intertwines vector fields `F` and `G`. |
| `ClosureFamily.IsLinear` | `{V} [AddCommGroup V] [Module ℝ V] → ClosureFamily V → Prop` | Marker: the closure is linear in the moment coordinates. |
| `ClosureFamily.IsKirkwoodForm` | `{V} [Add V] → ClosureFamily V → Prop` | Marker: the closure has the *multiplicative Kirkwood form* (product-of-monomials over product-of-monomials with at least one coordinate-index appearing with positive exponent in the numerator AND at least one strictly positive output component depending on at least two distinct input coordinates). The precise multi-index data is abstracted; the only hypothesis we use downstream is *existence of a strictly bilinear (or higher-degree) monomial entry* in `C` that does not collapse under any single linear pushforward. |
| `MℝLin` | `U4ℝ →ₗ[ℝ] U3ℝ` | The marginalisation `Mℝ : U4ℝ →ₗ[ℝ] U3ℝ`, summing the two order-4 coordinates into the single order-3 coordinate. |
| `F4Kℝ` | `U4ℝ → U4ℝ` | The Kirkwood-closed order-4 RHS at the witness configuration over ℝ. |
| `C4ℝ` | `ClosureFamily U4ℝ` | The order-4 Kirkwood-form closure family packaged as a `ClosureFamily`. |
| `u₁` | `U4ℝ` | Auxiliary point: `(a ↦ 1, b ↦ 3)`. |
| `u₂` | `U4ℝ` | Auxiliary point: `(a ↦ 4, b ↦ 0)`. |

### Dynamical gap (`EBCMCategory.MarginalisationDynamicalGap`)

| name | signature | docstring |
|---|---|---|
| `algebraicGap` | `{V₄ V₃} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃] [NormedSpace ℝ V₃] → (M : V₄ →L[ℝ] V₃) → (F₄ : V₄ → V₄) → (F₃ : V₃ → V₃) → (u : V₄) → V₃` | The algebraic gap `M(F₄ u) − F₃(M u)` is the value of the first-order divergence rate between any marginalised m=4 trajectory and any m=3 trajectory starting from the same image point `M u`. Established by T5 below. |
| `trajectoryGap` (noncomputable) | same context `→ (M : V₄ →L[ℝ] V₃) → (φ₄ : V₄ → ℝ → V₄) → (φ₃ : V₃ → ℝ → V₃) → (u : V₄) → (t : ℝ) → V₃` | The trajectory deviation at time `t` between the marginalised m=4 flow and the m=3 flow starting at the same image point `M u`. |
| `F3Kℝ` (noncomputable) | `U3ℝ → U3ℝ` | The order-3 Kirkwood-form RHS: `v(c)²/4`. |
| `MℝLinCLM` (noncomputable) | `U4ℝ →L[ℝ] U3ℝ` | `MℝLin` promoted to a continuous linear map. Continuity holds since `U4ℝ = Idx4 → ℝ` is finite-dimensional: each output component `fun u => u .a + u .b` is continuous by pointwise evaluation. |

### T2 surrogate over ℚ (`MarginalisationObstruction`)

`M_witness : U4 → U3`, `F4_Kirkwood : U4 → U4`, `F3_Kirkwood : U3 → U3` — docstrings in
`DataTypes/Obstructions.md`.

## (d) Mathlib notions

* Category theory: `CategoryTheory.Category`, `CategoryTheory.Functor`,
  `CategoryTheory.Functor.Faithful`, `CategoryTheory.Adjunction`, `GaloisConnection`,
  `Preorder.smallCategory`; `Monotone`, `Antitone`, `Function.Injective`.
* Linear algebra / analysis: `LinearMap` (`→ₗ[ℝ]`), `ContinuousLinearMap` (`→L[ℝ]`),
  `HasDerivAt`, `HasFDerivAt`, `deriv`, `Asymptotics.IsLittleO`, `‖·‖` (Pi sup norm),
  `Filter.Tendsto`, `nhds`, `Filter.atTop`.
* ODE theory: `IsPicardLindelof`, `ODE_solution_unique` (local existence/uniqueness).
* PGFs read literally: `PMF ℕ`, `HasSum`/`tsum`, `Polynomial.eval`, `iteratedDeriv`,
  `Real.exp`, `ProbabilityTheory.variance`.
