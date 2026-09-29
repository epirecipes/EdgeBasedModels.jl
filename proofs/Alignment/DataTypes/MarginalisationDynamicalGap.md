# DataTypes — group `MarginalisationDynamicalGap`

Blind-safe vocabulary for shadow authors: imports, data types and **opaque signatures plus
docstrings** of the definitions the claims mention. No theorem statements, proofs,
definition bodies or instance bodies. Claim texts: `Alignment/claims_blind.yaml`.

## (a) Imports and namespaces

```lean
import EBCMCategory.MarginalisationDynamicalGap
-- (imports EBCMCategory.MarginalisationCharacterization, Mathlib.Tactic)
open EBCMCategory.Marginalisation
open EBCMCategory.MarginalisationCharacterization
open MarginalisationObstruction
```

* New declarations live in `namespace EBCMCategory.MarginalisationDynamicalGap`.
* The dynamical-gap definitions use a section with
  `variable {V₄ V₃ : Type _} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]`
  and a **continuous linear** `M : V₄ →L[ℝ] V₃`.
* This module declares `Fintype` instances for `Idx4` and `Idx3` (so `U4ℝ = Idx4 → ℝ` and
  `U3ℝ = Idx3 → ℝ` carry the sup norm and are `NormedSpace ℝ`); instance bodies omitted.
* All vocabulary of `DataTypes/MarginalisationFunctor.md` (`IsFlow`, `IsSolution`,
  `UniqueFlow`, T2 objects) and `DataTypes/MarginalisationCharacterization.md`
  (`Equivariant`, `ClosureFamily`, `IsKirkwoodForm`, `U4ℝ`, `U3ℝ`, `MℝLin`, `F4Kℝ`, `C4ℝ`,
  `u₁`, `u₂`) is available.

## (b) Data types

No new structures. `ClosureFamily.mk F` packages a map `F : V → V` as a `ClosureFamily`.

## (c) Operations under test (opaque signatures + docstrings)

| signature | docstring |
|---|---|
| `algebraicGap (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (u : V₄) : V₃` | The algebraic gap `M(F₄ u) − F₃(M u)` is the value of the first-order divergence rate between any marginalised m=4 trajectory and any m=3 trajectory starting from the same image point `M u`. Established by T5 below. |
| `trajectoryGap (M : V₄ →L[ℝ] V₃) (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃) (u : V₄) (t : ℝ) : V₃` | The trajectory deviation at time `t` between the marginalised m=4 flow and the m=3 flow starting at the same image point `M u`. |
| `F3Kℝ : U3ℝ → U3ℝ` | The order-3 Kirkwood-form RHS: `v(c)²/4`. |
| `MℝLinCLM : U4ℝ →L[ℝ] U3ℝ` | `MℝLin` promoted to a continuous linear map. Continuity holds since `U4ℝ = Idx4 → ℝ` is finite-dimensional: each output component `fun u => u .a + u .b` is continuous by pointwise evaluation. |

(`algebraicGap` and `trajectoryGap` carry the implicit section arguments
`{V₄ V₃ : Type _}` and the four normed-space instances.)

Vocabulary used in the claim texts:

* "flow of F": `IsFlow F φ` (global in time: all `t : ℝ`).
* "first-order divergence rate at t = 0" / "`= 2t · ê_c + o(t)`": `HasDerivAt (trajectoryGap …) g 0`
  or an explicit `Asymptotics.IsLittleO` statement.
* "IC u₀": a point `u₀ : U4ℝ`; "m=4 / m=3 chain": order-4 / order-3 closed RHS.

## (d) Mathlib notions

* `HasDerivAt`, `HasDerivAt.sub`, `HasDerivAt.isLittleO`, `Asymptotics.IsLittleO`
  (`=o[nhds 0]`), `Metric.eventually_nhds_iff`, `norm_smul`, `norm_sub_norm_le`.
* `Filter.Eventually` over `nhdsWithin 0 (Set.Ioi 0)` for "for all sufficiently small t > 0".
* `ContinuousLinearMap`, `Pi` normed spaces over a `Fintype` index.
* Local solutions (if global flows are not intended): `HasDerivWithinAt` on `Set.Ioo (-δ) δ`,
  `IsPicardLindelof`.
