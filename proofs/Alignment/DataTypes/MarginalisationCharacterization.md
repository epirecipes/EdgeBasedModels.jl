# DataTypes — group `MarginalisationCharacterization`

Blind-safe vocabulary for shadow authors: imports, data types (fields/constructors +
docstrings) and **opaque signatures plus docstrings** of the definitions the claims mention.
No theorem statements, proofs, definition bodies or instance bodies. Claim texts:
`Alignment/claims_blind.yaml`.

## (a) Imports and namespaces

```lean
import EBCMCategory.MarginalisationCharacterization
-- (imports EBCMCategory.MarginalisationFunctor, EBCMCategory.Obstructions,
--  EBCMCategory.ClosureTheorem, Mathlib.Tactic)
open EBCMCategory.Marginalisation
open EBCMCategory.MarginalisationCharacterization
open MarginalisationObstruction
```

* New declarations live in `namespace EBCMCategory.MarginalisationCharacterization`.
* Vector spaces here are **algebraic** ℝ-modules (`[AddCommGroup V] [Module ℝ V]`) and the
  marginalisation is a **linear map** `M : V₄ →ₗ[ℝ] V₃` (no topology).
* The flow vocabulary of `MarginalisationFunctor` (`IsFlow`, `IsSolution`, `UniqueFlow`) and
  the T2 vocabulary of `Obstructions` (`Idx4`, `Idx3`, `U4`, `U3`, `M_witness`, `F4_Kirkwood`,
  `F3_Kirkwood`) are available; see `DataTypes/MarginalisationFunctor.md`.

## (b) Data types

```lean
/-- An abstract closure family on a state space `V`. -/
structure ClosureFamily (V : Type _) where
  C : V → V
```

From `EBCMCategory.Obstructions` (namespace `MarginalisationObstruction`):

```lean
/-- Index type for the order-4 surrogate (a = C₄ SISI, b = C₄ SSSS). -/
inductive Idx4 | a | b      -- deriving DecidableEq, Repr
/-- Index type for the order-3 surrogate (c = P₃ SIS). -/
inductive Idx3 | c          -- deriving DecidableEq, Repr
```

From `EBCMCategory.EpiCategory` (root namespace; used for the Kiss–Kenah–Rempala claims):

```lean
/-- Abstract probability generating function data.
    A PGF ψ of a degree distribution is characterised by:
    * `mean` = ψ'(1): the mean degree κ
    * `secondFactorial` = ψ''(1): the second factorial moment
    * `mean_pos`: the mean degree is positive -/
structure PGFData where
  mean : ℚ
  secondFactorial : ℚ
  mean_pos : 0 < mean
  secondFactorial_nonneg : 0 ≤ secondFactorial
```

## (c) Operations under test (opaque signatures + docstrings)

| signature | docstring |
|---|---|
| `Equivariant {V₄ V₃ : Type _} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃] (M : V₄ →ₗ[ℝ] V₃) (F : V₄ → V₄) (G : V₃ → V₃) : Prop` | `Equivariant M F G` says that `M` intertwines vector fields `F` and `G`. |
| `ClosureFamily.IsLinear {V : Type _} [AddCommGroup V] [Module ℝ V] (C : ClosureFamily V) : Prop` | Marker: the closure is linear in the moment coordinates. |
| `ClosureFamily.IsKirkwoodForm {V : Type _} [Add V] (C : ClosureFamily V) : Prop` | Marker: the closure has the *multiplicative Kirkwood form* (product-of-monomials over product-of-monomials with at least one coordinate-index appearing with positive exponent in the numerator AND at least one strictly positive output component depending on at least two distinct input coordinates). The precise multi-index data is abstracted; the only hypothesis we use downstream is *existence of a strictly bilinear (or higher-degree) monomial entry* in `C` that does not collapse under any single linear pushforward. |
| `abbrev U4ℝ : Type` | Order-4 surrogate state space over ℝ: `Idx4 → ℝ`. |
| `abbrev U3ℝ : Type` | Order-3 surrogate state space over ℝ: `Idx3 → ℝ`. |
| `MℝLin : U4ℝ →ₗ[ℝ] U3ℝ` | The marginalisation `Mℝ : U4ℝ →ₗ[ℝ] U3ℝ`, summing the two order-4 coordinates into the single order-3 coordinate. |
| `F4Kℝ : U4ℝ → U4ℝ` | The Kirkwood-closed order-4 RHS at the witness configuration over ℝ. |
| `C4ℝ : ClosureFamily U4ℝ` | The order-4 Kirkwood-form closure family packaged as a `ClosureFamily`. |
| `u₁ : U4ℝ` | Auxiliary point: `(a ↦ 1, b ↦ 3)`. |
| `u₂ : U4ℝ` | Auxiliary point: `(a ↦ 4, b ↦ 0)`. |
| `PGFData.poisson (κ : ℚ) (hκ : 0 < κ) : PGFData` | The Poisson PGF with mean κ. Key property: ψ''(1) = κ². |
| `PGFData.closureKappa (ψ : PGFData) : ℚ` | The closure parameter κ for a PGF. κ = ψ''(1)·ψ(1) / (ψ'(1))² = secondFactorial / mean² (since ψ(1) = 1 for any proper PGF). This is the ratio of mean excess degree to mean degree. It is constant in θ iff the degree distribution is Poisson-type. |

Vocabulary used in the claim texts:

* "closure diagram commutes" / "marginalisation-equivariant": `Equivariant M F₄ F₃`.
* "Kirkwood-form closure": a `ClosureFamily` satisfying `IsKirkwoodForm` (the claim texts also
  describe the intended monomial-ratio shape `C(u)_i = ∏_j u_{α(i,j)}^{p(i,j)} / ∏_k u_{β(i,k)}^{q(i,k)}`).
* "KKR pairwise-exactness criterion": the text identifies it with `closureKappa = 1`.

## (d) Mathlib notions

* `LinearMap` (`→ₗ[ℝ]`), `LinearMap.ker`, `Function.Surjective`, `Module ℝ`, `AddCommGroup`.
* "Generic" linear maps: e.g. `∀ᶠ M in …` is not natural here; a faithful reading may quantify
  over all surjective `M` or over a dense/open set in `Matrix`-coordinates (`Matrix.toLin'`).
* Monomials: `Finsupp`/`MvPolynomial` (`MvPolynomial.monomial`) or explicit `∏ j, u (α j) ^ p j`
  with `Finset.prod`.
* Existential packaging of types with instances: `∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℝ V), …`.
