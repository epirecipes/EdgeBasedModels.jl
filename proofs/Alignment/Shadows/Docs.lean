import Alignment.Registry
import EBCMCategory.EpiCategory
import EBCMCategory.CoarseGrain
import EBCMCategory.GaloisPair
import EBCMCategory.Hierarchy
import EBCMCategory.Obstructions
import EBCMCategory.DynamicLimits
import EBCMCategory.VolzMeyersEquations
import EBCMCategory.MarginalisationFunctor
import EBCMCategory.MarginalisationCharacterization
import EBCMCategory.MarginalisationDynamicalGap

/-!
# Blind shadow sets for group `Docs`

Claims taken from `proofs/categorical_foundations.md` (`Docs.cf.*`),
`proofs/EBCMCategory/MARGINALISATION_SPEC.md` (`Docs.ms.*`) and the README "Lean proofs"
section (`Docs.readme.*`).

Written blind: the author read only `SA-PASS_SKILL.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/Docs.md`, the `claims_blind.yaml`
entries of these ids, the cited `.md` passages, and `#check` signatures / docstrings of the data
types and operations listed in `DataTypes/Docs.md`. No `.lean` file of the trusted library, no
theorem statement and no definition body was consulted.

The imports list the individual `EBCMCategory.*` modules (instead of the root `EBCMCategory`)
only to obtain the vocabulary of `DataTypes/Docs.md`.

Vocabulary conventions used below (from the docstrings in `DataTypes/Docs.md`):
* F = `coarseGrain`, G = `poissonLift` (on the abstract `EpiModel`s with fields `dim`, `R0`).
* A node-based (object of **Node**) model is `nodeModel p κ` (`κ` = mean degree, binder name
  `κ`); an edge-based (object of **Edge**) model is `edgeModel p ψ`. By the docstrings a node
  model is "3-dimensional" and an edge model is "4D"; where the text says "on Node"/"on Edge" we
  give both the constructor reading and the dimension reading.
* ψ'(1) = `ψ.mean` (= κ), ψ''(1) = `ψ.secondFactorial`, Var(degree) = `PGFData.variance ψ`
  (docstring: "Degree variance"), "Poisson" = `PGFData.poisson κ hκ`.

Re-authored blind (second pass, from the current claim texts and the full cited sections of
`categorical_foundations.md` and `MARGINALISATION_SPEC.md`): the blocks after the namespace
`Alignment.Shadows.Docs.Shared2` near the end of the file. Not formalised in that pass (the text
describes categorical notions that are not defined, the proof status, or the types used by the
formal statements): `cf.edgeCategory`, `cf.edgeTreeFunctor`, `cf.thm3_3`, `ms.T1-proofStatus`,
`ms.T3-proofStatus`, `ms.T5-empiricalBridge`, `ms.marginalisationLinearMap`, `ms.realVsRational`.
-/

universe u v

namespace Alignment.Shadows.Docs.cf_cor4_2_FG

/-! ### `Docs.cf.cor4_2-FG`

Text: "F ∘ G = id_Node (coarse-graining the Poisson lift recovers the original)" -/

-- AMBIGUITY: "id_Node" -- the objects of Node read as (S1) the node models `nodeModel p κ`
-- and (S2) the 3-dimensional models (coarseGrain docstring: "3-dimensional node model").

@[sa_reference "Docs.cf.cor4_2-FG"]
def T : Prop :=
  (∀ (p : SIRParams) (κ : ℚ), coarseGrain (poissonLift (nodeModel p κ)) = nodeModel p κ) ∧
  (∀ N : EpiModel, N.dim = 3 → coarseGrain (poissonLift N) = N)

/-- S1: F ∘ G fixes every node-based model. -/
@[sa_shadow "Docs.cf.cor4_2-FG" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ), coarseGrain (poissonLift (nodeModel p κ)) = nodeModel p κ

/-- S2: F ∘ G fixes every 3-dimensional (node-level) model. -/
@[sa_shadow "Docs.cf.cor4_2-FG" 2]
def S2 : Prop := ∀ N : EpiModel, N.dim = 3 → coarseGrain (poissonLift N) = N

@[sa_ref_forward "Docs.cf.cor4_2-FG" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.cor4_2-FG" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Docs.cf.cor4_2-FG"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Docs.cf_cor4_2_FG

namespace Alignment.Shadows.Docs.cf_cor4_2_GFG

/-! ### `Docs.cf.cor4_2-GFG`

Text: "G ∘ F ∘ G = G (the connection is idempotent)" -/

-- AMBIGUITY: G is "Node → Edge" in §4.1 but the Galois connection of Theorem 4.1 is "on the
-- preorder of epidemic models", so the identity is read (S1) on all models, and restricted to
-- Node as (S2) node models `nodeModel p κ` and (S3) 3-dimensional models. "=" is read as
-- equality (not preorder-equivalence).

@[sa_reference "Docs.cf.cor4_2-GFG"]
def T : Prop :=
  (∀ N : EpiModel, poissonLift (coarseGrain (poissonLift N)) = poissonLift N) ∧
  (∀ (p : SIRParams) (κ : ℚ),
      poissonLift (coarseGrain (poissonLift (nodeModel p κ))) = poissonLift (nodeModel p κ)) ∧
  (∀ N : EpiModel, N.dim = 3 → poissonLift (coarseGrain (poissonLift N)) = poissonLift N)

/-- S1: G ∘ F ∘ G = G on every model. -/
@[sa_shadow "Docs.cf.cor4_2-GFG" 1]
def S1 : Prop := ∀ N : EpiModel, poissonLift (coarseGrain (poissonLift N)) = poissonLift N

/-- S2: G ∘ F ∘ G = G on node-based models. -/
@[sa_shadow "Docs.cf.cor4_2-GFG" 2]
def S2 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ),
    poissonLift (coarseGrain (poissonLift (nodeModel p κ))) = poissonLift (nodeModel p κ)

/-- S3: G ∘ F ∘ G = G on 3-dimensional models. -/
@[sa_shadow "Docs.cf.cor4_2-GFG" 3]
def S3 : Prop :=
  ∀ N : EpiModel, N.dim = 3 → poissonLift (coarseGrain (poissonLift N)) = poissonLift N

@[sa_ref_forward "Docs.cf.cor4_2-GFG" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.cor4_2-GFG" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.cf.cor4_2-GFG" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Docs.cf.cor4_2-GFG"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Docs.cf_cor4_2_GFG

namespace Alignment.Shadows.Docs.cf_cor4_2_FGF

/-! ### `Docs.cf.cor4_2-FGF`

Text: "F ∘ G ∘ F = F (the connection is idempotent)" -/

-- AMBIGUITY: as for GFG -- (S1) on all models (Theorem 4.1 context), restricted to Edge as
-- (S2) edge models `edgeModel p ψ` and (S3) 4-dimensional models.

@[sa_reference "Docs.cf.cor4_2-FGF"]
def T : Prop :=
  (∀ E : EpiModel, coarseGrain (poissonLift (coarseGrain E)) = coarseGrain E) ∧
  (∀ (p : SIRParams) (ψ : PGFData),
      coarseGrain (poissonLift (coarseGrain (edgeModel p ψ))) = coarseGrain (edgeModel p ψ)) ∧
  (∀ E : EpiModel, E.dim = 4 → coarseGrain (poissonLift (coarseGrain E)) = coarseGrain E)

/-- S1: F ∘ G ∘ F = F on every model. -/
@[sa_shadow "Docs.cf.cor4_2-FGF" 1]
def S1 : Prop := ∀ E : EpiModel, coarseGrain (poissonLift (coarseGrain E)) = coarseGrain E

/-- S2: F ∘ G ∘ F = F on edge-based models. -/
@[sa_shadow "Docs.cf.cor4_2-FGF" 2]
def S2 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData),
    coarseGrain (poissonLift (coarseGrain (edgeModel p ψ))) = coarseGrain (edgeModel p ψ)

/-- S3: F ∘ G ∘ F = F on 4-dimensional models. -/
@[sa_shadow "Docs.cf.cor4_2-FGF" 3]
def S3 : Prop :=
  ∀ E : EpiModel, E.dim = 4 → coarseGrain (poissonLift (coarseGrain E)) = coarseGrain E

@[sa_ref_forward "Docs.cf.cor4_2-FGF" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.cor4_2-FGF" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.cf.cor4_2-FGF" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Docs.cf.cor4_2-FGF"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Docs.cf_cor4_2_FGF

namespace Alignment.Shadows.Docs.cf_localisedObstruction

/-! ### `Docs.cf.localisedObstruction`

Text: "If the initial condition is spatially correlated (e.g., a localised outbreak), the
factorisation θ(0) = 1 - ε breaks down for edges near the seed." -/

-- VOCAB-GAP: the factorisation θ(0) = 1 − ε and "edges near the seed" are not representable;
-- a spatially correlated initial condition is `InitCondType.localised`, for every network and
-- transition type.
-- AMBIGUITY: "breaks down" read as (S1) the standard EBCM is not valid, and (S2, stronger,
-- following the §5 framing "obstructions ... under which no valid object in Edge maps to the
-- desired behaviour") no EBCM variant exists.

@[sa_reference "Docs.cf.localisedObstruction"]
def T : Prop :=
  (∀ (n : NetworkType) (tr : TransitionType), ¬ standardEbcmValid n tr InitCondType.localised) ∧
  (∀ (n : NetworkType) (tr : TransitionType), ¬ ebcmExists n tr InitCondType.localised)

/-- S1: with localised initial conditions the standard EBCM is not valid. -/
@[sa_shadow "Docs.cf.localisedObstruction" 1]
def S1 : Prop :=
  ∀ (n : NetworkType) (tr : TransitionType), ¬ standardEbcmValid n tr InitCondType.localised

/-- S2: with localised initial conditions no EBCM variant exists. -/
@[sa_shadow "Docs.cf.localisedObstruction" 2]
def S2 : Prop :=
  ∀ (n : NetworkType) (tr : TransitionType), ¬ ebcmExists n tr InitCondType.localised

@[sa_ref_forward "Docs.cf.localisedObstruction" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.localisedObstruction" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Docs.cf.localisedObstruction"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Docs.cf_localisedObstruction

namespace Alignment.Shadows.Docs.cf_thetaNonincreasing

/-! ### `Docs.cf.thetaNonincreasing`

Text: "In the EBCM, θ(t) is non-increasing (edges can only transmit, not "un-transmit")." -/

-- VOCAB-GAP: `DataTypes/Docs.md` has no trajectory or vector field of the standard EBCM. The
-- claim is stated with Mathlib primitives, using the EBCM θ-equation of §2.2 (single type,
-- single infectious stage; Miller–Slim–Volz): dθ/dt = −β·φ_I, where φ_I (probability that a
-- neighbour is infected and has not yet transmitted) is an edge-state coordinate and so lies in
-- [0, 1] (Edge state space [0,1]^n). "Non-increasing" is read on the time domain t ≥ 0.
-- AMBIGUITY: the only EBCM θ-derivative in the vocabulary is the Volz–Meyers `VMState.dθ`;
-- that variant model is not used for "the EBCM".

@[sa_reference "Docs.cf.thetaNonincreasing"]
def T : Prop :=
  ∀ (β : ℝ), 0 < β → ∀ (θ φI : ℝ → ℝ),
    (∀ t : ℝ, 0 ≤ t → HasDerivAt θ (-(β * φI t)) t) →
    (∀ t : ℝ, 0 ≤ t → 0 ≤ φI t ∧ φI t ≤ 1) →
    AntitoneOn θ (Set.Ici 0)

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "Docs.cf.thetaNonincreasing" 1]
def S1 : Prop :=
  ∀ (β : ℝ), 0 < β → ∀ (θ φI : ℝ → ℝ),
    (∀ t : ℝ, 0 ≤ t → HasDerivAt θ (-(β * φI t)) t) →
    (∀ t : ℝ, 0 ≤ t → 0 ≤ φI t ∧ φI t ≤ 1) →
    AntitoneOn θ (Set.Ici 0)

@[sa_ref_forward "Docs.cf.thetaNonincreasing" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Docs.cf.thetaNonincreasing"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Docs.cf_thetaNonincreasing

namespace Alignment.Shadows.Docs.cf_thm8_1

/-! ### `Docs.cf.thm8_1`

Text: "**Theorem 8.1 (Degree-variance inequality).** Let ψ be any valid PGF with mean degree κ.
Then: [...] ψ''(1)/ψ'(1) = κ + (σ² - κ)/κ = κ + (σ²/κ - 1) [...] where σ² = Var(degree)." -/

-- "any valid PGF" = any `PGFData`; κ = ψ'(1) = `ψ.mean`; σ² = `PGFData.variance ψ`.
-- The chain A = B = C is split as A = B (S1) and A = C (S2).

@[sa_reference "Docs.cf.thm8_1"]
def T : Prop :=
  ∀ ψ : PGFData,
    ψ.secondFactorial / ψ.mean = ψ.mean + (PGFData.variance ψ - ψ.mean) / ψ.mean ∧
      ψ.mean + (PGFData.variance ψ - ψ.mean) / ψ.mean = ψ.mean + (PGFData.variance ψ / ψ.mean - 1)

/-- S1: ψ''(1)/ψ'(1) = κ + (σ² − κ)/κ. -/
@[sa_shadow "Docs.cf.thm8_1" 1]
def S1 : Prop :=
  ∀ ψ : PGFData, ψ.secondFactorial / ψ.mean = ψ.mean + (PGFData.variance ψ - ψ.mean) / ψ.mean

/-- S2: ψ''(1)/ψ'(1) = κ + (σ²/κ − 1). -/
@[sa_shadow "Docs.cf.thm8_1" 2]
def S2 : Prop :=
  ∀ ψ : PGFData, ψ.secondFactorial / ψ.mean = ψ.mean + (PGFData.variance ψ / ψ.mean - 1)

@[sa_ref_forward "Docs.cf.thm8_1" 1] theorem ref_fwd1 : T → S1 := fun t ψ => (t ψ).1
@[sa_ref_forward "Docs.cf.thm8_1" 2]
theorem ref_fwd2 : T → S2 := fun t ψ => (t ψ).1.trans (t ψ).2
@[sa_complete "Docs.cf.thm8_1"]
theorem complete (s1 : S1) (s2 : S2) : T := fun ψ => ⟨s1 ψ, (s1 ψ).symm.trans (s2 ψ)⟩

end Alignment.Shadows.Docs.cf_thm8_1

namespace Alignment.Shadows.Docs.ms_T4

open EBCMCategory.MarginalisationCharacterization

/-! ### `Docs.ms.T4`

Text: "theorem fibre_collapse_obstruction (M : V₄ →ₗ[ℝ] V₃) (F : V₄ → V₄) (u₁ u₂ : V₄) (h_fibre :
M u₁ = M u₂) (h_split : M (F u₁) ≠ M (F u₂)) : ∀ (C₃ : ClosureFamily V₃), ¬ Equivariant M F C₃.C
[...] Lifts the argument inlined in T3b to a reusable structural lemma." -/

-- V₄, V₃ are arbitrary real vector spaces (any universes), as in the `Equivariant` signature.
-- "Lifts the argument ... reusable structural lemma" is descriptive, not a separate requirement.

@[sa_reference "Docs.ms.T4"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (F : V₄ → V₄) (u₁ u₂ : V₄),
    M u₁ = M u₂ → M (F u₁) ≠ M (F u₂) → ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M F C₃.C

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "Docs.ms.T4" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (F : V₄ → V₄) (u₁ u₂ : V₄),
    M u₁ = M u₂ → M (F u₁) ≠ M (F u₂) → ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M F C₃.C

@[sa_ref_forward "Docs.ms.T4" 1] theorem ref_fwd1 : T.{u, v} → S1.{u, v} := fun t => t
@[sa_complete "Docs.ms.T4"] theorem complete (s1 : S1.{u, v}) : T.{u, v} := s1

end Alignment.Shadows.Docs.ms_T4

namespace Alignment.Shadows.Docs.ms_T4_companion

open EBCMCategory.MarginalisationCharacterization

/-! ### `Docs.ms.T4-companion`

Text: "A companion theorem `kirkwood_not_equivariant_via_T4` re-derives T3b using T4." -/

-- AMBIGUITY: T3b is not stated in the cited passage. It is read (spec §5: "T3b (via T4)
-- certifies no correct Kirkwood marginalisation can fix this") as: at the witness, the
-- Kirkwood order-4 RHS is not equivariant, under the marginalisation Mℝ, with ANY order-3
-- closure family. The order-4 Kirkwood RHS is read as (S1) `F4Kℝ` ("The Kirkwood-closed order-4
-- RHS at the witness configuration") and (S2) the packaged family `C4ℝ` (its map `C4ℝ.C`).
-- "using T4" (how it is proved) is not a checkable statement.

@[sa_reference "Docs.ms.T4-companion"]
def T : Prop :=
  (∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin F4Kℝ C₃.C) ∧
  (∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin C4ℝ.C C₃.C)

/-- S1: `F4Kℝ` is not Mℝ-equivariant with any order-3 closure. -/
@[sa_shadow "Docs.ms.T4-companion" 1]
def S1 : Prop := ∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin F4Kℝ C₃.C

/-- S2: the Kirkwood family `C4ℝ` is not Mℝ-equivariant with any order-3 closure. -/
@[sa_shadow "Docs.ms.T4-companion" 2]
def S2 : Prop := ∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin C4ℝ.C C₃.C

@[sa_ref_forward "Docs.ms.T4-companion" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.ms.T4-companion" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Docs.ms.T4-companion"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Docs.ms_T4_companion

namespace Alignment.Shadows.Docs.ms_T5

open EBCMCategory.Marginalisation EBCMCategory.MarginalisationDynamicalGap

/-! ### `Docs.ms.T5`

Text: "theorem trajectoryGap_hasDerivAt_zero (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃)
{φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃} (h₄ : IsFlow F₄ φ₄) (h₃ : IsFlow F₃ φ₃) (u : V₄) :
HasDerivAt (trajectoryGap M φ₄ φ₃ u) (algebraicGap M F₄ F₃ u) 0" -/

-- S1 is the displayed statement with the operations; S2 states it in primitive terms, with the
-- trajectory gap t ↦ M (φ₄ u t) − φ₃ (M u) t and the algebraic gap M (F₄ u) − F₃ (M u) (their
-- docstrings / the spec's definitions). Arbitrary real normed spaces, any universes.

@[sa_reference "Docs.ms.T5"]
def T : Prop :=
  (∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
      [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
      (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
      IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ u : V₄,
        HasDerivAt (trajectoryGap M φ₄ φ₃ u) (algebraicGap M F₄ F₃ u) 0) ∧
  (∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
      [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
      (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
      IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ u : V₄,
        HasDerivAt (fun t => M (φ₄ u t) - φ₃ (M u) t) (M (F₄ u) - F₃ (M u)) 0)

/-- S1: the derivative at 0 of `trajectoryGap` is `algebraicGap`. -/
@[sa_shadow "Docs.ms.T5" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ u : V₄,
      HasDerivAt (trajectoryGap M φ₄ φ₃ u) (algebraicGap M F₄ F₃ u) 0

/-- S2: primitive form: d/dt|₀ [M (φ₄ u t) − φ₃ (M u) t] = M (F₄ u) − F₃ (M u). -/
@[sa_shadow "Docs.ms.T5" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ u : V₄,
      HasDerivAt (fun t => M (φ₄ u t) - φ₃ (M u) t) (M (F₄ u) - F₃ (M u)) 0

@[sa_ref_forward "Docs.ms.T5" 1] theorem ref_fwd1 : T.{u, v} → S1.{u, v} := fun t => t.1
@[sa_ref_forward "Docs.ms.T5" 2] theorem ref_fwd2 : T.{u, v} → S2.{u, v} := fun t => t.2
@[sa_complete "Docs.ms.T5"]
theorem complete (s1 : S1.{u, v}) (s2 : S2.{u, v}) : T.{u, v} := ⟨s1, s2⟩

end Alignment.Shadows.Docs.ms_T5

namespace Alignment.Shadows.Docs.ms_T6

open EBCMCategory.MarginalisationCharacterization EBCMCategory.MarginalisationDynamicalGap

/-! ### `Docs.ms.T6`

Text: the displayed statement of `refinement_failure_exists` [...] "Witness: `F4_kirk = F4Kℝ`,
`F3_kirk = F3Kℝ`, `F3_exact = const 6`, `u₀ = u₁`." -/

-- S1: the existential statement; S2–S5: the named witness satisfies each of its four conjuncts
-- (`const 6` = the constant map with value the constant vector 6).

@[sa_reference "Docs.ms.T6"]
def T : Prop :=
  (∃ (F4_kirk : U4ℝ → U4ℝ) (F3_kirk : U3ℝ → U3ℝ) (F3_exact : U3ℝ → U3ℝ) (u₀ : U4ℝ),
      (ClosureFamily.mk F4_kirk).IsKirkwoodForm ∧
      (ClosureFamily.mk F3_kirk).IsKirkwoodForm ∧
      MℝLin (F4_kirk u₀) = F3_exact (MℝLin u₀) ∧
      F3_kirk (MℝLin u₀) ≠ F3_exact (MℝLin u₀)) ∧
  (ClosureFamily.mk F4Kℝ).IsKirkwoodForm ∧
  (ClosureFamily.mk F3Kℝ).IsKirkwoodForm ∧
  MℝLin (F4Kℝ u₁) = (fun _ => (6 : ℝ)) ∧
  F3Kℝ (MℝLin u₁) ≠ (fun _ => (6 : ℝ))

/-- S1: the existential statement. -/
@[sa_shadow "Docs.ms.T6" 1]
def S1 : Prop :=
  ∃ (F4_kirk : U4ℝ → U4ℝ) (F3_kirk : U3ℝ → U3ℝ) (F3_exact : U3ℝ → U3ℝ) (u₀ : U4ℝ),
    (ClosureFamily.mk F4_kirk).IsKirkwoodForm ∧
    (ClosureFamily.mk F3_kirk).IsKirkwoodForm ∧
    MℝLin (F4_kirk u₀) = F3_exact (MℝLin u₀) ∧
    F3_kirk (MℝLin u₀) ≠ F3_exact (MℝLin u₀)

/-- S2: the witness `F4Kℝ` has Kirkwood form. -/
@[sa_shadow "Docs.ms.T6" 2]
def S2 : Prop := (ClosureFamily.mk F4Kℝ).IsKirkwoodForm

/-- S3: the witness `F3Kℝ` has Kirkwood form. -/
@[sa_shadow "Docs.ms.T6" 3]
def S3 : Prop := (ClosureFamily.mk F3Kℝ).IsKirkwoodForm

/-- S4: at u₁ the marginalised order-4 RHS equals the exact value (const 6). -/
@[sa_shadow "Docs.ms.T6" 4]
def S4 : Prop := MℝLin (F4Kℝ u₁) = (fun _ => (6 : ℝ))

/-- S5: at M u₁ the order-3 Kirkwood RHS differs from the exact value (const 6). -/
@[sa_shadow "Docs.ms.T6" 5]
def S5 : Prop := F3Kℝ (MℝLin u₁) ≠ (fun _ => (6 : ℝ))

@[sa_ref_forward "Docs.ms.T6" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.ms.T6" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.ms.T6" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Docs.ms.T6" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "Docs.ms.T6" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2
@[sa_complete "Docs.ms.T6"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.Docs.ms_T6

namespace Alignment.Shadows.Docs.ms_T6_values

open EBCMCategory.MarginalisationCharacterization EBCMCategory.MarginalisationDynamicalGap
  MarginalisationObstruction

/-! ### `Docs.ms.T6-values`

Text: "`M(F4Kℝ u₁)(c) = 1·3 + 3 = 6` — m=4 chain is **exact** at first order. * `F3Kℝ(M u₁)(c) =
4²/4 = 4 ≠ 6` — m=3 Kirkwood deviates by 2." -/

-- AMBIGUITY: `M` read as `MℝLin` (the marginalisation of the T6 statement).
-- The intermediate arithmetic (1·3 + 3, 4²/4) is presentation; the asserted values are 6 and 4.
-- "m=4 chain is exact" = the value equals the exact value 6 (S1). "deviates by 2" read as the
-- difference m=4 value − m=3 value = 2 at c (S4).

@[sa_reference "Docs.ms.T6-values"]
def T : Prop :=
  MℝLin (F4Kℝ u₁) Idx3.c = 6 ∧
  F3Kℝ (MℝLin u₁) Idx3.c = 4 ∧
  F3Kℝ (MℝLin u₁) Idx3.c ≠ 6 ∧
  MℝLin (F4Kℝ u₁) Idx3.c - F3Kℝ (MℝLin u₁) Idx3.c = 2

/-- S1: M(F4Kℝ u₁)(c) = 6. -/
@[sa_shadow "Docs.ms.T6-values" 1]
def S1 : Prop := MℝLin (F4Kℝ u₁) Idx3.c = 6

/-- S2: F3Kℝ(M u₁)(c) = 4. -/
@[sa_shadow "Docs.ms.T6-values" 2]
def S2 : Prop := F3Kℝ (MℝLin u₁) Idx3.c = 4

/-- S3: F3Kℝ(M u₁)(c) ≠ 6. -/
@[sa_shadow "Docs.ms.T6-values" 3]
def S3 : Prop := F3Kℝ (MℝLin u₁) Idx3.c ≠ 6

/-- S4: the m=3 Kirkwood value deviates from the m=4 value by 2. -/
@[sa_shadow "Docs.ms.T6-values" 4]
def S4 : Prop := MℝLin (F4Kℝ u₁) Idx3.c - F3Kℝ (MℝLin u₁) Idx3.c = 2

@[sa_ref_forward "Docs.ms.T6-values" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.ms.T6-values" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.ms.T6-values" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Docs.ms.T6-values" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "Docs.ms.T6-values"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.Docs.ms_T6_values

namespace Alignment.Shadows.Docs.ms_T7

open EBCMCategory.Marginalisation EBCMCategory.MarginalisationDynamicalGap

/-! ### `Docs.ms.T7`

Text: the displayed statement of `trajectoryGap_norm_ge_half_eps_t` [...] "Quantitative
time-domain refinement of T5: if the algebraic gap has norm at least `ε`, then the trajectory gap
grows at least linearly (at rate `ε/2`) for sufficiently small positive `t`." -/

-- S1: the displayed statement with the operations; S2: primitive form (gaps written out).
-- Arbitrary real normed spaces, any universes.

@[sa_reference "Docs.ms.T7"]
def T : Prop :=
  (∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
      [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
      (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
      IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ (u : V₄) {ε : ℝ}, 0 < ε →
        ε ≤ ‖algebraicGap M F₄ F₃ u‖ →
        ∃ τ > 0, ∀ t, 0 < t → t ≤ τ → ε * t / 2 ≤ ‖trajectoryGap M φ₄ φ₃ u t‖) ∧
  (∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
      [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
      (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
      IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ (u : V₄) {ε : ℝ}, 0 < ε →
        ε ≤ ‖M (F₄ u) - F₃ (M u)‖ →
        ∃ τ > 0, ∀ t, 0 < t → t ≤ τ → ε * t / 2 ≤ ‖M (φ₄ u t) - φ₃ (M u) t‖)

/-- S1: the displayed lower bound, stated with `algebraicGap` / `trajectoryGap`. -/
@[sa_shadow "Docs.ms.T7" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ (u : V₄) {ε : ℝ}, 0 < ε →
      ε ≤ ‖algebraicGap M F₄ F₃ u‖ →
      ∃ τ > 0, ∀ t, 0 < t → t ≤ τ → ε * t / 2 ≤ ‖trajectoryGap M φ₄ φ₃ u t‖

/-- S2: the same lower bound with the gaps in primitive terms. -/
@[sa_shadow "Docs.ms.T7" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄]
    [NormedAddCommGroup V₃] [NormedSpace ℝ V₃]
    (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃},
    IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → ∀ (u : V₄) {ε : ℝ}, 0 < ε →
      ε ≤ ‖M (F₄ u) - F₃ (M u)‖ →
      ∃ τ > 0, ∀ t, 0 < t → t ≤ τ → ε * t / 2 ≤ ‖M (φ₄ u t) - φ₃ (M u) t‖

@[sa_ref_forward "Docs.ms.T7" 1] theorem ref_fwd1 : T.{u, v} → S1.{u, v} := fun t => t.1
@[sa_ref_forward "Docs.ms.T7" 2] theorem ref_fwd2 : T.{u, v} → S2.{u, v} := fun t => t.2
@[sa_complete "Docs.ms.T7"]
theorem complete (s1 : S1.{u, v}) (s2 : S2.{u, v}) : T.{u, v} := ⟨s1, s2⟩

end Alignment.Shadows.Docs.ms_T7

/-! ## README "Lean proofs" section

The four `Docs.readme.*` claims of the former README sentence were retired (WP4) when the
sentence was replaced; their shadow sets were removed with them. The new README claims are
informal and have no shadows. -/

noncomputable section

/-! ## Shared notions for the re-authored Docs blocks (blind)

Not registered; inlined by the audit. Sources: `categorical_foundations.md` §3–§8 and
`EBCMCategory/MARGINALISATION_SPEC.md` §1–§5 (read in full for context).

* Poisson EBCM with per-edge rates β̃ = `p.β`, γ̃ = `p.γ` (an `SIRParams`) and mean degree κ
  (§4.1, §4.3): `θ̇ = −β̃θ + β̃e^{κ(θ−1)} + γ̃(1−θ)`, `S = e^{κ(θ−1)}`, `φ_I = −θ̇/β̃`; classical
  (mass-action) SIR `Ṡ = −βSI`, `İ = βSI − γI`; network recovery `Ṙ = γ̃(1 − S − R)`.
* The lift of §4.1: per-edge rates β̃ = β/κ, γ̃ = γ − β/κ for κ > R₀ = β/γ.
* The non-Poisson law ψ(u) = (1 + u²)/2 of Theorem 4.3.
* A local solution (MARGINALISATION_SPEC §1, "Local solution"): `0 < δ ∧ ψ 0 = v₀ ∧
  ∀ t, |t| < δ → HasDerivAt ψ (F (ψ t)) t`. -/
namespace Alignment.Shadows.Docs.Shared2

open EBCMCategory.Marginalisation EBCMCategory.MarginalisationCharacterization
open EBCMCategory.MarginalisationDynamicalGap MarginalisationObstruction

/-- Right-hand side of the Poisson EBCM θ-equation. -/
def ebcmRHS (p : SIRParams) (κ : ℚ) (x : ℝ) : ℝ :=
  -(p.β : ℝ) * x + (p.β : ℝ) * Real.exp ((κ : ℝ) * (x - 1)) + (p.γ : ℝ) * (1 - x)
/-- `S = e^{κ(θ−1)}`. -/
def Sof (κ : ℚ) (x : ℝ) : ℝ := Real.exp ((κ : ℝ) * (x - 1))
/-- `φ_I = −θ̇/β̃`. -/
def phiI (p : SIRParams) (κ : ℚ) (x : ℝ) : ℝ := -(ebcmRHS p κ x) / (p.β : ℝ)
/-- `(S, I)` solves classical SIR with rates `β`, `γ`. -/
def IsSIR (β γ : ℝ) (S I : ℝ → ℝ) : Prop :=
  (∀ t, HasDerivAt S (-β * S t * I t) t) ∧ (∀ t, HasDerivAt I (β * S t * I t - γ * I t) t)
/-- Mass action matches the Poisson EBCM's S(t) with β = κβ̃, γ = β̃ + γ̃ and I := φ_I. -/
def SMatch : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (θ : ℝ → ℝ), 0 < κ → (∀ t, HasDerivAt θ (ebcmRHS p κ (θ t)) t) →
    IsSIR ((κ : ℝ) * p.β) ((p.β : ℝ) + p.γ) (fun t => Sof κ (θ t)) (fun t => phiI p κ (θ t))
/-- The mass-action infected curve φ_I is not the network prevalence (for some solution). -/
def IDiffer : Prop :=
  ∃ (p : SIRParams) (κ : ℚ) (θ R : ℝ → ℝ) (t : ℝ), 0 < κ ∧
    (∀ s, HasDerivAt θ (ebcmRHS p κ (θ s)) s) ∧
    (∀ s, HasDerivAt R ((p.γ : ℝ) * (1 - Sof κ (θ s) - R s)) s) ∧
    phiI p κ (θ t) ≠ 1 - Sof κ (θ t) - R t

/-- The lifted per-edge rates `β̃ = β/κ`, `γ̃ = γ − β/κ` (valid for κ > β/γ). -/
def liftParams (β γ κ : ℚ) (hβ : 0 < β) (hγ : 0 < γ) (hκ : 0 < κ) (h : β / γ < κ) : SIRParams :=
  ⟨β / κ, γ - β / κ, div_pos hβ hκ,
    by rw [sub_pos, div_lt_iff₀ hκ]; rw [div_lt_iff₀ hγ] at h; linarith⟩

/-- The law ψ(u) = (1 + u²)/2. -/
def psiMix (u : ℝ) : ℝ := (1 + u ^ 2) / 2

/-- `ψ` is a local solution of `F` through `v`. -/
def LocalSol {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → V) (v : V)
    (ψ : ℝ → V) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ψ 0 = v ∧ ∀ t : ℝ, |t| < δ → HasDerivAt ψ (F (ψ t)) t

/-- The constant order-3 vector with value `r`. -/
def cst (r : ℝ) : U3ℝ := fun _ => r
/-- The order-3 closure `c ↦ 3c²/8` over ℝ. -/
def C3match : U3ℝ → U3ℝ := fun v => cst (3 * v Idx3.c ^ 2 / 8)
/-- The T2 witness state `u4 = (1, 3)` over ℚ. -/
def wQ : U4 := fun i =>
  match i with
  | Idx4.a => 1
  | Idx4.b => 3

end Alignment.Shadows.Docs.Shared2

/-! ## `Docs.cf.coarseGrainDef` (blind)

Text: "Given an EBCM object (θ, φ, R, ψ), define F on objects by: [...] F(θ, φ, R, ψ) = (S, I, R)
where S_l = ψ_l(θ_{1l}, …, θ_{Kl}) (evaluate PGF at θ-vector) R_l = R_l (identity)
I_l = 1 - S_l - R_l (derived) [...] On morphisms, F is not yet defined: the formula ψ ∘ h ∘ ψ^{-1}
does not type-check in general (h acts on (θ, φ, R), ψ only on θ), so F is a map on objects only."

The Lean F is `coarseGrain` on `EpiModel` records. -- AMBIGUITY: the definition is read through
its one checkable consequence for the records: F lands in the node-level state space (S, I, R),
i.e. a 3-dimensional model. The component formulas are definitions (I := 1 − S − R), and "a map
on objects only" is a remark. -/
namespace Alignment.Shadows.Docs.cf_coarseGrainDef

@[sa_reference "Docs.cf.coarseGrainDef"]
def T : Prop := ∀ e : EpiModel, (coarseGrain e).dim = 3

/-- S1: F produces a node-level (S, I, R) model. -/
@[sa_shadow "Docs.cf.coarseGrainDef" 1]
def S1 : Prop := ∀ e : EpiModel, (coarseGrain e).dim = 3

@[sa_ref_forward "Docs.cf.coarseGrainDef" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Docs.cf.coarseGrainDef"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Docs.cf_coarseGrainDef

/-! ## `Docs.cf.cor4_2-GF` (re-authored blind)

Text: "G ∘ F ≠ id_Edge (projecting then lifting forgets the original PGF)"

Corollary 4.2 says these identities hold for the Lean records (dimension and R₀). S1: `G ∘ F ≠ id`;
S2 ("forgets"): `G(F e)` depends on `e` only through its R₀. -/
namespace Alignment.Shadows.Docs.cf_cor4_2_GF

@[sa_reference "Docs.cf.cor4_2-GF"]
def T : Prop :=
  poissonLift ∘ coarseGrain ≠ id ∧
    ∀ e e' : EpiModel, e.R0 = e'.R0 → poissonLift (coarseGrain e) = poissonLift (coarseGrain e')

/-- S1: `G ∘ F ≠ id`. -/
@[sa_shadow "Docs.cf.cor4_2-GF" 1]
def S1 : Prop := poissonLift ∘ coarseGrain ≠ id
/-- S2: `G ∘ F` keeps only the R₀ of its argument. -/
@[sa_shadow "Docs.cf.cor4_2-GF" 2]
def S2 : Prop :=
  ∀ e e' : EpiModel, e.R0 = e'.R0 → poissonLift (coarseGrain e) = poissonLift (coarseGrain e')

@[sa_ref_forward "Docs.cf.cor4_2-GF" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.cor4_2-GF" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Docs.cf.cor4_2-GF"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Docs.cf_cor4_2_GF

/-! ## `Docs.cf.dispersionSingleScalar` (blind)

Text: "The correction involves the **index of dispersion** σ²/κ and the mean κ:
ψ''(1)/ψ'(1) = κ − 1 + σ²/κ. No single scalar measures how much information the EBCM adds over the
node model."

S1: the identity for every degree record (`excessDegree`, `dispersionIndex`). The second sentence
is informal and not formalised. -/
namespace Alignment.Shadows.Docs.cf_dispersionSingleScalar

@[sa_reference "Docs.cf.dispersionSingleScalar"]
def T : Prop := ∀ ψ : PGFData, ψ.excessDegree = ψ.mean - 1 + ψ.dispersionIndex

/-- S1: `ψ''(1)/ψ'(1) = κ − 1 + σ²/κ`. -/
@[sa_shadow "Docs.cf.dispersionSingleScalar" 1]
def S1 : Prop := ∀ ψ : PGFData, ψ.excessDegree = ψ.mean - 1 + ψ.dispersionIndex

@[sa_ref_forward "Docs.cf.dispersionSingleScalar" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Docs.cf.dispersionSingleScalar"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Docs.cf_dispersionSingleScalar

/-! ## `Docs.cf.liftDef` (blind)

Text: "Given a node-based SIR model with mass-action rates β and γ (R₀ = β/γ), define G by: [...]
G(S, I, R; β, γ) = EBCM(ψ_Poisson(κ), β̃, γ̃) where β̃ = β/κ, γ̃ = γ − β/κ, for any mean degree
κ > R₀"

S1: for κ > R₀ = β/γ the lifted recovery rate γ̃ is positive (the lift is a valid EBCM); S2: the
lifted Poisson edge model has the node model's R₀ β/γ (`edgeModel`). -/
namespace Alignment.Shadows.Docs.cf_liftDef

open Alignment.Shadows.Docs.Shared2

@[sa_reference "Docs.cf.liftDef"]
def T : Prop :=
  (∀ β γ κ : ℚ, 0 < β → 0 < γ → 0 < κ → β / γ < κ → 0 < γ - β / κ) ∧
  (∀ (β γ κ : ℚ) (hβ : 0 < β) (hγ : 0 < γ) (hκ : 0 < κ) (h : β / γ < κ),
      (edgeModel (liftParams β γ κ hβ hγ hκ h) (PGFData.poisson κ hκ)).R0 = β / γ)

/-- S1: the lifted γ̃ is positive for κ > R₀. -/
@[sa_shadow "Docs.cf.liftDef" 1]
def S1 : Prop := ∀ β γ κ : ℚ, 0 < β → 0 < γ → 0 < κ → β / γ < κ → 0 < γ - β / κ
/-- S2: the lifted Poisson EBCM has R₀ = β/γ. -/
@[sa_shadow "Docs.cf.liftDef" 2]
def S2 : Prop :=
  ∀ (β γ κ : ℚ) (hβ : 0 < β) (hγ : 0 < γ) (hκ : 0 < κ) (h : β / γ < κ),
    (edgeModel (liftParams β γ κ hβ hγ hκ h) (PGFData.poisson κ hκ)).R0 = β / γ

@[sa_ref_forward "Docs.cf.liftDef" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.liftDef" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Docs.cf.liftDef"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Docs.cf_liftDef

/-! ## `Docs.cf.liftNotUnique` (blind)

Text: "**Caveat:** Even the Poisson lift is not unique: any mean degree κ > R₀ works, with β̃ = β/κ
and γ̃ = γ − β/κ. [...] The Poisson lift is singled out by giving mass-action dynamics for S, not by
any minimality property."

"Works": the lifted Poisson EBCM keeps the node model's R₀ (S1) and reproduces the mass-action
S(t) with rates β = κβ̃, γ = β̃ + γ̃ (S2); "not unique": two different κ both work (S3). The last
sentence contrasts two properties and is covered by `Docs.cf.poissonUniqueSection`. -/
namespace Alignment.Shadows.Docs.cf_liftNotUnique

open Alignment.Shadows.Docs.Shared2

@[sa_reference "Docs.cf.liftNotUnique"]
def T : Prop :=
  (∀ (β γ κ : ℚ) (hβ : 0 < β) (hγ : 0 < γ) (hκ : 0 < κ) (h : β / γ < κ),
      (edgeModel (liftParams β γ κ hβ hγ hκ h) (PGFData.poisson κ hκ)).R0 = β / γ) ∧
  (∀ (β γ κ : ℚ) (hβ : 0 < β) (hγ : 0 < γ) (hκ : 0 < κ) (h : β / γ < κ) (θ : ℝ → ℝ),
      (∀ t, HasDerivAt θ (ebcmRHS (liftParams β γ κ hβ hγ hκ h) κ (θ t)) t) →
      ∃ I : ℝ → ℝ, IsSIR (β : ℝ) (γ : ℝ) (fun t => Sof κ (θ t)) I) ∧
  (∀ β γ : ℚ, 0 < β → 0 < γ → ∃ κ₁ κ₂ : ℚ, β / γ < κ₁ ∧ β / γ < κ₂ ∧ κ₁ ≠ κ₂)

/-- S1: every κ > R₀ gives a lift with the node model's R₀. -/
@[sa_shadow "Docs.cf.liftNotUnique" 1]
def S1 : Prop :=
  ∀ (β γ κ : ℚ) (hβ : 0 < β) (hγ : 0 < γ) (hκ : 0 < κ) (h : β / γ < κ),
    (edgeModel (liftParams β γ κ hβ hγ hκ h) (PGFData.poisson κ hκ)).R0 = β / γ
/-- S2: every κ > R₀ gives a lift with the mass-action S(t). -/
@[sa_shadow "Docs.cf.liftNotUnique" 2]
def S2 : Prop :=
  ∀ (β γ κ : ℚ) (hβ : 0 < β) (hγ : 0 < γ) (hκ : 0 < κ) (h : β / γ < κ) (θ : ℝ → ℝ),
    (∀ t, HasDerivAt θ (ebcmRHS (liftParams β γ κ hβ hγ hκ h) κ (θ t)) t) →
    ∃ I : ℝ → ℝ, IsSIR (β : ℝ) (γ : ℝ) (fun t => Sof κ (θ t)) I
/-- S3: at least two mean degrees exceed R₀. -/
@[sa_shadow "Docs.cf.liftNotUnique" 3]
def S3 : Prop := ∀ β γ : ℚ, 0 < β → 0 < γ → ∃ κ₁ κ₂ : ℚ, β / γ < κ₁ ∧ β / γ < κ₂ ∧ κ₁ ≠ κ₂

@[sa_ref_forward "Docs.cf.liftNotUnique" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.liftNotUnique" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.cf.liftNotUnique" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Docs.cf.liftNotUnique"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Docs.cf_liftNotUnique

/-! ## `Docs.cf.nonMarkovObstruction` (re-authored blind)

Text: "The ODE system must be replaced by integro-differential equations or delay-differential
equations. [...] These dynamics are outside the ODE-based **Edge** models, but they are not an
obstruction to edge-based modelling: the non-Markovian EBCM is exact for general independent
transmission and recovery processes (Sherborne, Miller, Blyuss & Kiss 2018)."

Vocabulary of `Obstructions`: S1 the general non-Markovian case does not give an ODE system
(`systemRequired`), S2 its system is the PDE one; S3 an EBCM variant exists for it on
configuration-model networks with uniform seeding (`ebcmExists`), so it is not an obstruction. -/
namespace Alignment.Shadows.Docs.cf_nonMarkovObstruction

@[sa_reference "Docs.cf.nonMarkovObstruction"]
def T : Prop :=
  systemRequired .generalNonMarkov .uniform ≠ .ode ∧ systemRequired .generalNonMarkov .uniform = .pde ∧
    ebcmExists .configurationModel .generalNonMarkov .uniform

/-- S1: the non-Markovian system is not an ODE system. -/
@[sa_shadow "Docs.cf.nonMarkovObstruction" 1]
def S1 : Prop := systemRequired .generalNonMarkov .uniform ≠ .ode
/-- S2: it is the age-structured PDE system. -/
@[sa_shadow "Docs.cf.nonMarkovObstruction" 2]
def S2 : Prop := systemRequired .generalNonMarkov .uniform = .pde
/-- S3: a (non-Markovian) EBCM exists, so it is not an obstruction. -/
@[sa_shadow "Docs.cf.nonMarkovObstruction" 3]
def S3 : Prop := ebcmExists .configurationModel .generalNonMarkov .uniform

@[sa_ref_forward "Docs.cf.nonMarkovObstruction" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.nonMarkovObstruction" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.cf.nonMarkovObstruction" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Docs.cf.nonMarkovObstruction"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Docs.cf_nonMarkovObstruction

/-! ## `Docs.cf.pgfClosureTreeLike` (blind)

Text: "S(t) = ψ(θ(t)) (exact on configuration-model networks as N → ∞, which are locally
tree-like)"

-- AMBIGUITY: the N → ∞ limit is not formalisable with the vocabulary; read through its record in
`Obstructions`: the standard EBCM (built on S = ψ(θ)) is valid on configuration-model networks
(Markovian, uniform seeding). -/
namespace Alignment.Shadows.Docs.cf_pgfClosureTreeLike

@[sa_reference "Docs.cf.pgfClosureTreeLike"]
def T : Prop := standardEbcmValid .configurationModel .markovian .uniform

/-- S1: the PGF closure is exact (the standard EBCM is valid) on configuration models. -/
@[sa_shadow "Docs.cf.pgfClosureTreeLike" 1]
def S1 : Prop := standardEbcmValid .configurationModel .markovian .uniform

@[sa_ref_forward "Docs.cf.pgfClosureTreeLike" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Docs.cf.pgfClosureTreeLike"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Docs.cf_pgfClosureTreeLike

/-! ## `Docs.cf.poissonEquivMassAction` (blind)

Text: "Markovian on Poisson network ← same S(t) as mass-action SIR (after reparametrisation)" -/
namespace Alignment.Shadows.Docs.cf_poissonEquivMassAction

open Alignment.Shadows.Docs.Shared2

@[sa_reference "Docs.cf.poissonEquivMassAction"]
def T : Prop := SMatch

/-- S1: the Poisson EBCM's S(t) solves mass-action SIR after reparametrisation. -/
@[sa_shadow "Docs.cf.poissonEquivMassAction" 1]
def S1 : Prop := SMatch

@[sa_ref_forward "Docs.cf.poissonEquivMassAction" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Docs.cf.poissonEquivMassAction"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Docs.cf_poissonEquivMassAction

/-! ## `Docs.cf.poissonUniqueSection` (blind)

Text: "This embeds the node-based model into an EBCM with the **Poisson PGF**, whose susceptible
curve matches the node model's after this reparametrisation; the EBCM infected curve differs. Among
PGFs, only the Poisson PGF gives mass-action dynamics for S (Theorem 4.3(c))."

S1: G embeds the node model as the Poisson edge model (`poissonLift`, `edgeModel`); S2: the
susceptible curves match after reparametrisation; S3: the infected curves differ; S4: a PGF with
ψ(1) = 1 and mass-action dynamics for S (ψ′ = κψ on [0, 1], Theorem 4.3(c)) is the Poisson PGF on
[0, 1]. -/
namespace Alignment.Shadows.Docs.cf_poissonUniqueSection

open Alignment.Shadows.Docs.Shared2

@[sa_reference "Docs.cf.poissonUniqueSection"]
def T : Prop :=
  (∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
      poissonLift (nodeModel p κ) = edgeModel p (PGFData.poisson κ hκ)) ∧
  SMatch ∧ IDiffer ∧
  (∀ (ψ : ℝ → ℝ) (κ : ℝ), ψ 1 = 1 → (∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ψ (κ * ψ θ) θ) →
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, ψ θ = Real.exp (κ * (θ - 1)))

/-- S1: G embeds the node model as the Poisson edge model. -/
@[sa_shadow "Docs.cf.poissonUniqueSection" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ), poissonLift (nodeModel p κ) = edgeModel p (PGFData.poisson κ hκ)
/-- S2: the susceptible curves match after reparametrisation. -/
@[sa_shadow "Docs.cf.poissonUniqueSection" 2]
def S2 : Prop := SMatch
/-- S3: the infected curves differ. -/
@[sa_shadow "Docs.cf.poissonUniqueSection" 3]
def S3 : Prop := IDiffer
/-- S4: only the Poisson PGF gives mass-action dynamics for S. -/
@[sa_shadow "Docs.cf.poissonUniqueSection" 4]
def S4 : Prop :=
  ∀ (ψ : ℝ → ℝ) (κ : ℝ), ψ 1 = 1 → (∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ψ (κ * ψ θ) θ) →
    ∀ θ ∈ Set.Icc (0 : ℝ) 1, ψ θ = Real.exp (κ * (θ - 1))

@[sa_ref_forward "Docs.cf.poissonUniqueSection" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.poissonUniqueSection" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.cf.poissonUniqueSection" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Docs.cf.poissonUniqueSection" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "Docs.cf.poissonUniqueSection"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.Docs.cf_poissonUniqueSection

/-! ## `Docs.cf.subcategoryInclusions` (blind)

Text: "Each restriction narrows the class of models (informally a subcategory inclusion; no category
is defined)."

-- AMBIGUITY: read over the validity records of `Obstructions` (§5.4): the class where the standard
EBCM is valid is contained in the class where some EBCM variant exists (S1), strictly (S2). -/
namespace Alignment.Shadows.Docs.cf_subcategoryInclusions

@[sa_reference "Docs.cf.subcategoryInclusions"]
def T : Prop :=
  (∀ (n : NetworkType) (t : TransitionType) (i : InitCondType),
      standardEbcmValid n t i → ebcmExists n t i) ∧
  (∃ (n : NetworkType) (t : TransitionType) (i : InitCondType),
      ebcmExists n t i ∧ ¬ standardEbcmValid n t i)

/-- S1: the restricted class is contained in the larger one. -/
@[sa_shadow "Docs.cf.subcategoryInclusions" 1]
def S1 : Prop :=
  ∀ (n : NetworkType) (t : TransitionType) (i : InitCondType),
    standardEbcmValid n t i → ebcmExists n t i
/-- S2: the restriction is proper. -/
@[sa_shadow "Docs.cf.subcategoryInclusions" 2]
def S2 : Prop :=
  ∃ (n : NetworkType) (t : TransitionType) (i : InitCondType),
    ebcmExists n t i ∧ ¬ standardEbcmValid n t i

@[sa_ref_forward "Docs.cf.subcategoryInclusions" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.subcategoryInclusions" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Docs.cf.subcategoryInclusions"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Docs.cf_subcategoryInclusions

/-! ## `Docs.cf.thm3_2` (re-authored blind)

Text: "**Theorem 3.2.** F is not injective on EBCM states: distinct EBCM states (θ, φ, R, ψ) can
have the same image (S, I, R), because F forgets φ and all of ψ except its value at θ. Whether
distinct EBCM *trajectories* can project to identical node-level trajectories is not established
here."

-- AMBIGUITY: two readings. State level (S1): single-type states (θ, φ, R, ψ) with
F(θ, φ, R, ψ) = (ψ(θ), 1 − ψ(θ) − R, R) (§3.1); F is not injective. Record level (S2): the Lean F,
`coarseGrain`, is not injective. The last sentence states an open question. -/
namespace Alignment.Shadows.Docs.cf_thm3_2

/-- F on single-type EBCM states `(θ, φ, R, ψ)`. -/
def Fstate (s : ℝ × ℝ × ℝ × (ℝ → ℝ)) : ℝ × ℝ × ℝ :=
  (s.2.2.2 s.1, 1 - s.2.2.2 s.1 - s.2.2.1, s.2.2.1)

@[sa_reference "Docs.cf.thm3_2"]
def T : Prop := ¬ Function.Injective Fstate ∧ ¬ Function.Injective coarseGrain

/-- S1: F is not injective on EBCM states. -/
@[sa_shadow "Docs.cf.thm3_2" 1]
def S1 : Prop := ¬ Function.Injective Fstate
/-- S2: `coarseGrain` is not injective. -/
@[sa_shadow "Docs.cf.thm3_2" 2]
def S2 : Prop := ¬ Function.Injective coarseGrain

@[sa_ref_forward "Docs.cf.thm3_2" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.thm3_2" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Docs.cf.thm3_2"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Docs.cf_thm3_2

/-! ## `Docs.cf.thm3_3-lostInformation` (blind)

Text: "The node-level trajectory does not determine ψ, but it retains more than the first moment: for
instance its early growth rate depends on ψ''(1)/ψ'(1). So the lost information is not simply the
degree distribution beyond its mean."

The early growth rate of the (correct) EBCM near the disease-free state is
`r = β̃·ψ''(1)/ψ'(1) − (β̃ + γ̃)` (linearising `φ̇_I = βφ_Iψ″(θ)/ψ′(1) − (β+γ)φ_I` at θ = 1). S1: at
equal mean degree, degree records with different ψ''(1) have different early growth rates.
"Does not determine ψ" is not formalised (it concerns whole trajectories). -/
namespace Alignment.Shadows.Docs.cf_thm3_3_lostInformation

/-- Early growth rate `β̃·ψ''(1)/ψ'(1) − (β̃ + γ̃)`. -/
def growth (p : SIRParams) (ψ : PGFData) : ℚ := p.β * ψ.excessDegree - (p.β + p.γ)

@[sa_reference "Docs.cf.thm3_3-lostInformation"]
def T : Prop :=
  ∀ (p : SIRParams) (ψ₁ ψ₂ : PGFData), ψ₁.mean = ψ₂.mean →
    ψ₁.secondFactorial ≠ ψ₂.secondFactorial → growth p ψ₁ ≠ growth p ψ₂

/-- S1: the early growth rate depends on ψ''(1)/ψ'(1), not only on the mean. -/
@[sa_shadow "Docs.cf.thm3_3-lostInformation" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (ψ₁ ψ₂ : PGFData), ψ₁.mean = ψ₂.mean →
    ψ₁.secondFactorial ≠ ψ₂.secondFactorial → growth p ψ₁ ≠ growth p ψ₂

@[sa_ref_forward "Docs.cf.thm3_3-lostInformation" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Docs.cf.thm3_3-lostInformation"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Docs.cf_thm3_3_lostInformation

/-! ## `Docs.cf.thm4_1` (blind)

Text: "**Theorem 4.1 (corrected).** F and G are not a Galois connection for the dimension preorder
(M₁ ≤ M₂ iff dim M₁ ≤ dim M₂) used in the Lean library: the condition [...] F(E) ≤ N ⟺ E ≤ G(N)
[...] fails for E = ⟨10, r⟩ and N = ⟨3, r⟩, where F(E) ≤ N holds but E ≤ G(N) does not
(`not_galoisConnection_coarseGrain_poissonLift`)." -/
namespace Alignment.Shadows.Docs.cf_thm4_1

@[sa_reference "Docs.cf.thm4_1"]
def T : Prop :=
  (∀ M₁ M₂ : EpiModel, M₁ ≤ M₂ → M₁.dim ≤ M₂.dim) ∧ (∀ M₁ M₂ : EpiModel, M₁.dim ≤ M₂.dim → M₁ ≤ M₂) ∧
  ¬ GaloisConnection coarseGrain poissonLift ∧ (∀ r : ℚ, coarseGrain ⟨10, r⟩ ≤ ⟨3, r⟩) ∧
  (∀ r : ℚ, ¬ (⟨10, r⟩ : EpiModel) ≤ poissonLift ⟨3, r⟩)

/-- S1: the preorder is by dimension (→). -/
@[sa_shadow "Docs.cf.thm4_1" 1]
def S1 : Prop := ∀ M₁ M₂ : EpiModel, M₁ ≤ M₂ → M₁.dim ≤ M₂.dim
/-- S2: the preorder is by dimension (←). -/
@[sa_shadow "Docs.cf.thm4_1" 2]
def S2 : Prop := ∀ M₁ M₂ : EpiModel, M₁.dim ≤ M₂.dim → M₁ ≤ M₂
/-- S3: F and G are not a Galois connection. -/
@[sa_shadow "Docs.cf.thm4_1" 3]
def S3 : Prop := ¬ GaloisConnection coarseGrain poissonLift
/-- S4: `F⟨10, r⟩ ≤ ⟨3, r⟩`. -/
@[sa_shadow "Docs.cf.thm4_1" 4]
def S4 : Prop := ∀ r : ℚ, coarseGrain ⟨10, r⟩ ≤ ⟨3, r⟩
/-- S5: `⟨10, r⟩ ≤ G⟨3, r⟩` fails. -/
@[sa_shadow "Docs.cf.thm4_1" 5]
def S5 : Prop := ∀ r : ℚ, ¬ (⟨10, r⟩ : EpiModel) ≤ poissonLift ⟨3, r⟩

@[sa_ref_forward "Docs.cf.thm4_1" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.thm4_1" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.cf.thm4_1" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Docs.cf.thm4_1" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "Docs.cf.thm4_1" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2
@[sa_complete "Docs.cf.thm4_1"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.Docs.cf_thm4_1

/-! ## `Docs.cf.thm4_3` (re-authored blind)

Text: "**Theorem 4.3.** (a) ψ''(1)/ψ'(1) = ψ'(1) (excess degree equals mean degree) iff the degree
distribution has variance equal to its mean. (b) A Poisson degree distribution satisfies (a). (c) The
EBCM has mass-action form for S iff ψ' = κψ on [0, 1], i.e. iff the degree distribution is Poisson.
(a) does not imply Poisson: ψ(u) = (1 + u²)/2 satisfies (a) and is not Poisson."

(a), (b) on degree records (`excessDegree`, `variance`, `PGFData.poisson`). (c) The mass-action
form dS/dt = −(κβ̃)Sφ_I of dS/dt = −β̃ψ′(θ)φ_I (proof of (c)) means ψ′ = κψ on [0, 1]; with ψ(1) = 1
this forces the Poisson PGF (S5), and the Poisson PGF satisfies it (S6). Counterexample: S7, S8. -/
namespace Alignment.Shadows.Docs.cf_thm4_3

open Alignment.Shadows.Docs.Shared2

@[sa_reference "Docs.cf.thm4_3"]
def T : Prop :=
  (∀ ψ : PGFData, ψ.excessDegree = ψ.mean → ψ.variance = ψ.mean) ∧
  (∀ ψ : PGFData, ψ.variance = ψ.mean → ψ.excessDegree = ψ.mean) ∧
  (∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).excessDegree = (PGFData.poisson κ hκ).mean) ∧
  (∀ (ψ : ℝ → ℝ) (κ β : ℝ), 0 < β →
      ((∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ φ : ℝ, -β * deriv ψ θ * φ = -(κ * β) * ψ θ * φ) ↔
        ∀ θ ∈ Set.Icc (0 : ℝ) 1, deriv ψ θ = κ * ψ θ)) ∧
  (∀ (ψ : ℝ → ℝ) (κ : ℝ), ψ 1 = 1 → (∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ψ (κ * ψ θ) θ) →
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, ψ θ = Real.exp (κ * (θ - 1))) ∧
  (∀ κ θ : ℝ, HasDerivAt (fun x => Real.exp (κ * (x - 1))) (κ * Real.exp (κ * (θ - 1))) θ) ∧
  iteratedDeriv 2 psiMix 1 / deriv psiMix 1 = deriv psiMix 1 ∧
  (∀ lam : ℝ, psiMix ≠ fun u => Real.exp (lam * (u - 1)))

/-- S1: (a) →. -/
@[sa_shadow "Docs.cf.thm4_3" 1]
def S1 : Prop := ∀ ψ : PGFData, ψ.excessDegree = ψ.mean → ψ.variance = ψ.mean
/-- S2: (a) ←. -/
@[sa_shadow "Docs.cf.thm4_3" 2]
def S2 : Prop := ∀ ψ : PGFData, ψ.variance = ψ.mean → ψ.excessDegree = ψ.mean
/-- S3: (b) Poisson satisfies (a). -/
@[sa_shadow "Docs.cf.thm4_3" 3]
def S3 : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).excessDegree = (PGFData.poisson κ hκ).mean
/-- S4: (c) mass-action form for S iff ψ′ = κψ on [0, 1]. -/
@[sa_shadow "Docs.cf.thm4_3" 4]
def S4 : Prop :=
  ∀ (ψ : ℝ → ℝ) (κ β : ℝ), 0 < β →
    ((∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ φ : ℝ, -β * deriv ψ θ * φ = -(κ * β) * ψ θ * φ) ↔
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, deriv ψ θ = κ * ψ θ)
/-- S5: (c) ψ′ = κψ on [0, 1] and ψ(1) = 1 force the Poisson PGF. -/
@[sa_shadow "Docs.cf.thm4_3" 5]
def S5 : Prop :=
  ∀ (ψ : ℝ → ℝ) (κ : ℝ), ψ 1 = 1 → (∀ θ ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ψ (κ * ψ θ) θ) →
    ∀ θ ∈ Set.Icc (0 : ℝ) 1, ψ θ = Real.exp (κ * (θ - 1))
/-- S6: (c) the Poisson PGF satisfies ψ′ = κψ. -/
@[sa_shadow "Docs.cf.thm4_3" 6]
def S6 : Prop :=
  ∀ κ θ : ℝ, HasDerivAt (fun x => Real.exp (κ * (x - 1))) (κ * Real.exp (κ * (θ - 1))) θ
/-- S7: (1 + u²)/2 satisfies (a). -/
@[sa_shadow "Docs.cf.thm4_3" 7]
def S7 : Prop := iteratedDeriv 2 psiMix 1 / deriv psiMix 1 = deriv psiMix 1
/-- S8: (1 + u²)/2 is not Poisson. -/
@[sa_shadow "Docs.cf.thm4_3" 8]
def S8 : Prop := ∀ lam : ℝ, psiMix ≠ fun u => Real.exp (lam * (u - 1))

@[sa_ref_forward "Docs.cf.thm4_3" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.thm4_3" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.cf.thm4_3" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Docs.cf.thm4_3" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "Docs.cf.thm4_3" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2.1
@[sa_ref_forward "Docs.cf.thm4_3" 6] theorem ref_fwd6 : T → S6 := fun t => t.2.2.2.2.2.1
@[sa_ref_forward "Docs.cf.thm4_3" 7] theorem ref_fwd7 : T → S7 := fun t => t.2.2.2.2.2.2.1
@[sa_ref_forward "Docs.cf.thm4_3" 8] theorem ref_fwd8 : T → S8 := fun t => t.2.2.2.2.2.2.2
@[sa_complete "Docs.cf.thm4_3"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7) (s8 : S8) :
    T :=
  ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩

end Alignment.Shadows.Docs.cf_thm4_3

/-! ## `Docs.cf.thm4_3-massAction` (blind)

Text: "(c) With S = ψ(θ), dS/dt = ψ'(θ)·dθ/dt = −β̃ψ'(θ)φ_I, which equals −(κβ̃)·S·φ_I iff
ψ'(θ) = κψ(θ); then S(t) solves the mass-action equation with I := φ_I and rates β = κβ̃,
γ = β̃ + γ̃ (Rempała 2023)."

S1: the chain rule with θ̇ = −β̃φ_I; S2: the iff (for β̃ > 0 and φ_I ≠ 0); S3: for the Poisson PGF,
S(t) solves mass-action SIR with I := φ_I and the stated rates. -/
namespace Alignment.Shadows.Docs.cf_thm4_3_massAction

open Alignment.Shadows.Docs.Shared2

@[sa_reference "Docs.cf.thm4_3-massAction"]
def T : Prop :=
  (∀ (ψ ψ' θ φ : ℝ → ℝ) (β : ℝ) (t : ℝ), HasDerivAt ψ (ψ' (θ t)) (θ t) →
      HasDerivAt θ (-β * φ t) t → HasDerivAt (fun s => ψ (θ s)) (-β * ψ' (θ t) * φ t) t) ∧
  (∀ (β κ dψ Sv φ : ℝ), 0 < β → φ ≠ 0 → (-β * dψ * φ = -(κ * β) * Sv * φ ↔ dψ = κ * Sv)) ∧
  SMatch

/-- S1: dS/dt = ψ′(θ)·dθ/dt = −β̃ψ′(θ)φ_I. -/
@[sa_shadow "Docs.cf.thm4_3-massAction" 1]
def S1 : Prop :=
  ∀ (ψ ψ' θ φ : ℝ → ℝ) (β : ℝ) (t : ℝ), HasDerivAt ψ (ψ' (θ t)) (θ t) →
    HasDerivAt θ (-β * φ t) t → HasDerivAt (fun s => ψ (θ s)) (-β * ψ' (θ t) * φ t) t
/-- S2: it equals −(κβ̃)Sφ_I iff ψ′(θ) = κψ(θ). -/
@[sa_shadow "Docs.cf.thm4_3-massAction" 2]
def S2 : Prop :=
  ∀ (β κ dψ Sv φ : ℝ), 0 < β → φ ≠ 0 → (-β * dψ * φ = -(κ * β) * Sv * φ ↔ dψ = κ * Sv)
/-- S3: then S(t) solves mass-action SIR with I := φ_I, β = κβ̃, γ = β̃ + γ̃. -/
@[sa_shadow "Docs.cf.thm4_3-massAction" 3]
def S3 : Prop := SMatch

@[sa_ref_forward "Docs.cf.thm4_3-massAction" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.thm4_3-massAction" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.cf.thm4_3-massAction" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Docs.cf.thm4_3-massAction"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Docs.cf_thm4_3_massAction

/-! ## `Docs.cf.thm7_1` (blind)

Text: "**Theorem 7.1 (withdrawn).** It is not true that every SIR trajectory is reproduced exactly by
EBCMs with arbitrary PGFs ψ with ψ'(1) = κ: an EBCM with given ψ has only two rates (β̃, γ̃), which
cannot in general match an arbitrary curve S(t). The earlier proof defined θ(t) = ψ⁻¹(S(t)) but did
not check that θ(t) solves the EBCM θ-equation. What does hold is the Poisson lift of §4.1: for
Poisson ψ and κ > R₀ the EBCM reproduces the mass-action S(t) (Rempała 2023)."

S1: some PGF ψ (a power series Σ pₖuᵏ, pₖ ≥ 0, Σ pₖ = 1, ψ′(1) > 0) and some SIR trajectory are not
matched by any EBCM θ-equation `θ̇ = −β̃θ + β̃ψ′(θ)/ψ′(1) + γ̃(1−θ)` with S = ψ(θ). S2: for the
Poisson PGF and κ > R₀ = β/γ, the lifted EBCM reproduces the mass-action S(t). The remark on the
earlier proof is not formalised. -/
namespace Alignment.Shadows.Docs.cf_thm7_1

open Alignment.Shadows.Docs.Shared2

@[sa_reference "Docs.cf.thm7_1"]
def T : Prop :=
  (∃ (q : ℕ → ℝ) (β γ : ℝ) (S I : ℝ → ℝ),
      (∀ k, 0 ≤ q k) ∧ HasSum q 1 ∧ 0 < deriv (fun x => ∑' k, q k * x ^ k) 1 ∧ 0 < β ∧ 0 < γ ∧
      IsSIR β γ S I ∧
      ¬ ∃ (β' γ' : ℝ) (θ : ℝ → ℝ), 0 < β' ∧ 0 < γ' ∧
        (∀ t, HasDerivAt θ (-β' * θ t +
            β' * deriv (fun x => ∑' k, q k * x ^ k) (θ t) / deriv (fun x => ∑' k, q k * x ^ k) 1 +
            γ' * (1 - θ t)) t) ∧
        ∀ t, S t = ∑' k, q k * θ t ^ k) ∧
  (∀ (β γ κ : ℚ) (hβ : 0 < β) (hγ : 0 < γ) (hκ : 0 < κ) (h : β / γ < κ) (θ : ℝ → ℝ),
      (∀ t, HasDerivAt θ (ebcmRHS (liftParams β γ κ hβ hγ hκ h) κ (θ t)) t) →
      ∃ I : ℝ → ℝ, IsSIR (β : ℝ) (γ : ℝ) (fun t => Sof κ (θ t)) I)

/-- S1: some PGF and SIR trajectory are not reproduced by any EBCM with that PGF. -/
@[sa_shadow "Docs.cf.thm7_1" 1]
def S1 : Prop :=
  ∃ (q : ℕ → ℝ) (β γ : ℝ) (S I : ℝ → ℝ),
    (∀ k, 0 ≤ q k) ∧ HasSum q 1 ∧ 0 < deriv (fun x => ∑' k, q k * x ^ k) 1 ∧ 0 < β ∧ 0 < γ ∧
    IsSIR β γ S I ∧
    ¬ ∃ (β' γ' : ℝ) (θ : ℝ → ℝ), 0 < β' ∧ 0 < γ' ∧
      (∀ t, HasDerivAt θ (-β' * θ t +
          β' * deriv (fun x => ∑' k, q k * x ^ k) (θ t) / deriv (fun x => ∑' k, q k * x ^ k) 1 +
          γ' * (1 - θ t)) t) ∧
      ∀ t, S t = ∑' k, q k * θ t ^ k
/-- S2: the Poisson lift with κ > R₀ reproduces the mass-action S(t). -/
@[sa_shadow "Docs.cf.thm7_1" 2]
def S2 : Prop :=
  ∀ (β γ κ : ℚ) (hβ : 0 < β) (hγ : 0 < γ) (hκ : 0 < κ) (h : β / γ < κ) (θ : ℝ → ℝ),
    (∀ t, HasDerivAt θ (ebcmRHS (liftParams β γ κ hβ hγ hκ h) κ (θ t)) t) →
    ∃ I : ℝ → ℝ, IsSIR (β : ℝ) (γ : ℝ) (fun t => Sof κ (θ t)) I

@[sa_ref_forward "Docs.cf.thm7_1" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.thm7_1" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Docs.cf.thm7_1"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Docs.cf_thm7_1

/-! ## `Docs.cf.thm8_1-factor` (blind)

Text: "The ratio of the EBCM excess degree to the mean degree is
(ψ''(1)/ψ'(1))/κ = 1 + (σ²/κ - 1)/κ = (κ² − κ + σ²)/κ²." -/
namespace Alignment.Shadows.Docs.cf_thm8_1_factor

@[sa_reference "Docs.cf.thm8_1-factor"]
def T : Prop :=
  (∀ ψ : PGFData, ψ.excessDegree / ψ.mean = 1 + (ψ.dispersionIndex - 1) / ψ.mean) ∧
  (∀ ψ : PGFData, ψ.excessDegree / ψ.mean = (ψ.mean ^ 2 - ψ.mean + ψ.variance) / ψ.mean ^ 2)

/-- S1: the ratio is `1 + (σ²/κ − 1)/κ`. -/
@[sa_shadow "Docs.cf.thm8_1-factor" 1]
def S1 : Prop := ∀ ψ : PGFData, ψ.excessDegree / ψ.mean = 1 + (ψ.dispersionIndex - 1) / ψ.mean
/-- S2: the ratio is `(κ² − κ + σ²)/κ²`. -/
@[sa_shadow "Docs.cf.thm8_1-factor" 2]
def S2 : Prop :=
  ∀ ψ : PGFData, ψ.excessDegree / ψ.mean = (ψ.mean ^ 2 - ψ.mean + ψ.variance) / ψ.mean ^ 2

@[sa_ref_forward "Docs.cf.thm8_1-factor" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.thm8_1-factor" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Docs.cf.thm8_1-factor"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Docs.cf_thm8_1_factor

/-! ## `Docs.cf.thm8_1-poisson` (re-authored blind)

Text: "σ² = κ (e.g. Poisson): excess degree = mean degree; exact equivalence of S(t) with mass
action holds for Poisson degrees (Theorem 4.3(c)), not for every law with σ² = κ"

S1: σ² = κ ⇒ excess degree = mean (records); S2: Poisson records have σ² = κ; S3: exact
equivalence of S(t) for Poisson degrees; S4, S5: the law (1 + u²)/2 has σ² = κ (= 1) but not the
mass-action property ψ′ = κψ on [0, 1] required by Theorem 4.3(c). -/
namespace Alignment.Shadows.Docs.cf_thm8_1_poisson

open Alignment.Shadows.Docs.Shared2

@[sa_reference "Docs.cf.thm8_1-poisson"]
def T : Prop :=
  (∀ ψ : PGFData, ψ.variance = ψ.mean → ψ.excessDegree = ψ.mean) ∧
  (∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).variance = κ) ∧ SMatch ∧
  iteratedDeriv 2 psiMix 1 + deriv psiMix 1 - deriv psiMix 1 ^ 2 = deriv psiMix 1 ∧
  (∃ θ ∈ Set.Icc (0 : ℝ) 1, deriv psiMix θ ≠ deriv psiMix 1 * psiMix θ)

/-- S1: σ² = κ ⇒ excess degree = mean degree. -/
@[sa_shadow "Docs.cf.thm8_1-poisson" 1]
def S1 : Prop := ∀ ψ : PGFData, ψ.variance = ψ.mean → ψ.excessDegree = ψ.mean
/-- S2: Poisson has σ² = κ. -/
@[sa_shadow "Docs.cf.thm8_1-poisson" 2]
def S2 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).variance = κ
/-- S3: exact S(t) equivalence for Poisson degrees. -/
@[sa_shadow "Docs.cf.thm8_1-poisson" 3]
def S3 : Prop := SMatch
/-- S4: (1 + u²)/2 has σ² = κ. -/
@[sa_shadow "Docs.cf.thm8_1-poisson" 4]
def S4 : Prop := iteratedDeriv 2 psiMix 1 + deriv psiMix 1 - deriv psiMix 1 ^ 2 = deriv psiMix 1
/-- S5: (1 + u²)/2 violates ψ′ = κψ on [0, 1]. -/
@[sa_shadow "Docs.cf.thm8_1-poisson" 5]
def S5 : Prop := ∃ θ ∈ Set.Icc (0 : ℝ) 1, deriv psiMix θ ≠ deriv psiMix 1 * psiMix θ

@[sa_ref_forward "Docs.cf.thm8_1-poisson" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.thm8_1-poisson" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.cf.thm8_1-poisson" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Docs.cf.thm8_1-poisson" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "Docs.cf.thm8_1-poisson" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2
@[sa_complete "Docs.cf.thm8_1-poisson"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.Docs.cf_thm8_1_poisson

/-! ## `Docs.cf.validityDomain` (re-authored blind)

Text: "The ODE EBCM is exact for Markovian processes on configuration-model networks with uniform
(independent) seeding; the non-Markovian (PDE) EBCM extends this to general independent transmission
and recovery processes."

Vocabulary of `Obstructions`: S1 the standard (ODE) EBCM is valid for configuration model +
Markovian + uniform; S2 that case needs an ODE system; S3 general non-Markovian dynamics need the
PDE system; S4 and an EBCM variant exists for them. -/
namespace Alignment.Shadows.Docs.cf_validityDomain

@[sa_reference "Docs.cf.validityDomain"]
def T : Prop :=
  standardEbcmValid .configurationModel .markovian .uniform ∧
    systemRequired .markovian .uniform = .ode ∧ systemRequired .generalNonMarkov .uniform = .pde ∧
    ebcmExists .configurationModel .generalNonMarkov .uniform

/-- S1: the ODE EBCM is valid for CM + Markovian + uniform. -/
@[sa_shadow "Docs.cf.validityDomain" 1]
def S1 : Prop := standardEbcmValid .configurationModel .markovian .uniform
/-- S2: Markovian + uniform is an ODE system. -/
@[sa_shadow "Docs.cf.validityDomain" 2]
def S2 : Prop := systemRequired .markovian .uniform = .ode
/-- S3: general non-Markovian + uniform is the PDE system. -/
@[sa_shadow "Docs.cf.validityDomain" 3]
def S3 : Prop := systemRequired .generalNonMarkov .uniform = .pde
/-- S4: the non-Markovian EBCM exists on configuration models. -/
@[sa_shadow "Docs.cf.validityDomain" 4]
def S4 : Prop := ebcmExists .configurationModel .generalNonMarkov .uniform

@[sa_ref_forward "Docs.cf.validityDomain" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.cf.validityDomain" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.cf.validityDomain" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Docs.cf.validityDomain" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "Docs.cf.validityDomain"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.Docs.cf_validityDomain

/-! ## `Docs.ms.T1` (re-authored blind)

Text: "theorem dynamic_marginalisation_iff_equivariance (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄)
(F₃ : V₃ → V₃) {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃} (h₄ : IsFlow F₄ φ₄) (h₃ : IsFlow F₃ φ₃)
(uniq₃ : UniqueFlow F₃) : (∀ u, M (F₄ u) = F₃ (M u)) ↔ (∀ u t, M (φ₄ u t) = φ₃ (M u) t) [...]
Plain math: for global flows, and unique solutions of `F₃`, along trajectories
`M ∘ φ₄(·, t) = φ₃(M ·, t) ↔ RHS commute`." -/
namespace Alignment.Shadows.Docs.ms_T1

open EBCMCategory.Marginalisation

@[sa_reference "Docs.ms.T1"]
def T : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
    [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄)
    (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → UniqueFlow F₃ →
      ((∀ w, M (F₄ w) = F₃ (M w)) ↔ ∀ w t, M (φ₄ w t) = φ₃ (M w) t)

/-- S1: RHS commute ⇒ trajectories commute. -/
@[sa_shadow "Docs.ms.T1" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
    [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄)
    (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → UniqueFlow F₃ →
      (∀ w, M (F₄ w) = F₃ (M w)) → ∀ w t, M (φ₄ w t) = φ₃ (M w) t
/-- S2: trajectories commute ⇒ RHS commute. -/
@[sa_shadow "Docs.ms.T1" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
    [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄)
    (φ₃ : V₃ → ℝ → V₃), IsFlow F₄ φ₄ → IsFlow F₃ φ₃ → UniqueFlow F₃ →
      (∀ w t, M (φ₄ w t) = φ₃ (M w) t) → ∀ w, M (F₄ w) = F₃ (M w)

@[sa_ref_forward "Docs.ms.T1" 1] theorem ref_fwd1 : T.{u, v} → S1.{u, v} := by
  intro t V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h4 h3 hu
  exact (t M F₄ F₃ φ₄ φ₃ h4 h3 hu).1
@[sa_ref_forward "Docs.ms.T1" 2] theorem ref_fwd2 : T.{u, v} → S2.{u, v} := by
  intro t V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h4 h3 hu
  exact (t M F₄ F₃ φ₄ φ₃ h4 h3 hu).2
@[sa_complete "Docs.ms.T1"]
theorem complete (s1 : S1.{u, v}) (s2 : S2.{u, v}) : T.{u, v} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h4 h3 hu
  exact ⟨s1 M F₄ F₃ φ₄ φ₃ h4 h3 hu, s2 M F₄ F₃ φ₄ φ₃ h4 h3 hu⟩

end Alignment.Shadows.Docs.ms_T1

/-! ## `Docs.ms.T2` (re-authored blind)

Text: "theorem kirkwood_marginalisation_obstruction : ∃ (u4 : Order4Var → ℚ),
M_Q (F4_Kirkwood u4) ≠ F3_Kirkwood (M_Q u4) [...] We use a **concrete ℚ-valued surrogate** with
mnemonic labels: two order-4 entries (`a = C_4 SISI`, `b = C_4 SSSS` placeholder) and one order-3
entry (`c = P_3 SIS`); `M_Q(a,b) = a + b`; `F4_Kirkwood (a,b) = (a*b, b)`; `F3_Kirkwood c = c^2 / 4`.
In Lean the index types are `Idx4 = {a, b}` and `Idx3 = {c}`, not `Order4Var`/`Order3Var`."

Over the surrogate index types (as the text says the Lean statement uses): S1 the obstruction;
S2–S5 the surrogate formulas (`M_witness`, `F4_Kirkwood`, `F3_Kirkwood`). -/
namespace Alignment.Shadows.Docs.ms_T2

open MarginalisationObstruction

@[sa_reference "Docs.ms.T2"]
def T : Prop :=
  (∃ u : U4, M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u)) ∧
  (∀ u : U4, M_witness u Idx3.c = u Idx4.a + u Idx4.b) ∧
  (∀ u : U4, F4_Kirkwood u Idx4.a = u Idx4.a * u Idx4.b) ∧
  (∀ u : U4, F4_Kirkwood u Idx4.b = u Idx4.b) ∧
  (∀ v : U3, F3_Kirkwood v Idx3.c = v Idx3.c ^ 2 / 4)

/-- S1: some order-4 state where `M ∘ F₄ ≠ F₃ ∘ M`. -/
@[sa_shadow "Docs.ms.T2" 1]
def S1 : Prop := ∃ u : U4, M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u)
/-- S2: `M_Q(a,b) = a + b`. -/
@[sa_shadow "Docs.ms.T2" 2]
def S2 : Prop := ∀ u : U4, M_witness u Idx3.c = u Idx4.a + u Idx4.b
/-- S3: the a-component of `F4_Kirkwood` is `a·b`. -/
@[sa_shadow "Docs.ms.T2" 3]
def S3 : Prop := ∀ u : U4, F4_Kirkwood u Idx4.a = u Idx4.a * u Idx4.b
/-- S4: the b-component of `F4_Kirkwood` is `b`. -/
@[sa_shadow "Docs.ms.T2" 4]
def S4 : Prop := ∀ u : U4, F4_Kirkwood u Idx4.b = u Idx4.b
/-- S5: `F3_Kirkwood c = c²/4`. -/
@[sa_shadow "Docs.ms.T2" 5]
def S5 : Prop := ∀ v : U3, F3_Kirkwood v Idx3.c = v Idx3.c ^ 2 / 4

@[sa_ref_forward "Docs.ms.T2" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.ms.T2" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.ms.T2" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Docs.ms.T2" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "Docs.ms.T2" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2
@[sa_complete "Docs.ms.T2"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.Docs.ms_T2

/-! ## `Docs.ms.T2-smallestWitness` (blind)

Text: "It is one arithmetic witness for one pair of fields, not a general law: with `M = id` a
quadratic field commutes with itself, and at `u4 = (1, 3)` the quadratic field `c ↦ 3c²/8` agrees
with `M ∘ F4_Kirkwood`."

S1: with `M = id` on ℝ, `x ↦ x²` is equivariant with itself (`Equivariant`); S2: at `u4 = (1, 3)`
the ℚ surrogate satisfies `M(F4_Kirkwood u4) = (c ↦ 3c²/8)(M u4)`. -/
namespace Alignment.Shadows.Docs.ms_T2_smallestWitness

open EBCMCategory.MarginalisationCharacterization MarginalisationObstruction
open Alignment.Shadows.Docs.Shared2

@[sa_reference "Docs.ms.T2-smallestWitness"]
def T : Prop :=
  Equivariant (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (fun x => x ^ 2) (fun x => x ^ 2) ∧
    M_witness (F4_Kirkwood wQ) = (fun _ => 3 * M_witness wQ Idx3.c ^ 2 / 8)

/-- S1: with `M = id` a quadratic field commutes with itself. -/
@[sa_shadow "Docs.ms.T2-smallestWitness" 1]
def S1 : Prop := Equivariant (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (fun x => x ^ 2) (fun x => x ^ 2)
/-- S2: at `(1, 3)`, `c ↦ 3c²/8` agrees with `M ∘ F4_Kirkwood`. -/
@[sa_shadow "Docs.ms.T2-smallestWitness" 2]
def S2 : Prop := M_witness (F4_Kirkwood wQ) = (fun _ => 3 * M_witness wQ Idx3.c ^ 2 / 8)

@[sa_ref_forward "Docs.ms.T2-smallestWitness" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.ms.T2-smallestWitness" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Docs.ms.T2-smallestWitness"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Docs.ms_T2_smallestWitness

/-! ## `Docs.ms.T3` (re-authored blind)

Text: "theorem kirkwood_form_not_equivariant : ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄)
(_ : AddCommGroup V₃) (_ : Module ℝ V₄) (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃)
(C₄ : ClosureFamily V₄), C₄.IsKirkwoodForm ∧ ∀ (C₃ : ClosureFamily V₃), ¬ Equivariant M C₄.C C₃.C
[...] Plain math: T3 is the existential statement T3b. There is a linear `M` and a non-additive
order-4 field `C₄` such that no order-3 field `C₃` satisfies `M ∘ C₄ = C₃ ∘ M` (the witness of T2,
over ℝ)."

S1: the quoted statement; S2: the plain-math reading (literally non-additive, `M ∘ C₄ = C₃ ∘ M`
written out); S3: the witness is T2's over ℝ (`MℝLin`, `C4ℝ`). -/
namespace Alignment.Shadows.Docs.ms_T3

open EBCMCategory.Marginalisation EBCMCategory.MarginalisationCharacterization

@[sa_reference "Docs.ms.T3"]
def T : Prop :=
  (∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
      (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      C₄.IsKirkwoodForm ∧ ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M C₄.C C₃.C) ∧
  (∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
      (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
      (¬ ∀ x y, C₄.C (x + y) = C₄.C x + C₄.C y) ∧
        ∀ C₃ : ClosureFamily V₃, ¬ ∀ w, M (C₄.C w) = C₃.C (M w)) ∧
  (C4ℝ.IsKirkwoodForm ∧ ∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin C4ℝ.C C₃.C)

/-- S1: the quoted existential statement. -/
@[sa_shadow "Docs.ms.T3" 1]
def S1 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    C₄.IsKirkwoodForm ∧ ∀ C₃ : ClosureFamily V₃, ¬ Equivariant M C₄.C C₃.C
/-- S2: plain math: a non-additive `C₄` with no `C₃` satisfying `M ∘ C₄ = C₃ ∘ M`. -/
@[sa_shadow "Docs.ms.T3" 2]
def S2 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄),
    (¬ ∀ x y, C₄.C (x + y) = C₄.C x + C₄.C y) ∧
      ∀ C₃ : ClosureFamily V₃, ¬ ∀ w, M (C₄.C w) = C₃.C (M w)
/-- S3: the witness is T2's surrogate over ℝ. -/
@[sa_shadow "Docs.ms.T3" 3]
def S3 : Prop := C4ℝ.IsKirkwoodForm ∧ ∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin C4ℝ.C C₃.C

@[sa_ref_forward "Docs.ms.T3" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.ms.T3" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.ms.T3" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Docs.ms.T3"] theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Docs.ms_T3

/-! ## `Docs.ms.T3-kkr` (re-authored blind)

Text: "the Kiss–Kenah–Rempala conditions ensure `F_3` is exact at the *unclosed limit* (κ constant)
but place no constraint on the order-4 closure used to define `F_4`. T3c records only that a degree
record with `closureKappa = 1` can be paired with the non-equivariant surrogate of T3b; the two are
unrelated data."

S1: a degree record with `closureKappa = 1` exists (e.g. Poisson); S2: the T3b surrogate
(`C4ℝ` under `MℝLin`) is non-equivariant. "Place no constraint" / "unrelated data" are remarks. -/
namespace Alignment.Shadows.Docs.ms_T3_kkr

open EBCMCategory.MarginalisationCharacterization

@[sa_reference "Docs.ms.T3-kkr"]
def T : Prop :=
  (∃ ψ : PGFData, ψ.closureKappa = 1) ∧ ∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin C4ℝ.C C₃.C

/-- S1: some degree record has `closureKappa = 1`. -/
@[sa_shadow "Docs.ms.T3-kkr" 1]
def S1 : Prop := ∃ ψ : PGFData, ψ.closureKappa = 1
/-- S2: the T3b surrogate is non-equivariant. -/
@[sa_shadow "Docs.ms.T3-kkr" 2]
def S2 : Prop := ∀ C₃ : ClosureFamily U3ℝ, ¬ Equivariant MℝLin C4ℝ.C C₃.C

@[sa_ref_forward "Docs.ms.T3-kkr" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.ms.T3-kkr" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Docs.ms.T3-kkr"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Docs.ms_T3_kkr

/-! ## `Docs.ms.T3-linearEquivariant` (re-authored blind)

Text: "For a linear `L₄` this reads `L₄(ker M) ⊆ ker M` (`linear_admits_equivariant_iff`), so
linear closures are not equivariant for every `M`."

"This" is the fibre criterion: some `C₃` makes the diagram commute. S1, S2: for linear `L₄`,
`(∃ F₃, Equivariant M L₄ F₃) ↔ L₄(ker M) ⊆ ker M`; S3: some linear `L₄` and `M` admit no
equivariant `F₃`. -/
namespace Alignment.Shadows.Docs.ms_T3_linearEquivariant

open EBCMCategory.MarginalisationCharacterization

@[sa_reference "Docs.ms.T3-linearEquivariant"]
def T : Prop :=
  (∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
      (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
      (∃ F₃ : V₃ → V₃, Equivariant M L₄ F₃) → (LinearMap.ker M).map L₄ ≤ LinearMap.ker M) ∧
  (∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
      (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
      (LinearMap.ker M).map L₄ ≤ LinearMap.ker M → ∃ F₃ : V₃ → V₃, Equivariant M L₄ F₃) ∧
  (∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
      (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
      ¬ ∃ F₃ : V₃ → V₃, Equivariant M L₄ F₃)

/-- S1 (→). -/
@[sa_shadow "Docs.ms.T3-linearEquivariant" 1]
def S1 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
    (∃ F₃ : V₃ → V₃, Equivariant M L₄ F₃) → (LinearMap.ker M).map L₄ ≤ LinearMap.ker M
/-- S2 (←). -/
@[sa_shadow "Docs.ms.T3-linearEquivariant" 2]
def S2 : Prop :=
  ∀ {V₄ : Type u} {V₃ : Type v} [AddCommGroup V₄] [AddCommGroup V₃] [Module ℝ V₄] [Module ℝ V₃]
    (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
    (LinearMap.ker M).map L₄ ≤ LinearMap.ker M → ∃ F₃ : V₃ → V₃, Equivariant M L₄ F₃
/-- S3: linear closures are not equivariant for every `M`. -/
@[sa_shadow "Docs.ms.T3-linearEquivariant" 3]
def S3 : Prop :=
  ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄)
    (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (L₄ : V₄ →ₗ[ℝ] V₄),
    ¬ ∃ F₃ : V₃ → V₃, Equivariant M L₄ F₃

@[sa_ref_forward "Docs.ms.T3-linearEquivariant" 1] theorem ref_fwd1 : T.{u, v} → S1.{u, v} :=
  fun t => t.1
@[sa_ref_forward "Docs.ms.T3-linearEquivariant" 2] theorem ref_fwd2 : T.{u, v} → S2.{u, v} :=
  fun t => t.2.1
@[sa_ref_forward "Docs.ms.T3-linearEquivariant" 3] theorem ref_fwd3 : T.{u, v} → S3 :=
  fun t => t.2.2
@[sa_complete "Docs.ms.T3-linearEquivariant"]
theorem complete (s1 : S1.{u, v}) (s2 : S2.{u, v}) (s3 : S3) : T.{u, v} := ⟨s1, s2, s3⟩

end Alignment.Shadows.Docs.ms_T3_linearEquivariant

/-! ## `Docs.ms.T5-rateTwo` (re-authored blind)

Text: "For *any* local solutions ψ₄ of F4Kℝ from u₁ and ψ₃ of F3Kℝ from M u₁, the gap
`t ↦ M(ψ₄ t) − ψ₃ t` has first-order rate exactly 2 (`witness_localGap_hasDerivAt`), and such local
solutions exist (`witness_local_solutions_exist`)." -/
namespace Alignment.Shadows.Docs.ms_T5_rateTwo

open EBCMCategory.MarginalisationCharacterization EBCMCategory.MarginalisationDynamicalGap
open Alignment.Shadows.Docs.Shared2

@[sa_reference "Docs.ms.T5-rateTwo"]
def T : Prop :=
  (∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
      HasDerivAt (fun t => MℝLinCLM (ψ₄ t) - ψ₃ t) (cst 2) 0) ∧
  (∃ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ ∧ LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃)

/-- S1: the gap has first-order rate exactly 2. -/
@[sa_shadow "Docs.ms.T5-rateTwo" 1]
def S1 : Prop :=
  ∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
    HasDerivAt (fun t => MℝLinCLM (ψ₄ t) - ψ₃ t) (cst 2) 0
/-- S2: such local solutions exist. -/
@[sa_shadow "Docs.ms.T5-rateTwo" 2]
def S2 : Prop :=
  ∃ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ ∧ LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃

@[sa_ref_forward "Docs.ms.T5-rateTwo" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.ms.T5-rateTwo" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Docs.ms.T5-rateTwo"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Docs.ms_T5_rateTwo

/-! ## `Docs.ms.T5-witnessGap` (re-authored blind)

Text: "**Specialisation to the (2,1) witness** (`algebraicGap_at_witness`):
`algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = fun _ => 2`." -/
namespace Alignment.Shadows.Docs.ms_T5_witnessGap

open EBCMCategory.MarginalisationCharacterization EBCMCategory.MarginalisationDynamicalGap

@[sa_reference "Docs.ms.T5-witnessGap"]
def T : Prop := algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = fun _ => 2

/-- S1: the algebraic gap at the witness is 2. -/
@[sa_shadow "Docs.ms.T5-witnessGap" 1]
def S1 : Prop := algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = fun _ => 2

@[sa_ref_forward "Docs.ms.T5-witnessGap" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Docs.ms.T5-witnessGap"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Docs.ms_T5_witnessGap

/-! ## `Docs.ms.T6-phaseReversal` (blind)

Text: "Here "exact" means only agreement with the fitted constant `F3_exact = 6`. T6 is one
surrogate witness and says nothing about the empirical phase reversal. T3b (via T4) shows that no
order-3 field commutes with F4Kℝ under MℝLin at every state; at the single state u₁ the non-additive
field `c ↦ 3c²/8` does match (`kirkwoodForm_matches_at_witness`)."

S1: at `u₁`, `MℝLin (F4Kℝ u₁)` is the fitted constant 6 (the meaning of "exact"); S2: no order-3
field commutes with `F4Kℝ` under `MℝLin` at every state; S3, S4: at `u₁` the non-additive field
`c ↦ 3c²/8` matches. The remark about the empirical phase reversal is not formalised. -/
namespace Alignment.Shadows.Docs.ms_T6_phaseReversal

open EBCMCategory.MarginalisationCharacterization EBCMCategory.MarginalisationDynamicalGap
open Alignment.Shadows.Docs.Shared2

@[sa_reference "Docs.ms.T6-phaseReversal"]
def T : Prop :=
  MℝLin (F4Kℝ u₁) = cst 6 ∧ (∀ F₃ : U3ℝ → U3ℝ, ¬ ∀ w : U4ℝ, MℝLin (F4Kℝ w) = F₃ (MℝLin w)) ∧
    (ClosureFamily.mk C3match).IsKirkwoodForm ∧ MℝLin (F4Kℝ u₁) = C3match (MℝLin u₁)

/-- S1: "exact" = agreement with the fitted constant 6. -/
@[sa_shadow "Docs.ms.T6-phaseReversal" 1]
def S1 : Prop := MℝLin (F4Kℝ u₁) = cst 6
/-- S2: no order-3 field commutes with F4Kℝ at every state. -/
@[sa_shadow "Docs.ms.T6-phaseReversal" 2]
def S2 : Prop := ∀ F₃ : U3ℝ → U3ℝ, ¬ ∀ w : U4ℝ, MℝLin (F4Kℝ w) = F₃ (MℝLin w)
/-- S3: `c ↦ 3c²/8` is non-additive. -/
@[sa_shadow "Docs.ms.T6-phaseReversal" 3]
def S3 : Prop := (ClosureFamily.mk C3match).IsKirkwoodForm
/-- S4: it matches at `u₁`. -/
@[sa_shadow "Docs.ms.T6-phaseReversal" 4]
def S4 : Prop := MℝLin (F4Kℝ u₁) = C3match (MℝLin u₁)

@[sa_ref_forward "Docs.ms.T6-phaseReversal" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.ms.T6-phaseReversal" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.ms.T6-phaseReversal" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Docs.ms.T6-phaseReversal" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "Docs.ms.T6-phaseReversal"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.Docs.ms_T6_phaseReversal

/-! ## `Docs.ms.T7-witness` (blind)

Text: "At the (2,1) witness the global-flow form is vacuous (F3Kℝ has no global flow). The local
form `localGap_norm_ge_half_eps_t` assumes only local solutions, and at the witness
(`witness_localGap_ge`, ε = 2) it gives `‖M(ψ₄ t) − ψ₃ t‖ ≥ t` for all small `t > 0`, for any local
solutions ψ₄ of F4Kℝ from u₁ and ψ₃ of F3Kℝ from M u₁."

S1: F3Kℝ has no global flow; S2: the local form (general fields, local solutions only):
`‖algebraicGap‖ ≥ ε > 0` ⇒ `‖M(ψ₄ t) − ψ₃ t‖ ≥ εt/2` for small `t > 0`; S3: at the witness,
`‖M(ψ₄ t) − ψ₃ t‖ ≥ t` for small `t > 0`. -/
namespace Alignment.Shadows.Docs.ms_T7_witness

open EBCMCategory.Marginalisation EBCMCategory.MarginalisationCharacterization
open EBCMCategory.MarginalisationDynamicalGap Filter Topology
open Alignment.Shadows.Docs.Shared2

@[sa_reference "Docs.ms.T7-witness"]
def T : Prop :=
  (∀ φ₃ : U3ℝ → ℝ → U3ℝ, ¬ IsFlow F3Kℝ φ₃) ∧
  (∀ {V₄ V₃ : Type} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
      [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (w : V₄) (ε : ℝ)
      (ψ₄ : ℝ → V₄) (ψ₃ : ℝ → V₃), 0 < ε → ε ≤ ‖algebraicGap M F₄ F₃ w‖ →
      LocalSol F₄ w ψ₄ → LocalSol F₃ (M w) ψ₃ →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ε * t / 2 ≤ ‖M (ψ₄ t) - ψ₃ t‖) ∧
  (∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ ‖MℝLinCLM (ψ₄ t) - ψ₃ t‖)

/-- S1: the global-flow form is vacuous: F3Kℝ has no flow. -/
@[sa_shadow "Docs.ms.T7-witness" 1]
def S1 : Prop := ∀ φ₃ : U3ℝ → ℝ → U3ℝ, ¬ IsFlow F3Kℝ φ₃
/-- S2: the local form of T7. -/
@[sa_shadow "Docs.ms.T7-witness" 2]
def S2 : Prop :=
  ∀ {V₄ V₃ : Type} [NormedAddCommGroup V₄] [NormedSpace ℝ V₄] [NormedAddCommGroup V₃]
    [NormedSpace ℝ V₃] (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) (w : V₄) (ε : ℝ)
    (ψ₄ : ℝ → V₄) (ψ₃ : ℝ → V₃), 0 < ε → ε ≤ ‖algebraicGap M F₄ F₃ w‖ →
    LocalSol F₄ w ψ₄ → LocalSol F₃ (M w) ψ₃ →
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ε * t / 2 ≤ ‖M (ψ₄ t) - ψ₃ t‖
/-- S3: at the witness, `‖M(ψ₄ t) − ψ₃ t‖ ≥ t` for small `t > 0`. -/
@[sa_shadow "Docs.ms.T7-witness" 3]
def S3 : Prop :=
  ∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
    ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ ‖MℝLinCLM (ψ₄ t) - ψ₃ t‖

@[sa_ref_forward "Docs.ms.T7-witness" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.ms.T7-witness" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.ms.T7-witness" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Docs.ms.T7-witness"] theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T :=
  ⟨s1, s2, s3⟩

end Alignment.Shadows.Docs.ms_T7_witness

/-! ## `Docs.ms.flowDef` (blind)

Text: "**Flow:** `IsFlow F φ` ↔ `(∀ v, φ v 0 = v) ∧ ∀ v t, HasDerivAt (φ v) (F (φ v t)) t`.
Existence and uniqueness are *hypotheses* on the systems, not derived. `IsFlow` asks for solutions on
all of `ℝ`, so a field whose solutions blow up in finite time has no flow: `F3Kℝ` (`c ↦ c²/4`) has
none (`no_flow_F3Kℝ`)."

S1, S2: the two directions of the characterisation of `IsFlow`; S3: `F3Kℝ` has no flow.
"Hypotheses, not derived" is a remark about the theorems. -/
namespace Alignment.Shadows.Docs.ms_flowDef

open EBCMCategory.Marginalisation EBCMCategory.MarginalisationCharacterization
open EBCMCategory.MarginalisationDynamicalGap

@[sa_reference "Docs.ms.flowDef"]
def T : Prop :=
  (∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → V) (φ : V → ℝ → V),
      IsFlow F φ → (∀ w, φ w 0 = w) ∧ ∀ w t, HasDerivAt (φ w) (F (φ w t)) t) ∧
  (∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → V) (φ : V → ℝ → V),
      ((∀ w, φ w 0 = w) ∧ ∀ w t, HasDerivAt (φ w) (F (φ w t)) t) → IsFlow F φ) ∧
  (∀ φ₃ : U3ℝ → ℝ → U3ℝ, ¬ IsFlow F3Kℝ φ₃)

/-- S1: a flow starts at the identity and solves `F` at all times. -/
@[sa_shadow "Docs.ms.flowDef" 1]
def S1 : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → V) (φ : V → ℝ → V),
    IsFlow F φ → (∀ w, φ w 0 = w) ∧ ∀ w t, HasDerivAt (φ w) (F (φ w t)) t
/-- S2: conversely, such a φ is a flow. -/
@[sa_shadow "Docs.ms.flowDef" 2]
def S2 : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → V) (φ : V → ℝ → V),
    ((∀ w, φ w 0 = w) ∧ ∀ w t, HasDerivAt (φ w) (F (φ w t)) t) → IsFlow F φ
/-- S3: `F3Kℝ` has no flow. -/
@[sa_shadow "Docs.ms.flowDef" 3]
def S3 : Prop := ∀ φ₃ : U3ℝ → ℝ → U3ℝ, ¬ IsFlow F3Kℝ φ₃

@[sa_ref_forward "Docs.ms.flowDef" 1] theorem ref_fwd1 : T.{u} → S1.{u} := fun t => t.1
@[sa_ref_forward "Docs.ms.flowDef" 2] theorem ref_fwd2 : T.{u} → S2.{u} := fun t => t.2.1
@[sa_ref_forward "Docs.ms.flowDef" 3] theorem ref_fwd3 : T.{u} → S3 := fun t => t.2.2
@[sa_complete "Docs.ms.flowDef"]
theorem complete (s1 : S1.{u}) (s2 : S2.{u}) (s3 : S3) : T.{u} := ⟨s1, s2, s3⟩

end Alignment.Shadows.Docs.ms_flowDef

/-! ## `Docs.ms.flowHypothesised` (blind)

Text: "**ODE flow existence/uniqueness** is *hypothesised*, not derived. Picard–Lindelöf gives only
local existence for `C¹` `F`; global flows (`IsFlow`) need not exist, and for `F3Kℝ` they do not
(`no_flow_F3Kℝ`)."

S1: `F3Kℝ` is `C¹`; S2: local solutions of `F3Kℝ` exist through every state; S3: it has no global
flow. That existence is hypothesised is a remark about the theorems. -/
namespace Alignment.Shadows.Docs.ms_flowHypothesised

open EBCMCategory.Marginalisation EBCMCategory.MarginalisationCharacterization
open EBCMCategory.MarginalisationDynamicalGap
open Alignment.Shadows.Docs.Shared2

@[sa_reference "Docs.ms.flowHypothesised"]
def T : Prop :=
  ContDiff ℝ 1 F3Kℝ ∧ (∀ w : U3ℝ, ∃ ψ : ℝ → U3ℝ, LocalSol F3Kℝ w ψ) ∧
    ∀ φ₃ : U3ℝ → ℝ → U3ℝ, ¬ IsFlow F3Kℝ φ₃

/-- S1: `F3Kℝ` is `C¹`. -/
@[sa_shadow "Docs.ms.flowHypothesised" 1]
def S1 : Prop := ContDiff ℝ 1 F3Kℝ
/-- S2: local solutions exist through every state. -/
@[sa_shadow "Docs.ms.flowHypothesised" 2]
def S2 : Prop := ∀ w : U3ℝ, ∃ ψ : ℝ → U3ℝ, LocalSol F3Kℝ w ψ
/-- S3: no global flow. -/
@[sa_shadow "Docs.ms.flowHypothesised" 3]
def S3 : Prop := ∀ φ₃ : U3ℝ → ℝ → U3ℝ, ¬ IsFlow F3Kℝ φ₃

@[sa_ref_forward "Docs.ms.flowHypothesised" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Docs.ms.flowHypothesised" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Docs.ms.flowHypothesised" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Docs.ms.flowHypothesised"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Docs.ms_flowHypothesised

end
