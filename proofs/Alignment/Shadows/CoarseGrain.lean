import Alignment.Registry
import EBCMCategory.CoarseGrain

/-!
# Blind shadow sets: group `CoarseGrain`

Written blind: the author read only the claims' entries in `claims_blind.yaml`,
`Alignment/DataTypes/CoarseGrain.md`, `Alignment/README.md`, `SA-PASS_SKILL.md`,
`Example/ExampleShadows.lean` and (for the meaning of "excess degree") `papers/*.md`.
Types of the listed data types and operations were learned with `#check` only.

Vocabulary (from `DataTypes/CoarseGrain.md`):
* `F` = `coarseGrain : EpiModel → EpiModel`;
* refinement = the `Preorder` instance on `EpiModel` (written `≤`);
* `R₀` = the field `EpiModel.R0`;
* for `ψ : PGFData`: `ψ'(1)` = `ψ.mean` (= κ), `ψ''(1)` = `ψ.secondFactorial`,
  σ² = `ψ.variance`, the excess degree ratio = `ψ.excessDegree` (docstring: ψ''(1)/ψ'(1)),
  the index of dispersion = `ψ.dispersionIndex` (docstring: σ²/κ);
* "Poisson" = `PGFData.poisson κ hκ` (the Poisson PGF with mean κ, for every κ > 0).
-/

/-! ## `CoarseGrain.table.R5` -- "| 5 | F is a monotone map (preserves refinement) |" -/
namespace Alignment.Shadows.CoarseGrain.table_R5

/-- Intended statement: `F` is monotone for the refinement preorder on models. -/
@[sa_reference "CoarseGrain.table.R5"]
def T : Prop := Monotone coarseGrain

/-- S1: `F` preserves refinement: `m ≤ m'` implies `F m ≤ F m'`, for all models. -/
@[sa_shadow "CoarseGrain.table.R5" 1]
def S1 : Prop := ∀ m m' : EpiModel, m ≤ m' → coarseGrain m ≤ coarseGrain m'

@[sa_ref_forward "CoarseGrain.table.R5" 1]
theorem ref_fwd1 : T → S1 := fun t _ _ h => t h

@[sa_complete "CoarseGrain.table.R5"]
theorem complete (s1 : S1) : T := fun m m' h => s1 m m' h

end Alignment.Shadows.CoarseGrain.table_R5

/-! ## `CoarseGrain.table.R6` -- "| 6 | F is not injective (lossy) |" -/
namespace Alignment.Shadows.CoarseGrain.table_R6

-- AMBIGUITY: "not injective (lossy)" read literally as `¬ Function.Injective F`. The witness
-- reading "there are two distinct models with the same image" is classically equivalent;
-- "(lossy)" is treated as a gloss on non-injectivity and not required as a separate
-- (constructively stronger) shadow.

/-- Intended statement: `F` is not injective. -/
@[sa_reference "CoarseGrain.table.R6"]
def T : Prop := ¬ Function.Injective coarseGrain

/-- S1: it is not the case that `F m = F m'` always forces `m = m'`. -/
@[sa_shadow "CoarseGrain.table.R6" 1]
def S1 : Prop := ¬ (∀ m m' : EpiModel, coarseGrain m = coarseGrain m' → m = m')

@[sa_ref_forward "CoarseGrain.table.R6" 1]
theorem ref_fwd1 : T → S1 := fun t hinj => t (fun m m' h => hinj m m' h)

@[sa_complete "CoarseGrain.table.R6"]
theorem complete (s1 : S1) : T := fun hinj => s1 (fun _ _ h => hinj h)

end Alignment.Shadows.CoarseGrain.table_R6

/-! ## `CoarseGrain.table.R7` -- "| 7 | Degree-variance inequality: excess = κ-1+σ²/κ |" -/
namespace Alignment.Shadows.CoarseGrain.table_R7

-- AMBIGUITY: "Degree-variance inequality" -- the label says "inequality" but the row states an
-- equation; no inequality is written out, so only the equation is formalised (no inequality
-- shadow is guessed).
-- AMBIGUITY: "excess" read as the excess degree ratio, both as the operation
-- `PGFData.excessDegree` (S1) and as its stated meaning ψ''(1)/ψ'(1) (S2); both required.
-- Quantifier: for every PGF `ψ : PGFData` (κ = ψ.mean, σ² = ψ.variance).

/-- Intended statement: for every PGF ψ, the excess degree ratio (as the operation and as
ψ''(1)/ψ'(1)) equals κ − 1 + σ²/κ. -/
@[sa_reference "CoarseGrain.table.R7"]
def T : Prop :=
  ∀ ψ : PGFData,
    ψ.excessDegree = ψ.mean - 1 + ψ.variance / ψ.mean ∧
      ψ.secondFactorial / ψ.mean = ψ.mean - 1 + ψ.variance / ψ.mean

/-- S1: `excessDegree ψ = κ − 1 + σ²/κ` for every ψ. -/
@[sa_shadow "CoarseGrain.table.R7" 1]
def S1 : Prop := ∀ ψ : PGFData, ψ.excessDegree = ψ.mean - 1 + ψ.variance / ψ.mean

/-- S2: `ψ''(1)/ψ'(1) = κ − 1 + σ²/κ` for every ψ. -/
@[sa_shadow "CoarseGrain.table.R7" 2]
def S2 : Prop :=
  ∀ ψ : PGFData, ψ.secondFactorial / ψ.mean = ψ.mean - 1 + ψ.variance / ψ.mean

@[sa_ref_forward "CoarseGrain.table.R7" 1]
theorem ref_fwd1 : T → S1 := fun t ψ => (t ψ).1

@[sa_ref_forward "CoarseGrain.table.R7" 2]
theorem ref_fwd2 : T → S2 := fun t ψ => (t ψ).2

@[sa_complete "CoarseGrain.table.R7"]
theorem complete (s1 : S1) (s2 : S2) : T := fun ψ => ⟨s1 ψ, s2 ψ⟩

end Alignment.Shadows.CoarseGrain.table_R7

/-! ## `CoarseGrain.table.R8` -- "| 8 | Poisson dispersion = 1 |" -/
namespace Alignment.Shadows.CoarseGrain.table_R8

-- AMBIGUITY: "dispersion" read as the index of dispersion, both as the operation
-- `PGFData.dispersionIndex` (S1) and as its stated meaning σ²/κ with κ = ψ.mean,
-- σ² = ψ.variance (S2); both required. "Poisson" = every Poisson PGF, i.e. all κ > 0.
-- The row is one-directional (Poisson ⇒ dispersion 1); no converse is read into it.

/-- Intended statement: every Poisson PGF has index of dispersion 1. -/
@[sa_reference "CoarseGrain.table.R8"]
def T : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ),
    (PGFData.poisson κ hκ).dispersionIndex = 1 ∧
      (PGFData.poisson κ hκ).variance / (PGFData.poisson κ hκ).mean = 1

/-- S1: `dispersionIndex (Poisson κ) = 1` for every κ > 0. -/
@[sa_shadow "CoarseGrain.table.R8" 1]
def S1 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).dispersionIndex = 1

/-- S2: `σ²/κ = 1` for the Poisson PGF with mean κ, for every κ > 0. -/
@[sa_shadow "CoarseGrain.table.R8" 2]
def S2 : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ),
    (PGFData.poisson κ hκ).variance / (PGFData.poisson κ hκ).mean = 1

@[sa_ref_forward "CoarseGrain.table.R8" 1]
theorem ref_fwd1 : T → S1 := fun t κ hκ => (t κ hκ).1

@[sa_ref_forward "CoarseGrain.table.R8" 2]
theorem ref_fwd2 : T → S2 := fun t κ hκ => (t κ hκ).2

@[sa_complete "CoarseGrain.table.R8"]
theorem complete (s1 : S1) (s2 : S2) : T := fun κ hκ => ⟨s1 κ hκ, s2 κ hκ⟩

end Alignment.Shadows.CoarseGrain.table_R8

/-! ## `CoarseGrain.R5` -- "**Result 5.** F is monotone." -/
namespace Alignment.Shadows.CoarseGrain.R5

-- "monotone" is read with respect to the refinement preorder on `EpiModel` (DataTypes), on
-- both sides of `F : EpiModel → EpiModel`.

/-- Intended statement: `F` is monotone. -/
@[sa_reference "CoarseGrain.R5"]
def T : Prop := Monotone coarseGrain

/-- S1: `m ≤ m'` implies `F m ≤ F m'`, for all models. -/
@[sa_shadow "CoarseGrain.R5" 1]
def S1 : Prop := ∀ m m' : EpiModel, m ≤ m' → coarseGrain m ≤ coarseGrain m'

@[sa_ref_forward "CoarseGrain.R5" 1]
theorem ref_fwd1 : T → S1 := fun t _ _ h => t h

@[sa_complete "CoarseGrain.R5"]
theorem complete (s1 : S1) : T := fun m m' h => s1 m m' h

end Alignment.Shadows.CoarseGrain.R5

/-! ## `CoarseGrain.coarseGrainPreservesR0` -- "F preserves R₀." -/
namespace Alignment.Shadows.CoarseGrain.coarseGrainPreservesR0

/-- Intended statement: for every model `m`, `R₀(F m) = R₀(m)`. -/
@[sa_reference "CoarseGrain.coarseGrainPreservesR0"]
def T : Prop := ∀ m : EpiModel, (coarseGrain m).R0 = m.R0

/-- S1: the whole statement (a single atomic requirement). -/
@[sa_shadow "CoarseGrain.coarseGrainPreservesR0" 1]
def S1 : Prop := ∀ m : EpiModel, (coarseGrain m).R0 = m.R0

@[sa_ref_forward "CoarseGrain.coarseGrainPreservesR0" 1]
theorem ref_fwd1 : T → S1 := fun t m => t m

@[sa_complete "CoarseGrain.coarseGrainPreservesR0"]
theorem complete (s1 : S1) : T := fun m => s1 m

end Alignment.Shadows.CoarseGrain.coarseGrainPreservesR0

/-! ## `CoarseGrain.R6` -- "**Result 6.** F is not injective." -/
namespace Alignment.Shadows.CoarseGrain.R6

-- AMBIGUITY: "not injective" read literally as `¬ Function.Injective F` (DataTypes (d)); the
-- classically equivalent witness form (two distinct models with equal images) is not required.

/-- Intended statement: `F` is not injective. -/
@[sa_reference "CoarseGrain.R6"]
def T : Prop := ¬ Function.Injective coarseGrain

/-- S1: it is not the case that `F m = F m'` always forces `m = m'`. -/
@[sa_shadow "CoarseGrain.R6" 1]
def S1 : Prop := ¬ (∀ m m' : EpiModel, coarseGrain m = coarseGrain m' → m = m')

@[sa_ref_forward "CoarseGrain.R6" 1]
theorem ref_fwd1 : T → S1 := fun t hinj => t (fun m m' h => hinj m m' h)

@[sa_complete "CoarseGrain.R6"]
theorem complete (s1 : S1) : T := fun hinj => s1 (fun _ _ h => hinj h)

end Alignment.Shadows.CoarseGrain.R6

/-! ## `CoarseGrain.R7` --
"**Result 7.** The excess degree ratio decomposes as: ψ''(1)/ψ'(1) = κ - 1 + σ²/κ" -/
namespace Alignment.Shadows.CoarseGrain.R7

-- The sentence names the excess degree ratio (operation `PGFData.excessDegree`) and writes it
-- as ψ''(1)/ψ'(1) (= ψ.secondFactorial / ψ.mean); both are required to equal κ − 1 + σ²/κ,
-- with κ = ψ.mean and σ² = ψ.variance (DataTypes notation). Quantifier: every ψ : PGFData.

/-- Intended statement: for every PGF ψ, the excess degree ratio ψ''(1)/ψ'(1) equals
κ − 1 + σ²/κ. -/
@[sa_reference "CoarseGrain.R7"]
def T : Prop :=
  ∀ ψ : PGFData,
    ψ.secondFactorial / ψ.mean = ψ.mean - 1 + ψ.variance / ψ.mean ∧
      ψ.excessDegree = ψ.mean - 1 + ψ.variance / ψ.mean

/-- S1: the displayed identity `ψ''(1)/ψ'(1) = κ − 1 + σ²/κ` for every ψ. -/
@[sa_shadow "CoarseGrain.R7" 1]
def S1 : Prop :=
  ∀ ψ : PGFData, ψ.secondFactorial / ψ.mean = ψ.mean - 1 + ψ.variance / ψ.mean

/-- S2: the named excess degree ratio decomposes: `excessDegree ψ = κ − 1 + σ²/κ`. -/
@[sa_shadow "CoarseGrain.R7" 2]
def S2 : Prop := ∀ ψ : PGFData, ψ.excessDegree = ψ.mean - 1 + ψ.variance / ψ.mean

@[sa_ref_forward "CoarseGrain.R7" 1]
theorem ref_fwd1 : T → S1 := fun t ψ => (t ψ).1

@[sa_ref_forward "CoarseGrain.R7" 2]
theorem ref_fwd2 : T → S2 := fun t ψ => (t ψ).2

@[sa_complete "CoarseGrain.R7"]
theorem complete (s1 : S1) (s2 : S2) : T := fun ψ => ⟨s1 ψ, s2 ψ⟩

end Alignment.Shadows.CoarseGrain.R7

/-! ## `CoarseGrain.R8` -- "**Result 8.** For Poisson, the dispersion index equals 1." -/
namespace Alignment.Shadows.CoarseGrain.R8

-- AMBIGUITY: "the dispersion index" read both as the operation `PGFData.dispersionIndex` (S1)
-- and as its stated meaning σ²/κ with κ = ψ.mean, σ² = ψ.variance (S2); both required.
-- "For Poisson" = for the Poisson PGF with mean κ, for every κ > 0. One direction only.

/-- Intended statement: for every κ > 0, the Poisson PGF with mean κ has dispersion index 1. -/
@[sa_reference "CoarseGrain.R8"]
def T : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ),
    (PGFData.poisson κ hκ).dispersionIndex = 1 ∧
      (PGFData.poisson κ hκ).variance / (PGFData.poisson κ hκ).mean = 1

/-- S1: `dispersionIndex (Poisson κ) = 1` for every κ > 0. -/
@[sa_shadow "CoarseGrain.R8" 1]
def S1 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).dispersionIndex = 1

/-- S2: `σ²/κ = 1` for the Poisson PGF with mean κ, for every κ > 0. -/
@[sa_shadow "CoarseGrain.R8" 2]
def S2 : Prop :=
  ∀ (κ : ℚ) (hκ : 0 < κ),
    (PGFData.poisson κ hκ).variance / (PGFData.poisson κ hκ).mean = 1

@[sa_ref_forward "CoarseGrain.R8" 1]
theorem ref_fwd1 : T → S1 := fun t κ hκ => (t κ hκ).1

@[sa_ref_forward "CoarseGrain.R8" 2]
theorem ref_fwd2 : T → S2 := fun t κ hκ => (t κ hκ).2

@[sa_complete "CoarseGrain.R8"]
theorem complete (s1 : S1) (s2 : S2) : T := fun κ hκ => ⟨s1 κ hκ, s2 κ hκ⟩

end Alignment.Shadows.CoarseGrain.R8
