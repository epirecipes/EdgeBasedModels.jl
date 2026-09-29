import Alignment.Registry
import EBCMCategory.DynamicLimits
import EBCMCategory.Hierarchy   -- only for `levelDim` / `ModelLevel` (listed in DataTypes)
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Blind shadow sets: group `DynamicLimits`

Written blind: the author read only the claim entries in `claims_blind.yaml`,
`Alignment/DataTypes/DynamicLimits.md`, `Alignment/README.md`, `SA-PASS_SKILL.md` and
`Example/ExampleShadows.lean` (plus `#check` of the listed data types and operations).

Vocabulary (from `DataTypes/DynamicLimits.md`), for `m : DynamicEBCM`:
* "dynamic EBCM (dim …)": `m.dim` and, as an abstract model, `m.toEpiModel` (with `.dim`).
  AMBIGUITY (used throughout): "the dynamic EBCM's dimension" is read both as `m.dim` and as
  `m.toEpiModel.dim`; both readings are required as separate shadows.
* "static EBCM" / "static limit": `m.staticLimit`; "fast-rewiring limit" / "mean-field":
  `m.fastRewiringLimit`; "EBCM R₀": `m.R0`; coarse-graining F: `coarseGrain`.
* "A is coarser than B" = `A ≤ B` on `EpiModel` (R39 spells this out: "Mean-field (dim 3) ≤ Static
  EBCM (dim 4)"), hence "A refines B" = `B ≤ A`, and the strict tower uses `<`.
* "Poisson network": `m.pgf = PGFData.poisson κ hκ` for some `κ > 0`; "non-Poisson": for no κ.

VOCAB-GAP (group-wide): `DynamicEBCM` has no rewiring-rate fields (η₁, η₂) and no ODE right-hand
side, so the limits η → 0 / η → ∞ and "independent of the rewiring rate" cannot be stated
literally; the limits are the opaque operations `staticLimit` / `fastRewiringLimit`, and rate
independence is read as agreement with the zero-rewiring R₀ (see `R33a`).
-/

namespace Alignment.Shadows.DynamicLimits

/-- Certificate helper (not registered): `EpiModel` extensionality over its two fields. -/
theorem epiModel_ext_aux {a b : EpiModel} (h1 : a.dim = b.dim) (h2 : a.R0 = b.R0) : a = b := by
  cases a; cases b; cases h1; cases h2; rfl

end Alignment.Shadows.DynamicLimits

/-! ## Header table rows -/

namespace Alignment.Shadows.DynamicLimits.table_R29

/-! Text: "| 29 | Static EBCM dim < Dynamic EBCM dim |". -/

/-- Intended statement: for every dynamic EBCM, the static EBCM has smaller dimension. -/
@[sa_reference "DynamicLimits.table.R29"]
def T : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim < m.dim ∧ m.staticLimit.dim < m.toEpiModel.dim

/-- S1: static dim < dynamic dim (`m.dim`). -/
@[sa_shadow "DynamicLimits.table.R29" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim < m.dim

/-- S2: static dim < dynamic dim (`m.toEpiModel.dim`). -/
@[sa_shadow "DynamicLimits.table.R29" 2]
def S2 : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim < m.toEpiModel.dim

@[sa_ref_forward "DynamicLimits.table.R29" 1]
theorem ref_fwd1 : T → S1 := fun t m => (t m).1
@[sa_ref_forward "DynamicLimits.table.R29" 2]
theorem ref_fwd2 : T → S2 := fun t m => (t m).2
@[sa_complete "DynamicLimits.table.R29"]
theorem complete (s1 : S1) (s2 : S2) : T := fun m => ⟨s1 m, s2 m⟩

end Alignment.Shadows.DynamicLimits.table_R29

namespace Alignment.Shadows.DynamicLimits.table_R30

/-! Text: "| 30 | Dynamic EBCM dim < Pair approximation dim (N ≥ 1) |".
AMBIGUITY: "Pair approximation dim" read (A) as the vocabulary `levelDim
ModelLevel.pairApproximation N` ("State-space dimension at each level for an N-node SIR network
model") and (B) as `12 * N`, the value Result 30 gives ("pair approximation (dim 12N)"). Both
readings, each against both readings of the dynamic dimension, are required (S1–S4). -/

/-- Intended statement: for every dynamic EBCM and every N ≥ 1, its dimension is below the
pair-approximation dimension for N nodes. -/
@[sa_reference "DynamicLimits.table.R30"]
def T : Prop := ∀ (m : DynamicEBCM) (N : ℕ), 1 ≤ N →
  m.dim < levelDim ModelLevel.pairApproximation N ∧
  m.toEpiModel.dim < levelDim ModelLevel.pairApproximation N ∧
  m.dim < 12 * N ∧ m.toEpiModel.dim < 12 * N

/-- S1: `m.dim` < pair-approximation level dimension. -/
@[sa_shadow "DynamicLimits.table.R30" 1]
def S1 : Prop := ∀ (m : DynamicEBCM) (N : ℕ), 1 ≤ N →
  m.dim < levelDim ModelLevel.pairApproximation N

/-- S2: `m.toEpiModel.dim` < pair-approximation level dimension. -/
@[sa_shadow "DynamicLimits.table.R30" 2]
def S2 : Prop := ∀ (m : DynamicEBCM) (N : ℕ), 1 ≤ N →
  m.toEpiModel.dim < levelDim ModelLevel.pairApproximation N

/-- S3: `m.dim` < 12N. -/
@[sa_shadow "DynamicLimits.table.R30" 3]
def S3 : Prop := ∀ (m : DynamicEBCM) (N : ℕ), 1 ≤ N → m.dim < 12 * N

/-- S4: `m.toEpiModel.dim` < 12N. -/
@[sa_shadow "DynamicLimits.table.R30" 4]
def S4 : Prop := ∀ (m : DynamicEBCM) (N : ℕ), 1 ≤ N → m.toEpiModel.dim < 12 * N

@[sa_ref_forward "DynamicLimits.table.R30" 1]
theorem ref_fwd1 : T → S1 := fun t m N hN => (t m N hN).1
@[sa_ref_forward "DynamicLimits.table.R30" 2]
theorem ref_fwd2 : T → S2 := fun t m N hN => (t m N hN).2.1
@[sa_ref_forward "DynamicLimits.table.R30" 3]
theorem ref_fwd3 : T → S3 := fun t m N hN => (t m N hN).2.2.1
@[sa_ref_forward "DynamicLimits.table.R30" 4]
theorem ref_fwd4 : T → S4 := fun t m N hN => (t m N hN).2.2.2
@[sa_complete "DynamicLimits.table.R30"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T :=
  fun m N hN => ⟨s1 m N hN, s2 m N hN, s3 m N hN, s4 m N hN⟩

end Alignment.Shadows.DynamicLimits.table_R30

namespace Alignment.Shadows.DynamicLimits.table_R31

/-! Text: "| 31 | Static limit: dynamic → static (dim 5 → 4) |".
AMBIGUITY: "dynamic → static" — with the DataTypes mapping "static EBCM" = `m.staticLimit` the
arrow itself carries no further checkable content; the checkable part is "dim 5 → 4". -/

/-- Intended statement: the dynamic model has dim 5 and its static limit dim 4. -/
@[sa_reference "DynamicLimits.table.R31"]
def T : Prop := ∀ m : DynamicEBCM, m.dim = 5 ∧ m.toEpiModel.dim = 5 ∧ m.staticLimit.dim = 4

/-- S1: source dimension 5 (`m.dim`). -/
@[sa_shadow "DynamicLimits.table.R31" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.dim = 5

/-- S2: source dimension 5 (`m.toEpiModel.dim`). -/
@[sa_shadow "DynamicLimits.table.R31" 2]
def S2 : Prop := ∀ m : DynamicEBCM, m.toEpiModel.dim = 5

/-- S3: target dimension 4. -/
@[sa_shadow "DynamicLimits.table.R31" 3]
def S3 : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim = 4

@[sa_ref_forward "DynamicLimits.table.R31" 1]
theorem ref_fwd1 : T → S1 := fun t m => (t m).1
@[sa_ref_forward "DynamicLimits.table.R31" 2]
theorem ref_fwd2 : T → S2 := fun t m => (t m).2.1
@[sa_ref_forward "DynamicLimits.table.R31" 3]
theorem ref_fwd3 : T → S3 := fun t m => (t m).2.2
@[sa_complete "DynamicLimits.table.R31"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := fun m => ⟨s1 m, s2 m, s3 m⟩

end Alignment.Shadows.DynamicLimits.table_R31

namespace Alignment.Shadows.DynamicLimits.table_R34

/-! Text: "| 34 | Coarse-graining commutes with static limit |".
AMBIGUITY: "commutes" — `coarseGrain` acts on `EpiModel` and `staticLimit` on `DynamicEBCM`, so
the only well-typed reading is F(dynamic) = F(staticLimit(dynamic)) (as Result 34 spells out),
i.e. `coarseGrain m.toEpiModel = coarseGrain m.staticLimit`. Split into its two field
components. -/

/-- Intended statement: F(dynamic) = F(static limit of dynamic), for every dynamic EBCM. -/
@[sa_reference "DynamicLimits.table.R34"]
def T : Prop := ∀ m : DynamicEBCM, coarseGrain m.toEpiModel = coarseGrain m.staticLimit

/-- S1: the dimensions agree. -/
@[sa_shadow "DynamicLimits.table.R34" 1]
def S1 : Prop := ∀ m : DynamicEBCM, (coarseGrain m.toEpiModel).dim = (coarseGrain m.staticLimit).dim

/-- S2: the R₀ values agree. -/
@[sa_shadow "DynamicLimits.table.R34" 2]
def S2 : Prop := ∀ m : DynamicEBCM, (coarseGrain m.toEpiModel).R0 = (coarseGrain m.staticLimit).R0

@[sa_ref_forward "DynamicLimits.table.R34" 1]
theorem ref_fwd1 : T → S1 := fun t m => congrArg EpiModel.dim (t m)
@[sa_ref_forward "DynamicLimits.table.R34" 2]
theorem ref_fwd2 : T → S2 := fun t m => congrArg EpiModel.R0 (t m)
@[sa_complete "DynamicLimits.table.R34"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun m => Alignment.Shadows.DynamicLimits.epiModel_ext_aux (s1 m) (s2 m)

end Alignment.Shadows.DynamicLimits.table_R34

namespace Alignment.Shadows.DynamicLimits.table_R38

/-! Text: "| 38 | Dynamic refines static |". "A refines B" = `B ≤ A` (see module header). -/

/-- Intended statement (single atomic requirement). -/
@[sa_reference "DynamicLimits.table.R38"]
def T : Prop := ∀ m : DynamicEBCM, m.staticLimit ≤ m.toEpiModel

/-- S1: the whole statement. -/
@[sa_shadow "DynamicLimits.table.R38" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.staticLimit ≤ m.toEpiModel

@[sa_ref_forward "DynamicLimits.table.R38" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "DynamicLimits.table.R38"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynamicLimits.table_R38

namespace Alignment.Shadows.DynamicLimits.table_R39

/-! Text: "| 39 | Fast-rewiring is coarser than static |". -/

/-- Intended statement (single atomic requirement). -/
@[sa_reference "DynamicLimits.table.R39"]
def T : Prop := ∀ m : DynamicEBCM, m.fastRewiringLimit ≤ m.staticLimit

/-- S1: the whole statement. -/
@[sa_shadow "DynamicLimits.table.R39" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.fastRewiringLimit ≤ m.staticLimit

@[sa_ref_forward "DynamicLimits.table.R39" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "DynamicLimits.table.R39"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynamicLimits.table_R39

namespace Alignment.Shadows.DynamicLimits.table_R40

/-! Text: "| 40 | Full tower: mean-field < static < dynamic |". Strict order `<` of the
`EpiModel` preorder; "mean-field" = fast-rewiring limit, "dynamic" = `m.toEpiModel`. -/

/-- Intended statement: fast-rewiring limit < static limit < dynamic model. -/
@[sa_reference "DynamicLimits.table.R40"]
def T : Prop := ∀ m : DynamicEBCM,
  m.fastRewiringLimit < m.staticLimit ∧ m.staticLimit < m.toEpiModel

/-- S1: mean-field < static. -/
@[sa_shadow "DynamicLimits.table.R40" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.fastRewiringLimit < m.staticLimit

/-- S2: static < dynamic. -/
@[sa_shadow "DynamicLimits.table.R40" 2]
def S2 : Prop := ∀ m : DynamicEBCM, m.staticLimit < m.toEpiModel

@[sa_ref_forward "DynamicLimits.table.R40" 1]
theorem ref_fwd1 : T → S1 := fun t m => (t m).1
@[sa_ref_forward "DynamicLimits.table.R40" 2]
theorem ref_fwd2 : T → S2 := fun t m => (t m).2
@[sa_complete "DynamicLimits.table.R40"]
theorem complete (s1 : S1) (s2 : S2) : T := fun m => ⟨s1 m, s2 m⟩

end Alignment.Shadows.DynamicLimits.table_R40

/-! ## Results (docstrings) -/

namespace Alignment.Shadows.DynamicLimits.R29

/-! Text: "**Result 29.** The static EBCM (dim 4) has fewer variables than the dynamic EBCM
(dim 5)." The parentheticals are asserted values and are required too. -/

/-- Intended statement: static dim 4 < dynamic dim 5. -/
@[sa_reference "DynamicLimits.R29"]
def T : Prop := ∀ m : DynamicEBCM,
  m.staticLimit.dim < m.dim ∧ m.staticLimit.dim < m.toEpiModel.dim ∧
  m.staticLimit.dim = 4 ∧ m.dim = 5 ∧ m.toEpiModel.dim = 5

/-- S1: fewer variables (`m.dim`). -/
@[sa_shadow "DynamicLimits.R29" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim < m.dim

/-- S2: fewer variables (`m.toEpiModel.dim`). -/
@[sa_shadow "DynamicLimits.R29" 2]
def S2 : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim < m.toEpiModel.dim

/-- S3: "static EBCM (dim 4)". -/
@[sa_shadow "DynamicLimits.R29" 3]
def S3 : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim = 4

/-- S4: "dynamic EBCM (dim 5)", `m.dim`. -/
@[sa_shadow "DynamicLimits.R29" 4]
def S4 : Prop := ∀ m : DynamicEBCM, m.dim = 5

/-- S5: "dynamic EBCM (dim 5)", `m.toEpiModel.dim`. -/
@[sa_shadow "DynamicLimits.R29" 5]
def S5 : Prop := ∀ m : DynamicEBCM, m.toEpiModel.dim = 5

@[sa_ref_forward "DynamicLimits.R29" 1]
theorem ref_fwd1 : T → S1 := fun t m => (t m).1
@[sa_ref_forward "DynamicLimits.R29" 2]
theorem ref_fwd2 : T → S2 := fun t m => (t m).2.1
@[sa_ref_forward "DynamicLimits.R29" 3]
theorem ref_fwd3 : T → S3 := fun t m => (t m).2.2.1
@[sa_ref_forward "DynamicLimits.R29" 4]
theorem ref_fwd4 : T → S4 := fun t m => (t m).2.2.2.1
@[sa_ref_forward "DynamicLimits.R29" 5]
theorem ref_fwd5 : T → S5 := fun t m => (t m).2.2.2.2
@[sa_complete "DynamicLimits.R29"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  fun m => ⟨s1 m, s2 m, s3 m, s4 m, s5 m⟩

end Alignment.Shadows.DynamicLimits.R29

namespace Alignment.Shadows.DynamicLimits.R30

/-! Text: "**Result 30.** The dynamic EBCM (dim 5) has fewer variables than pair approximation
(dim 12N) for N ≥ 1." The pair-approximation dimension is taken as the text's own value 12N
(primitive terms); "for N ≥ 1" qualifies the comparison. -/

/-- Intended statement: dynamic dim is 5, and below 12N for every N ≥ 1. -/
@[sa_reference "DynamicLimits.R30"]
def T : Prop := ∀ m : DynamicEBCM,
  (∀ N : ℕ, 1 ≤ N → m.dim < 12 * N) ∧ (∀ N : ℕ, 1 ≤ N → m.toEpiModel.dim < 12 * N) ∧
  m.dim = 5 ∧ m.toEpiModel.dim = 5

/-- S1: fewer variables than 12N (`m.dim`). -/
@[sa_shadow "DynamicLimits.R30" 1]
def S1 : Prop := ∀ (m : DynamicEBCM) (N : ℕ), 1 ≤ N → m.dim < 12 * N

/-- S2: fewer variables than 12N (`m.toEpiModel.dim`). -/
@[sa_shadow "DynamicLimits.R30" 2]
def S2 : Prop := ∀ (m : DynamicEBCM) (N : ℕ), 1 ≤ N → m.toEpiModel.dim < 12 * N

/-- S3: "dynamic EBCM (dim 5)", `m.dim`. -/
@[sa_shadow "DynamicLimits.R30" 3]
def S3 : Prop := ∀ m : DynamicEBCM, m.dim = 5

/-- S4: "dynamic EBCM (dim 5)", `m.toEpiModel.dim`. -/
@[sa_shadow "DynamicLimits.R30" 4]
def S4 : Prop := ∀ m : DynamicEBCM, m.toEpiModel.dim = 5

@[sa_ref_forward "DynamicLimits.R30" 1]
theorem ref_fwd1 : T → S1 := fun t m => (t m).1
@[sa_ref_forward "DynamicLimits.R30" 2]
theorem ref_fwd2 : T → S2 := fun t m => (t m).2.1
@[sa_ref_forward "DynamicLimits.R30" 3]
theorem ref_fwd3 : T → S3 := fun t m => (t m).2.2.1
@[sa_ref_forward "DynamicLimits.R30" 4]
theorem ref_fwd4 : T → S4 := fun t m => (t m).2.2.2
@[sa_complete "DynamicLimits.R30"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T :=
  fun m => ⟨s1 m, s2 m, s3 m, s4 m⟩

end Alignment.Shadows.DynamicLimits.R30

namespace Alignment.Shadows.DynamicLimits.R31a

/-! Text: "reducing the dimension by 1 [...] **Result 31.** Static limit: the dimension drops
from 5 to 4." -/

/-- Intended statement: in the static limit the dimension goes from 5 to 4, a reduction by 1. -/
@[sa_reference "DynamicLimits.R31a"]
def T : Prop := ∀ m : DynamicEBCM,
  m.dim = 5 ∧ m.toEpiModel.dim = 5 ∧ m.staticLimit.dim = 4 ∧
  m.staticLimit.dim + 1 = m.dim ∧ m.staticLimit.dim + 1 = m.toEpiModel.dim

/-- S1: "from 5" (`m.dim`). -/
@[sa_shadow "DynamicLimits.R31a" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.dim = 5

/-- S2: "from 5" (`m.toEpiModel.dim`). -/
@[sa_shadow "DynamicLimits.R31a" 2]
def S2 : Prop := ∀ m : DynamicEBCM, m.toEpiModel.dim = 5

/-- S3: "to 4". -/
@[sa_shadow "DynamicLimits.R31a" 3]
def S3 : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim = 4

/-- S4: "reducing the dimension by 1" (`m.dim`). -/
@[sa_shadow "DynamicLimits.R31a" 4]
def S4 : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim + 1 = m.dim

/-- S5: "reducing the dimension by 1" (`m.toEpiModel.dim`). -/
@[sa_shadow "DynamicLimits.R31a" 5]
def S5 : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim + 1 = m.toEpiModel.dim

@[sa_ref_forward "DynamicLimits.R31a" 1]
theorem ref_fwd1 : T → S1 := fun t m => (t m).1
@[sa_ref_forward "DynamicLimits.R31a" 2]
theorem ref_fwd2 : T → S2 := fun t m => (t m).2.1
@[sa_ref_forward "DynamicLimits.R31a" 3]
theorem ref_fwd3 : T → S3 := fun t m => (t m).2.2.1
@[sa_ref_forward "DynamicLimits.R31a" 4]
theorem ref_fwd4 : T → S4 := fun t m => (t m).2.2.2.1
@[sa_ref_forward "DynamicLimits.R31a" 5]
theorem ref_fwd5 : T → S5 := fun t m => (t m).2.2.2.2
@[sa_complete "DynamicLimits.R31a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  fun m => ⟨s1 m, s2 m, s3 m, s4 m, s5 m⟩

end Alignment.Shadows.DynamicLimits.R31a

namespace Alignment.Shadows.DynamicLimits.R32a

/-! Text: "**Result 32.** Fast-rewiring limit: the dimension drops to 3."
AMBIGUITY: "drops to 3" read as (i) the resulting dimension is 3 and (ii) it is strictly lower
than the dynamic model's dimension (a drop); both required. -/

/-- Intended statement: the fast-rewiring limit has dim 3, strictly below the dynamic dim. -/
@[sa_reference "DynamicLimits.R32a"]
def T : Prop := ∀ m : DynamicEBCM,
  m.fastRewiringLimit.dim = 3 ∧ m.fastRewiringLimit.dim < m.dim ∧
  m.fastRewiringLimit.dim < m.toEpiModel.dim

/-- S1: resulting dimension 3. -/
@[sa_shadow "DynamicLimits.R32a" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.fastRewiringLimit.dim = 3

/-- S2: a drop relative to `m.dim`. -/
@[sa_shadow "DynamicLimits.R32a" 2]
def S2 : Prop := ∀ m : DynamicEBCM, m.fastRewiringLimit.dim < m.dim

/-- S3: a drop relative to `m.toEpiModel.dim`. -/
@[sa_shadow "DynamicLimits.R32a" 3]
def S3 : Prop := ∀ m : DynamicEBCM, m.fastRewiringLimit.dim < m.toEpiModel.dim

@[sa_ref_forward "DynamicLimits.R32a" 1]
theorem ref_fwd1 : T → S1 := fun t m => (t m).1
@[sa_ref_forward "DynamicLimits.R32a" 2]
theorem ref_fwd2 : T → S2 := fun t m => (t m).2.1
@[sa_ref_forward "DynamicLimits.R32a" 3]
theorem ref_fwd3 : T → S3 := fun t m => (t m).2.2
@[sa_complete "DynamicLimits.R32a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := fun m => ⟨s1 m, s2 m, s3 m⟩

end Alignment.Shadows.DynamicLimits.R32a

namespace Alignment.Shadows.DynamicLimits.R33b

/-! Text: "The static limit preserves R₀ exactly,". "Exactly" = equality. The R₀ of the dynamic
model read both as `m.R0` ("EBCM R₀") and as `m.toEpiModel.R0` (AMBIGUITY). -/

/-- Intended statement: the static limit has the same R₀ as the dynamic model. -/
@[sa_reference "DynamicLimits.R33b"]
def T : Prop := ∀ m : DynamicEBCM, m.staticLimit.R0 = m.R0 ∧ m.staticLimit.R0 = m.toEpiModel.R0

/-- S1: preserved relative to `m.R0`. -/
@[sa_shadow "DynamicLimits.R33b" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.staticLimit.R0 = m.R0

/-- S2: preserved relative to `m.toEpiModel.R0`. -/
@[sa_shadow "DynamicLimits.R33b" 2]
def S2 : Prop := ∀ m : DynamicEBCM, m.staticLimit.R0 = m.toEpiModel.R0

@[sa_ref_forward "DynamicLimits.R33b" 1]
theorem ref_fwd1 : T → S1 := fun t m => (t m).1
@[sa_ref_forward "DynamicLimits.R33b" 2]
theorem ref_fwd2 : T → S2 := fun t m => (t m).2
@[sa_complete "DynamicLimits.R33b"]
theorem complete (s1 : S1) (s2 : S2) : T := fun m => ⟨s1 m, s2 m⟩

end Alignment.Shadows.DynamicLimits.R33b

namespace Alignment.Shadows.DynamicLimits.R34

/-! Text: "**Result 34.** Coarse-graining commutes with the static limit. F(dynamic) =
F(staticLimit(dynamic)), because both give dim 3 with the same R₀."
The equation is split into its field components (S1, S2); the "because" clause asserts that both
sides have dimension 3 (S3, S4) and equal R₀ (S2). -/

/-- Intended statement: F(dynamic) = F(staticLimit(dynamic)), both of dimension 3. -/
@[sa_reference "DynamicLimits.R34"]
def T : Prop := ∀ m : DynamicEBCM,
  coarseGrain m.toEpiModel = coarseGrain m.staticLimit ∧
  (coarseGrain m.toEpiModel).dim = 3 ∧ (coarseGrain m.staticLimit).dim = 3

/-- S1: the dimensions of the two sides agree. -/
@[sa_shadow "DynamicLimits.R34" 1]
def S1 : Prop := ∀ m : DynamicEBCM, (coarseGrain m.toEpiModel).dim = (coarseGrain m.staticLimit).dim

/-- S2: "with the same R₀". -/
@[sa_shadow "DynamicLimits.R34" 2]
def S2 : Prop := ∀ m : DynamicEBCM, (coarseGrain m.toEpiModel).R0 = (coarseGrain m.staticLimit).R0

/-- S3: F(dynamic) has dim 3. -/
@[sa_shadow "DynamicLimits.R34" 3]
def S3 : Prop := ∀ m : DynamicEBCM, (coarseGrain m.toEpiModel).dim = 3

/-- S4: F(staticLimit(dynamic)) has dim 3. -/
@[sa_shadow "DynamicLimits.R34" 4]
def S4 : Prop := ∀ m : DynamicEBCM, (coarseGrain m.staticLimit).dim = 3

@[sa_ref_forward "DynamicLimits.R34" 1]
theorem ref_fwd1 : T → S1 := fun t m => congrArg EpiModel.dim (t m).1
@[sa_ref_forward "DynamicLimits.R34" 2]
theorem ref_fwd2 : T → S2 := fun t m => congrArg EpiModel.R0 (t m).1
@[sa_ref_forward "DynamicLimits.R34" 3]
theorem ref_fwd3 : T → S3 := fun t m => (t m).2.1
@[sa_ref_forward "DynamicLimits.R34" 4]
theorem ref_fwd4 : T → S4 := fun t m => (t m).2.2
@[sa_complete "DynamicLimits.R34"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T :=
  fun m => ⟨Alignment.Shadows.DynamicLimits.epiModel_ext_aux (s1 m) (s2 m), s3 m, s4 m⟩

end Alignment.Shadows.DynamicLimits.R34

namespace Alignment.Shadows.DynamicLimits.R35a

/-! Text: "**Result 35.** The fast-rewiring limit has the same dimension as coarse-graining (both
give dim = 3)."
AMBIGUITY: "coarse-graining" read as the coarse-graining F of the same dynamic model,
`coarseGrain m.toEpiModel` (the comparison in the sentence is per model). -/

/-- Intended statement: fast-rewiring dim = F(dynamic) dim = 3. -/
@[sa_reference "DynamicLimits.R35a"]
def T : Prop := ∀ m : DynamicEBCM,
  m.fastRewiringLimit.dim = (coarseGrain m.toEpiModel).dim ∧
  m.fastRewiringLimit.dim = 3 ∧ (coarseGrain m.toEpiModel).dim = 3

/-- S1: same dimension. -/
@[sa_shadow "DynamicLimits.R35a" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.fastRewiringLimit.dim = (coarseGrain m.toEpiModel).dim

/-- S2: fast-rewiring limit gives dim 3. -/
@[sa_shadow "DynamicLimits.R35a" 2]
def S2 : Prop := ∀ m : DynamicEBCM, m.fastRewiringLimit.dim = 3

/-- S3: coarse-graining gives dim 3. -/
@[sa_shadow "DynamicLimits.R35a" 3]
def S3 : Prop := ∀ m : DynamicEBCM, (coarseGrain m.toEpiModel).dim = 3

@[sa_ref_forward "DynamicLimits.R35a" 1]
theorem ref_fwd1 : T → S1 := fun t m => (t m).1
@[sa_ref_forward "DynamicLimits.R35a" 2]
theorem ref_fwd2 : T → S2 := fun t m => (t m).2.1
@[sa_ref_forward "DynamicLimits.R35a" 3]
theorem ref_fwd3 : T → S3 := fun t m => (t m).2.2
@[sa_complete "DynamicLimits.R35a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := fun m => ⟨s1 m, s2 m, s3 m⟩

end Alignment.Shadows.DynamicLimits.R35a

namespace Alignment.Shadows.DynamicLimits.R36b

/-! Text: "This is because the Poisson excess degree equals the mean degree: ψ''(1)/ψ'(1) = κ."
AMBIGUITY: "the mean degree" read as the parameter κ and as the PGF mean ψ'(1) (`.mean`); "excess
degree" read as the vocabulary `PGFData.excessDegree` and as the explicit primitive formula
ψ''(1)/ψ'(1) = `secondFactorial / mean` that the text writes out. -/

/-- Intended statement: for every κ > 0, the Poisson excess degree equals κ and ψ'(1), and
ψ''(1)/ψ'(1) = κ. -/
@[sa_reference "DynamicLimits.R36b"]
def T : Prop := ∀ (κ : ℚ) (hκ : 0 < κ),
  (PGFData.poisson κ hκ).excessDegree = κ ∧
  (PGFData.poisson κ hκ).excessDegree = (PGFData.poisson κ hκ).mean ∧
  (PGFData.poisson κ hκ).secondFactorial / (PGFData.poisson κ hκ).mean = κ

/-- S1: excess degree = κ. -/
@[sa_shadow "DynamicLimits.R36b" 1]
def S1 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).excessDegree = κ

/-- S2: excess degree = mean degree ψ'(1). -/
@[sa_shadow "DynamicLimits.R36b" 2]
def S2 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ),
  (PGFData.poisson κ hκ).excessDegree = (PGFData.poisson κ hκ).mean

/-- S3: ψ''(1)/ψ'(1) = κ, in primitive terms. -/
@[sa_shadow "DynamicLimits.R36b" 3]
def S3 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ),
  (PGFData.poisson κ hκ).secondFactorial / (PGFData.poisson κ hκ).mean = κ

@[sa_ref_forward "DynamicLimits.R36b" 1]
theorem ref_fwd1 : T → S1 := fun t κ hκ => (t κ hκ).1
@[sa_ref_forward "DynamicLimits.R36b" 2]
theorem ref_fwd2 : T → S2 := fun t κ hκ => (t κ hκ).2.1
@[sa_ref_forward "DynamicLimits.R36b" 3]
theorem ref_fwd3 : T → S3 := fun t κ hκ => (t κ hκ).2.2
@[sa_complete "DynamicLimits.R36b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T :=
  fun κ hκ => ⟨s1 κ hκ, s2 κ hκ, s3 κ hκ⟩

end Alignment.Shadows.DynamicLimits.R36b

namespace Alignment.Shadows.DynamicLimits.R38

/-! Text: "**Result 38.** The dynamic model refines the static model (it has strictly more state
variables: 5 > 4)."
"A refines B" = `B ≤ A`. The parenthetical asserts a strict dimension inequality and the values
5 and 4; all required. -/

/-- Intended statement: static ≤ dynamic, with 4 = static dim < dynamic dim = 5. -/
@[sa_reference "DynamicLimits.R38"]
def T : Prop := ∀ m : DynamicEBCM,
  m.staticLimit ≤ m.toEpiModel ∧
  m.staticLimit.dim < m.toEpiModel.dim ∧ m.staticLimit.dim < m.dim ∧
  m.toEpiModel.dim = 5 ∧ m.dim = 5 ∧ m.staticLimit.dim = 4

/-- S1: dynamic refines static. -/
@[sa_shadow "DynamicLimits.R38" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.staticLimit ≤ m.toEpiModel

/-- S2: strictly more state variables (`m.toEpiModel.dim`). -/
@[sa_shadow "DynamicLimits.R38" 2]
def S2 : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim < m.toEpiModel.dim

/-- S3: strictly more state variables (`m.dim`). -/
@[sa_shadow "DynamicLimits.R38" 3]
def S3 : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim < m.dim

/-- S4: dynamic has 5 (`m.toEpiModel.dim`). -/
@[sa_shadow "DynamicLimits.R38" 4]
def S4 : Prop := ∀ m : DynamicEBCM, m.toEpiModel.dim = 5

/-- S5: dynamic has 5 (`m.dim`). -/
@[sa_shadow "DynamicLimits.R38" 5]
def S5 : Prop := ∀ m : DynamicEBCM, m.dim = 5

/-- S6: static has 4. -/
@[sa_shadow "DynamicLimits.R38" 6]
def S6 : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim = 4

@[sa_ref_forward "DynamicLimits.R38" 1]
theorem ref_fwd1 : T → S1 := fun t m => (t m).1
@[sa_ref_forward "DynamicLimits.R38" 2]
theorem ref_fwd2 : T → S2 := fun t m => (t m).2.1
@[sa_ref_forward "DynamicLimits.R38" 3]
theorem ref_fwd3 : T → S3 := fun t m => (t m).2.2.1
@[sa_ref_forward "DynamicLimits.R38" 4]
theorem ref_fwd4 : T → S4 := fun t m => (t m).2.2.2.1
@[sa_ref_forward "DynamicLimits.R38" 5]
theorem ref_fwd5 : T → S5 := fun t m => (t m).2.2.2.2.1
@[sa_ref_forward "DynamicLimits.R38" 6]
theorem ref_fwd6 : T → S6 := fun t m => (t m).2.2.2.2.2
@[sa_complete "DynamicLimits.R38"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T :=
  fun m => ⟨s1 m, s2 m, s3 m, s4 m, s5 m, s6 m⟩

end Alignment.Shadows.DynamicLimits.R38

namespace Alignment.Shadows.DynamicLimits.R39

/-! Text: "**Result 39.** The fast-rewiring limit is coarser than the static limit. Mean-field
(dim 3) ≤ Static EBCM (dim 4)."
AMBIGUITY: the displayed "≤" is read as the refinement preorder between the models (S1, same
content as the first sentence); the parentheticals assert the dimensions (S2, S3); the numeric
comparison 3 ≤ 4 follows from S2 and S3. -/

/-- Intended statement: fast-rewiring limit ≤ static limit, of dims 3 and 4. -/
@[sa_reference "DynamicLimits.R39"]
def T : Prop := ∀ m : DynamicEBCM,
  m.fastRewiringLimit ≤ m.staticLimit ∧ m.fastRewiringLimit.dim = 3 ∧ m.staticLimit.dim = 4

/-- S1: coarser than the static limit. -/
@[sa_shadow "DynamicLimits.R39" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.fastRewiringLimit ≤ m.staticLimit

/-- S2: "Mean-field (dim 3)". -/
@[sa_shadow "DynamicLimits.R39" 2]
def S2 : Prop := ∀ m : DynamicEBCM, m.fastRewiringLimit.dim = 3

/-- S3: "Static EBCM (dim 4)". -/
@[sa_shadow "DynamicLimits.R39" 3]
def S3 : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim = 4

@[sa_ref_forward "DynamicLimits.R39" 1]
theorem ref_fwd1 : T → S1 := fun t m => (t m).1
@[sa_ref_forward "DynamicLimits.R39" 2]
theorem ref_fwd2 : T → S2 := fun t m => (t m).2.1
@[sa_ref_forward "DynamicLimits.R39" 3]
theorem ref_fwd3 : T → S3 := fun t m => (t m).2.2
@[sa_complete "DynamicLimits.R39"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := fun m => ⟨s1 m, s2 m, s3 m⟩

end Alignment.Shadows.DynamicLimits.R39

namespace Alignment.Shadows.DynamicLimits.R40a

/-! Text: "**Result 40.** The full tower: mean-field < static EBCM < dynamic EBCM."
Strict order `<` of the `EpiModel` preorder. -/

/-- Intended statement: fast-rewiring limit < static limit < dynamic model. -/
@[sa_reference "DynamicLimits.R40a"]
def T : Prop := ∀ m : DynamicEBCM,
  m.fastRewiringLimit < m.staticLimit ∧ m.staticLimit < m.toEpiModel

/-- S1: mean-field < static EBCM. -/
@[sa_shadow "DynamicLimits.R40a" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.fastRewiringLimit < m.staticLimit

/-- S2: static EBCM < dynamic EBCM. -/
@[sa_shadow "DynamicLimits.R40a" 2]
def S2 : Prop := ∀ m : DynamicEBCM, m.staticLimit < m.toEpiModel

@[sa_ref_forward "DynamicLimits.R40a" 1]
theorem ref_fwd1 : T → S1 := fun t m => (t m).1
@[sa_ref_forward "DynamicLimits.R40a" 2]
theorem ref_fwd2 : T → S2 := fun t m => (t m).2
@[sa_complete "DynamicLimits.R40a"]
theorem complete (s1 : S1) (s2 : S2) : T := fun m => ⟨s1 m, s2 m⟩

end Alignment.Shadows.DynamicLimits.R40a

noncomputable section

/-! ## Shared notions for the re-authored DynamicLimits blocks (blind)

Not registered; inlined by the audit. The rewiring rate η is not a field of `DynamicEBCM`, so the
edge-swapping R₀ is written from the cited source (Miller, Slim & Volz 2012; Miller & Volz,
"Edge-based compartmental modeling ... Part I", `papers/1106.6320v1.md`, the edge-swapping model):
`R₀(η) = β/(β+η+γ) · ((η+γ)/γ · ⟨K²−K⟩/⟨K⟩ + η/γ)`, with `⟨K²−K⟩/⟨K⟩ = ψ''(1)/ψ'(1)`. The MFSH
(fast-rewiring) R₀ is `(β/γ)⟨K²⟩/⟨K⟩ = (β/γ)(ψ''(1)/ψ'(1) + 1)`, and the static-limit R₀ is
`T·ψ''(1)/ψ'(1)` with `T = β/(β+γ)`, all in primitive terms of `SIRParams` and `PGFData`. -/
namespace Alignment.Shadows.DynamicLimits.Shared2

/-- Edge-swapping R₀ at rewiring rate η (over ℚ). -/
def edgeSwapR0 (p : SIRParams) (ψ : PGFData) (η : ℚ) : ℚ :=
  p.β / (p.β + η + p.γ) * ((η + p.γ) / p.γ * (ψ.secondFactorial / ψ.mean) + η / p.γ)
/-- Edge-swapping R₀ at a real rewiring rate η (for limits η → ∞). -/
def edgeSwapR0R (p : SIRParams) (ψ : PGFData) (η : ℝ) : ℝ :=
  (p.β : ℝ) / (p.β + η + p.γ) *
    ((η + p.γ) / p.γ * ((ψ.secondFactorial : ℝ) / ψ.mean) + η / p.γ)
/-- MFSH (fast-rewiring) R₀ `(β/γ)(ψ''(1)/ψ'(1) + 1)`. -/
def mfshR0 (p : SIRParams) (ψ : PGFData) : ℚ := p.β / p.γ * (ψ.secondFactorial / ψ.mean + 1)
/-- Static-limit R₀ `T·ψ''(1)/ψ'(1)`, `T = β/(β+γ)`. -/
def staticR0 (p : SIRParams) (ψ : PGFData) : ℚ :=
  p.β / (p.β + p.γ) * (ψ.secondFactorial / ψ.mean)

end Alignment.Shadows.DynamicLimits.Shared2

/-! ## `DynamicLimits.R32b` (re-authored blind)

Text: "When the network randomises infinitely fast, partnerships become fleeting and the model
approaches MFSH (θ and R, with S = ψ(θ) and I = 1 − S − R), in which degree heterogeneity survives
through ψ."

-- AMBIGUITY: "the model approaches MFSH" is read at the level of the one η-dependent quantity the
text names elsewhere, R₀: the edge-swapping R₀ tends to the MFSH R₀ as η → ∞ (S1). "Degree
heterogeneity survives through ψ": the MFSH R₀ depends on ψ''(1) and not only on the mean (S2).
The listing of the MFSH variables is descriptive and not formalised. -/
namespace Alignment.Shadows.DynamicLimits.R32b

open Alignment.Shadows.DynamicLimits.Shared2 Filter Topology

@[sa_reference "DynamicLimits.R32b"]
def T : Prop :=
  (∀ (p : SIRParams) (ψ : PGFData),
      Tendsto (fun η : ℝ => edgeSwapR0R p ψ η) atTop (𝓝 ((mfshR0 p ψ : ℚ) : ℝ))) ∧
  (∀ (p : SIRParams) (ψ₁ ψ₂ : PGFData), ψ₁.mean = ψ₂.mean →
      ψ₁.secondFactorial ≠ ψ₂.secondFactorial → mfshR0 p ψ₁ ≠ mfshR0 p ψ₂)

/-- S1: as η → ∞ the edge-swapping R₀ tends to the MFSH R₀. -/
@[sa_shadow "DynamicLimits.R32b" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData),
    Tendsto (fun η : ℝ => edgeSwapR0R p ψ η) atTop (𝓝 ((mfshR0 p ψ : ℚ) : ℝ))
/-- S2: the MFSH R₀ distinguishes degree laws with the same mean. -/
@[sa_shadow "DynamicLimits.R32b" 2]
def S2 : Prop :=
  ∀ (p : SIRParams) (ψ₁ ψ₂ : PGFData), ψ₁.mean = ψ₂.mean →
    ψ₁.secondFactorial ≠ ψ₂.secondFactorial → mfshR0 p ψ₁ ≠ mfshR0 p ψ₂

@[sa_ref_forward "DynamicLimits.R32b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DynamicLimits.R32b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "DynamicLimits.R32b"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.DynamicLimits.R32b

/-! ## `DynamicLimits.R33a` (re-authored blind)

Text: "`DynamicEBCM` records no rewiring rate, so this is not the R₀ of the dynamic model. [...]
**Result 33.** `DynamicEBCM` stores only the static-limit R₀: `DynamicEBCM.R0` is T·ψ''(1)/ψ'(1)."

S1: `DynamicEBCM.R0` is `T·ψ''(1)/ψ'(1)`. S2: it differs from the R₀ of the dynamic (edge-swapping)
model at every positive rewiring rate. That the record has no rate field is a fact about the
structure and is not a proposition. -/
namespace Alignment.Shadows.DynamicLimits.R33a

open Alignment.Shadows.DynamicLimits.Shared2

@[sa_reference "DynamicLimits.R33a"]
def T : Prop :=
  (∀ m : DynamicEBCM, m.R0 = staticR0 m.disease m.pgf) ∧
  (∀ (m : DynamicEBCM) (η : ℚ), 0 < η → m.R0 ≠ edgeSwapR0 m.disease m.pgf η)

/-- S1: `DynamicEBCM.R0 = T·ψ''(1)/ψ'(1)`. -/
@[sa_shadow "DynamicLimits.R33a" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.R0 = staticR0 m.disease m.pgf
/-- S2: it is not the R₀ of the dynamic model at any positive rewiring rate. -/
@[sa_shadow "DynamicLimits.R33a" 2]
def S2 : Prop := ∀ (m : DynamicEBCM) (η : ℚ), 0 < η → m.R0 ≠ edgeSwapR0 m.disease m.pgf η

@[sa_ref_forward "DynamicLimits.R33a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DynamicLimits.R33a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "DynamicLimits.R33a"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.DynamicLimits.R33a

/-! ## `DynamicLimits.R33c` (blind)

Text: "In the edge-swapping EBCM, R₀ depends on η (Miller, Slim & Volz 2012, §3.2.1;
`R0_edgeSwap`). [...] In the edge-swapping EBCM, R₀ depends on the rewiring rate η (Miller, Slim &
Volz 2012, §3.2.1; see `R0_edgeSwap`)."

"Depends on η": for every degree record and SIR parameters, two nonnegative rates give different
edge-swapping R₀. -/
namespace Alignment.Shadows.DynamicLimits.R33c

open Alignment.Shadows.DynamicLimits.Shared2

@[sa_reference "DynamicLimits.R33c"]
def T : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData), ∃ η₁ η₂ : ℚ, 0 ≤ η₁ ∧ 0 ≤ η₂ ∧
    edgeSwapR0 p ψ η₁ ≠ edgeSwapR0 p ψ η₂

/-- S1: the edge-swapping R₀ is not constant in η. -/
@[sa_shadow "DynamicLimits.R33c" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData), ∃ η₁ η₂ : ℚ, 0 ≤ η₁ ∧ 0 ≤ η₂ ∧
    edgeSwapR0 p ψ η₁ ≠ edgeSwapR0 p ψ η₂

@[sa_ref_forward "DynamicLimits.R33c" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "DynamicLimits.R33c"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynamicLimits.R33c

/-! ## `DynamicLimits.R35b` (re-authored blind)

Text: "It is not a coarse-graining of the same model: the MFSH R₀ differs from the static R₀
(`R0_static_lt_mfsh`)."

"It" is the fast-rewiring (MFSH) limit. S1: the MFSH R₀ differs from the static R₀
(`m.staticLimit.R0`). S2, S3: a model with the MFSH R₀ is not the coarse-graining F of the dynamic
model nor of its static limit. -/
namespace Alignment.Shadows.DynamicLimits.R35b

open Alignment.Shadows.DynamicLimits.Shared2

@[sa_reference "DynamicLimits.R35b"]
def T : Prop :=
  (∀ m : DynamicEBCM, mfshR0 m.disease m.pgf ≠ m.staticLimit.R0) ∧
  (∀ (m : DynamicEBCM) (e : EpiModel), e.R0 = mfshR0 m.disease m.pgf →
      e ≠ coarseGrain m.toEpiModel) ∧
  (∀ (m : DynamicEBCM) (e : EpiModel), e.R0 = mfshR0 m.disease m.pgf →
      e ≠ coarseGrain m.staticLimit)

/-- S1: the MFSH R₀ differs from the static R₀. -/
@[sa_shadow "DynamicLimits.R35b" 1]
def S1 : Prop := ∀ m : DynamicEBCM, mfshR0 m.disease m.pgf ≠ m.staticLimit.R0
/-- S2: a model with the MFSH R₀ is not F of the dynamic model. -/
@[sa_shadow "DynamicLimits.R35b" 2]
def S2 : Prop :=
  ∀ (m : DynamicEBCM) (e : EpiModel), e.R0 = mfshR0 m.disease m.pgf → e ≠ coarseGrain m.toEpiModel
/-- S3: a model with the MFSH R₀ is not F of the static limit. -/
@[sa_shadow "DynamicLimits.R35b" 3]
def S3 : Prop :=
  ∀ (m : DynamicEBCM) (e : EpiModel), e.R0 = mfshR0 m.disease m.pgf → e ≠ coarseGrain m.staticLimit

@[sa_ref_forward "DynamicLimits.R35b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DynamicLimits.R35b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "DynamicLimits.R35b" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "DynamicLimits.R35b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.DynamicLimits.R35b

/-! ## `DynamicLimits.R36a` (re-authored blind)

Text: "**Result 36.** For Poisson networks, the value T·κ stored by `fastRewiringLimit` equals the
static EBCM R₀."

S1: for a Poisson degree record, `fastRewiringLimit` stores `T·κ` (`T = β/(β+γ)`); S2: this equals
the static EBCM R₀ `m.staticLimit.R0`. -/
namespace Alignment.Shadows.DynamicLimits.R36a

@[sa_reference "DynamicLimits.R36a"]
def T : Prop :=
  (∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
      (DynamicEBCM.mk p (PGFData.poisson κ hκ)).fastRewiringLimit.R0 = p.β / (p.β + p.γ) * κ) ∧
  (∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
      (DynamicEBCM.mk p (PGFData.poisson κ hκ)).fastRewiringLimit.R0 =
        (DynamicEBCM.mk p (PGFData.poisson κ hκ)).staticLimit.R0)

/-- S1: for Poisson, the stored fast-rewiring value is `T·κ`. -/
@[sa_shadow "DynamicLimits.R36a" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
    (DynamicEBCM.mk p (PGFData.poisson κ hκ)).fastRewiringLimit.R0 = p.β / (p.β + p.γ) * κ
/-- S2: for Poisson, the stored value equals the static EBCM R₀. -/
@[sa_shadow "DynamicLimits.R36a" 2]
def S2 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
    (DynamicEBCM.mk p (PGFData.poisson κ hκ)).fastRewiringLimit.R0 =
      (DynamicEBCM.mk p (PGFData.poisson κ hκ)).staticLimit.R0

@[sa_ref_forward "DynamicLimits.R36a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DynamicLimits.R36a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "DynamicLimits.R36a"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.DynamicLimits.R36a

/-! ## `DynamicLimits.R37a` (re-authored blind)

Text: "**Result 37.** Some degree record has a stored fast-rewiring value T·κ different from the
static EBCM R₀. The genuine fast-rewiring (MFSH) R₀ exceeds the static R₀ for every degree law
(`R0_static_lt_mfsh`)." -/
namespace Alignment.Shadows.DynamicLimits.R37a

open Alignment.Shadows.DynamicLimits.Shared2

@[sa_reference "DynamicLimits.R37a"]
def T : Prop :=
  (∀ m : DynamicEBCM, m.fastRewiringLimit.R0 = m.disease.β / (m.disease.β + m.disease.γ) * m.pgf.mean) ∧
  (∃ m : DynamicEBCM, m.fastRewiringLimit.R0 ≠ m.staticLimit.R0) ∧
  (∀ m : DynamicEBCM, m.staticLimit.R0 < mfshR0 m.disease m.pgf)

/-- S1: the stored fast-rewiring value is `T·κ`. -/
@[sa_shadow "DynamicLimits.R37a" 1]
def S1 : Prop :=
  ∀ m : DynamicEBCM, m.fastRewiringLimit.R0 = m.disease.β / (m.disease.β + m.disease.γ) * m.pgf.mean
/-- S2: some record has stored value different from the static EBCM R₀. -/
@[sa_shadow "DynamicLimits.R37a" 2]
def S2 : Prop := ∃ m : DynamicEBCM, m.fastRewiringLimit.R0 ≠ m.staticLimit.R0
/-- S3: the MFSH R₀ exceeds the static R₀ for every record. -/
@[sa_shadow "DynamicLimits.R37a" 3]
def S3 : Prop := ∀ m : DynamicEBCM, m.staticLimit.R0 < mfshR0 m.disease m.pgf

@[sa_ref_forward "DynamicLimits.R37a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DynamicLimits.R37a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "DynamicLimits.R37a" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "DynamicLimits.R37a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.DynamicLimits.R37a

/-! ## `DynamicLimits.R37b` (blind)

Text: "Witness: a network with mean κ=3, second factorial=15 (excess=5). T=1/2, so EBCM R₀ = 5/2
and T·κ = 3/2; with β = γ = 1 the MFSH R₀ is 5 + 1 = 6."

The witness record has `β = γ = 1` (so T = 1/2) and PGF data `mean = 3`, `secondFactorial = 15`.
"EBCM R₀" is `DynamicEBCM.R0`; "T·κ" is the value stored by `fastRewiringLimit`; the MFSH R₀ is
`(β/γ)(excess + 1)` with the excess degree `PGFData.excessDegree`. -/
namespace Alignment.Shadows.DynamicLimits.R37b

/-- The witness: `β = γ = 1`, mean 3, second factorial moment 15. -/
def wit : DynamicEBCM :=
  ⟨⟨1, 1, by norm_num, by norm_num⟩, ⟨3, 15, by norm_num, by norm_num⟩⟩

@[sa_reference "DynamicLimits.R37b"]
def T : Prop :=
  wit.pgf.excessDegree = 5 ∧ wit.disease.transmissibility = 1 / 2 ∧ wit.R0 = 5 / 2 ∧
    wit.fastRewiringLimit.R0 = 3 / 2 ∧
    wit.disease.β / wit.disease.γ * (wit.pgf.excessDegree + 1) = 6

/-- S1: the witness has excess degree 5. -/
@[sa_shadow "DynamicLimits.R37b" 1]
def S1 : Prop := wit.pgf.excessDegree = 5
/-- S2: its transmissibility is 1/2. -/
@[sa_shadow "DynamicLimits.R37b" 2]
def S2 : Prop := wit.disease.transmissibility = 1 / 2
/-- S3: its EBCM R₀ is 5/2. -/
@[sa_shadow "DynamicLimits.R37b" 3]
def S3 : Prop := wit.R0 = 5 / 2
/-- S4: its stored fast-rewiring value T·κ is 3/2. -/
@[sa_shadow "DynamicLimits.R37b" 4]
def S4 : Prop := wit.fastRewiringLimit.R0 = 3 / 2
/-- S5: its MFSH R₀ `(β/γ)(excess + 1)` is 6. -/
@[sa_shadow "DynamicLimits.R37b" 5]
def S5 : Prop := wit.disease.β / wit.disease.γ * (wit.pgf.excessDegree + 1) = 6

@[sa_ref_forward "DynamicLimits.R37b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DynamicLimits.R37b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "DynamicLimits.R37b" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "DynamicLimits.R37b" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "DynamicLimits.R37b" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2
@[sa_complete "DynamicLimits.R37b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.DynamicLimits.R37b

/-! ## `DynamicLimits.R40b` (blind)

Text: "Combined with Hierarchy.lean, this gives, for N ≥ 4: Mean-field (3) < Static EBCM (4) <
Dynamic EBCM (5) < Pair (12N) < Full (3^N); the last inequality fails for N ≤ 3."

Dimensions: mean-field, static EBCM, pair and full levels are `levelDim` of `ModelLevel.meanField`,
`.edgeBased`, `.pairApproximation`, `.fullStochastic` (Hierarchy); the dynamic EBCM is
`DynamicEBCM.dim`. The parenthesised values are required too.
-- AMBIGUITY: "fails for N ≤ 3" read for networks with at least one node (1 ≤ N ≤ 3); at N = 0,
12·0 < 3⁰. -/
namespace Alignment.Shadows.DynamicLimits.R40b

@[sa_reference "DynamicLimits.R40b"]
def T : Prop :=
  (∀ N : ℕ, 4 ≤ N → levelDim .meanField N < levelDim .edgeBased N) ∧
  (∀ (N : ℕ) (m : DynamicEBCM), 4 ≤ N → levelDim .edgeBased N < m.dim) ∧
  (∀ (N : ℕ) (m : DynamicEBCM), 4 ≤ N → m.dim < levelDim .pairApproximation N) ∧
  (∀ N : ℕ, 4 ≤ N → levelDim .pairApproximation N < levelDim .fullStochastic N) ∧
  (∀ N : ℕ, 1 ≤ N → N ≤ 3 → ¬ levelDim .pairApproximation N < levelDim .fullStochastic N) ∧
  (∀ N : ℕ, levelDim .meanField N = 3) ∧ (∀ N : ℕ, levelDim .edgeBased N = 4) ∧
  (∀ m : DynamicEBCM, m.dim = 5) ∧ (∀ N : ℕ, levelDim .pairApproximation N = 12 * N) ∧
  (∀ N : ℕ, levelDim .fullStochastic N = 3 ^ N)

/-- S1: mean-field < static EBCM. -/
@[sa_shadow "DynamicLimits.R40b" 1]
def S1 : Prop := ∀ N : ℕ, 4 ≤ N → levelDim .meanField N < levelDim .edgeBased N
/-- S2: static EBCM < dynamic EBCM. -/
@[sa_shadow "DynamicLimits.R40b" 2]
def S2 : Prop := ∀ (N : ℕ) (m : DynamicEBCM), 4 ≤ N → levelDim .edgeBased N < m.dim
/-- S3: dynamic EBCM < pair. -/
@[sa_shadow "DynamicLimits.R40b" 3]
def S3 : Prop := ∀ (N : ℕ) (m : DynamicEBCM), 4 ≤ N → m.dim < levelDim .pairApproximation N
/-- S4: pair < full. -/
@[sa_shadow "DynamicLimits.R40b" 4]
def S4 : Prop := ∀ N : ℕ, 4 ≤ N → levelDim .pairApproximation N < levelDim .fullStochastic N
/-- S5: pair < full fails for 1 ≤ N ≤ 3. -/
@[sa_shadow "DynamicLimits.R40b" 5]
def S5 : Prop :=
  ∀ N : ℕ, 1 ≤ N → N ≤ 3 → ¬ levelDim .pairApproximation N < levelDim .fullStochastic N
/-- S6: mean-field has dimension 3. -/
@[sa_shadow "DynamicLimits.R40b" 6]
def S6 : Prop := ∀ N : ℕ, levelDim .meanField N = 3
/-- S7: the static EBCM has dimension 4. -/
@[sa_shadow "DynamicLimits.R40b" 7]
def S7 : Prop := ∀ N : ℕ, levelDim .edgeBased N = 4
/-- S8: the dynamic EBCM has dimension 5. -/
@[sa_shadow "DynamicLimits.R40b" 8]
def S8 : Prop := ∀ m : DynamicEBCM, m.dim = 5
/-- S9: the pair level has dimension 12N. -/
@[sa_shadow "DynamicLimits.R40b" 9]
def S9 : Prop := ∀ N : ℕ, levelDim .pairApproximation N = 12 * N
/-- S10: the full level has dimension 3^N. -/
@[sa_shadow "DynamicLimits.R40b" 10]
def S10 : Prop := ∀ N : ℕ, levelDim .fullStochastic N = 3 ^ N

@[sa_ref_forward "DynamicLimits.R40b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DynamicLimits.R40b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "DynamicLimits.R40b" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "DynamicLimits.R40b" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "DynamicLimits.R40b" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2.1
@[sa_ref_forward "DynamicLimits.R40b" 6] theorem ref_fwd6 : T → S6 := fun t => t.2.2.2.2.2.1
@[sa_ref_forward "DynamicLimits.R40b" 7] theorem ref_fwd7 : T → S7 :=
  fun t => t.2.2.2.2.2.2.1
@[sa_ref_forward "DynamicLimits.R40b" 8] theorem ref_fwd8 : T → S8 :=
  fun t => t.2.2.2.2.2.2.2.1
@[sa_ref_forward "DynamicLimits.R40b" 9] theorem ref_fwd9 : T → S9 :=
  fun t => t.2.2.2.2.2.2.2.2.1
@[sa_ref_forward "DynamicLimits.R40b" 10] theorem ref_fwd10 : T → S10 :=
  fun t => t.2.2.2.2.2.2.2.2.2
@[sa_complete "DynamicLimits.R40b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7) (s8 : S8)
    (s9 : S9) (s10 : S10) : T :=
  ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩

end Alignment.Shadows.DynamicLimits.R40b

/-! ## `DynamicLimits.fastRewiringR0MeanDegree` (blind)

Text: "Its R₀ is (β/γ)⟨K²⟩/⟨K⟩ = (β/γ)(ψ''(1)/ψ'(1) + 1) (`R0_mfsh`), which keeps degree
heterogeneity. The R₀ stored here, T·ψ'(1) = βκ/(β+γ), is not that limit; it is kept for
compatibility (Results 36, 37)."

"Its" is the fast-rewiring limit. S1: the fast-rewiring limit of the edge-swapping R₀ is
`(β/γ)⟨K²⟩/⟨K⟩`, with `⟨K²⟩ = ψ''(1) + ψ'(1)`; S2: it keeps degree heterogeneity; S3: the value
stored by `fastRewiringLimit` is `βκ/(β+γ)`; S4: the stored value is not that limit (for some
record). "Kept for compatibility" is not a proposition. -/
namespace Alignment.Shadows.DynamicLimits.fastRewiringR0MeanDegree

open Alignment.Shadows.DynamicLimits.Shared2 Filter Topology

@[sa_reference "DynamicLimits.fastRewiringR0MeanDegree"]
def T : Prop :=
  (∀ (p : SIRParams) (ψ : PGFData), Tendsto (fun η : ℝ => edgeSwapR0R p ψ η) atTop
      (𝓝 ((p.β : ℝ) / p.γ * (((ψ.secondFactorial : ℝ) + ψ.mean) / ψ.mean)))) ∧
  (∀ (p : SIRParams) (ψ₁ ψ₂ : PGFData), ψ₁.mean = ψ₂.mean →
      ψ₁.secondFactorial ≠ ψ₂.secondFactorial → mfshR0 p ψ₁ ≠ mfshR0 p ψ₂) ∧
  (∀ m : DynamicEBCM,
      m.fastRewiringLimit.R0 = m.disease.β * m.pgf.mean / (m.disease.β + m.disease.γ)) ∧
  (∃ m : DynamicEBCM, m.fastRewiringLimit.R0 ≠ mfshR0 m.disease m.pgf)

/-- S1: the fast-rewiring limit of R₀ is `(β/γ)⟨K²⟩/⟨K⟩`. -/
@[sa_shadow "DynamicLimits.fastRewiringR0MeanDegree" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData), Tendsto (fun η : ℝ => edgeSwapR0R p ψ η) atTop
    (𝓝 ((p.β : ℝ) / p.γ * (((ψ.secondFactorial : ℝ) + ψ.mean) / ψ.mean)))
/-- S2: the MFSH R₀ keeps degree heterogeneity. -/
@[sa_shadow "DynamicLimits.fastRewiringR0MeanDegree" 2]
def S2 : Prop :=
  ∀ (p : SIRParams) (ψ₁ ψ₂ : PGFData), ψ₁.mean = ψ₂.mean →
    ψ₁.secondFactorial ≠ ψ₂.secondFactorial → mfshR0 p ψ₁ ≠ mfshR0 p ψ₂
/-- S3: the stored value is `βκ/(β+γ)`. -/
@[sa_shadow "DynamicLimits.fastRewiringR0MeanDegree" 3]
def S3 : Prop :=
  ∀ m : DynamicEBCM, m.fastRewiringLimit.R0 = m.disease.β * m.pgf.mean / (m.disease.β + m.disease.γ)
/-- S4: the stored value is not the MFSH limit. -/
@[sa_shadow "DynamicLimits.fastRewiringR0MeanDegree" 4]
def S4 : Prop := ∃ m : DynamicEBCM, m.fastRewiringLimit.R0 ≠ mfshR0 m.disease m.pgf

@[sa_ref_forward "DynamicLimits.fastRewiringR0MeanDegree" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "DynamicLimits.fastRewiringR0MeanDegree" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "DynamicLimits.fastRewiringR0MeanDegree" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "DynamicLimits.fastRewiringR0MeanDegree" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2
@[sa_complete "DynamicLimits.fastRewiringR0MeanDegree"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.DynamicLimits.fastRewiringR0MeanDegree

/-! ## `DynamicLimits.header.fastRewiringCollapse` (blind)

Text: "**Fast-rewiring limit (η → ∞)**: The network reshuffles so quickly that partnerships are
fleeting. The system approaches the mean-field social-heterogeneity (MFSH) model of Miller, Slim &
Volz (2012): nodes keep their degrees, so degree heterogeneity survives, and R₀ tends to
(β/γ)⟨K²⟩/⟨K⟩."

S1: as η → ∞ the edge-swapping R₀ tends to `(β/γ)⟨K²⟩/⟨K⟩`; S2: degree heterogeneity survives
(the limit distinguishes degree laws of equal mean). The mechanism ("partnerships are fleeting")
is descriptive. -/
namespace Alignment.Shadows.DynamicLimits.header_fastRewiringCollapse

open Alignment.Shadows.DynamicLimits.Shared2 Filter Topology

/-- `(β/γ)⟨K²⟩/⟨K⟩` with `⟨K²⟩ = ψ''(1) + ψ'(1)`, `⟨K⟩ = ψ'(1)`. -/
def mfshLimit (p : SIRParams) (ψ : PGFData) : ℝ :=
  (p.β : ℝ) / p.γ * (((ψ.secondFactorial : ℝ) + ψ.mean) / ψ.mean)

@[sa_reference "DynamicLimits.header.fastRewiringCollapse"]
def T : Prop :=
  (∀ (p : SIRParams) (ψ : PGFData),
      Tendsto (fun η : ℝ => edgeSwapR0R p ψ η) atTop (𝓝 (mfshLimit p ψ))) ∧
  (∀ (p : SIRParams) (ψ₁ ψ₂ : PGFData), ψ₁.mean = ψ₂.mean →
      ψ₁.secondFactorial ≠ ψ₂.secondFactorial → mfshLimit p ψ₁ ≠ mfshLimit p ψ₂)

/-- S1: the fast-rewiring limit of R₀ is `(β/γ)⟨K²⟩/⟨K⟩`. -/
@[sa_shadow "DynamicLimits.header.fastRewiringCollapse" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData),
    Tendsto (fun η : ℝ => edgeSwapR0R p ψ η) atTop (𝓝 (mfshLimit p ψ))
/-- S2: the limit keeps degree heterogeneity. -/
@[sa_shadow "DynamicLimits.header.fastRewiringCollapse" 2]
def S2 : Prop :=
  ∀ (p : SIRParams) (ψ₁ ψ₂ : PGFData), ψ₁.mean = ψ₂.mean →
    ψ₁.secondFactorial ≠ ψ₂.secondFactorial → mfshLimit p ψ₁ ≠ mfshLimit p ψ₂

@[sa_ref_forward "DynamicLimits.header.fastRewiringCollapse" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "DynamicLimits.header.fastRewiringCollapse" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "DynamicLimits.header.fastRewiringCollapse"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.DynamicLimits.header_fastRewiringCollapse

/-! ## `DynamicLimits.header.interpolation` (re-authored blind)

Text: "The dynamic model thus interpolates between two extremes: MFSH (dim 3 as recorded) ← fast
rewiring — Dynamic (dim 5) — static → EBCM (dim 4)"

The recorded dimensions: fast-rewiring limit 3, dynamic model 5 (both `m.dim` and
`m.toEpiModel.dim`), static limit 4. -- AMBIGUITY: "interpolates" is read through the recorded
dimensions only, as the text annotates each model with its recorded dimension. -/
namespace Alignment.Shadows.DynamicLimits.header_interpolation

@[sa_reference "DynamicLimits.header.interpolation"]
def T : Prop :=
  (∀ m : DynamicEBCM, m.fastRewiringLimit.dim = 3) ∧ (∀ m : DynamicEBCM, m.dim = 5) ∧
  (∀ m : DynamicEBCM, m.toEpiModel.dim = 5) ∧ (∀ m : DynamicEBCM, m.staticLimit.dim = 4)

/-- S1: the fast-rewiring (MFSH) record has dimension 3. -/
@[sa_shadow "DynamicLimits.header.interpolation" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.fastRewiringLimit.dim = 3
/-- S2: the dynamic model has dimension 5 (`DynamicEBCM.dim`). -/
@[sa_shadow "DynamicLimits.header.interpolation" 2]
def S2 : Prop := ∀ m : DynamicEBCM, m.dim = 5
/-- S3: the dynamic model has dimension 5 (as an `EpiModel`). -/
@[sa_shadow "DynamicLimits.header.interpolation" 3]
def S3 : Prop := ∀ m : DynamicEBCM, m.toEpiModel.dim = 5
/-- S4: the static limit has dimension 4. -/
@[sa_shadow "DynamicLimits.header.interpolation" 4]
def S4 : Prop := ∀ m : DynamicEBCM, m.staticLimit.dim = 4

@[sa_ref_forward "DynamicLimits.header.interpolation" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DynamicLimits.header.interpolation" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "DynamicLimits.header.interpolation" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "DynamicLimits.header.interpolation" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2
@[sa_complete "DynamicLimits.header.interpolation"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.DynamicLimits.header_interpolation

/-! ## `DynamicLimits.table.R32` (re-authored blind)

Text: "| 32 | Fast-rewiring limit record: dim 5 → 3 |" -/
namespace Alignment.Shadows.DynamicLimits.table_R32

@[sa_reference "DynamicLimits.table.R32"]
def T : Prop :=
  (∀ m : DynamicEBCM, m.toEpiModel.dim = 5) ∧ (∀ m : DynamicEBCM, m.dim = 5) ∧
  (∀ m : DynamicEBCM, m.fastRewiringLimit.dim = 3)

/-- S1: the dynamic record has dimension 5 (as an `EpiModel`). -/
@[sa_shadow "DynamicLimits.table.R32" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.toEpiModel.dim = 5
/-- S2: the dynamic record has dimension 5 (`DynamicEBCM.dim`). -/
@[sa_shadow "DynamicLimits.table.R32" 2]
def S2 : Prop := ∀ m : DynamicEBCM, m.dim = 5
/-- S3: the fast-rewiring limit record has dimension 3. -/
@[sa_shadow "DynamicLimits.table.R32" 3]
def S3 : Prop := ∀ m : DynamicEBCM, m.fastRewiringLimit.dim = 3

@[sa_ref_forward "DynamicLimits.table.R32" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DynamicLimits.table.R32" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "DynamicLimits.table.R32" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "DynamicLimits.table.R32"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.DynamicLimits.table_R32

/-! ## `DynamicLimits.table.R33` (re-authored blind)

Text: "| 33 | `DynamicEBCM.R0` stores the static-limit R₀ only |"

S1: `DynamicEBCM.R0` is the static-limit R₀ `T·ψ''(1)/ψ'(1)`; S2: it equals the R₀ of the static
limit record; S3 ("only"): it is not the R₀ of the dynamic model at any positive rewiring rate. -/
namespace Alignment.Shadows.DynamicLimits.table_R33

open Alignment.Shadows.DynamicLimits.Shared2

@[sa_reference "DynamicLimits.table.R33"]
def T : Prop :=
  (∀ m : DynamicEBCM, m.R0 = staticR0 m.disease m.pgf) ∧
  (∀ m : DynamicEBCM, m.R0 = m.staticLimit.R0) ∧
  (∀ (m : DynamicEBCM) (η : ℚ), 0 < η → m.R0 ≠ edgeSwapR0 m.disease m.pgf η)

/-- S1: `DynamicEBCM.R0 = T·ψ''(1)/ψ'(1)`. -/
@[sa_shadow "DynamicLimits.table.R33" 1]
def S1 : Prop := ∀ m : DynamicEBCM, m.R0 = staticR0 m.disease m.pgf
/-- S2: `DynamicEBCM.R0` is the static limit's R₀. -/
@[sa_shadow "DynamicLimits.table.R33" 2]
def S2 : Prop := ∀ m : DynamicEBCM, m.R0 = m.staticLimit.R0
/-- S3: it is not the dynamic R₀ at a positive rewiring rate. -/
@[sa_shadow "DynamicLimits.table.R33" 3]
def S3 : Prop := ∀ (m : DynamicEBCM) (η : ℚ), 0 < η → m.R0 ≠ edgeSwapR0 m.disease m.pgf η

@[sa_ref_forward "DynamicLimits.table.R33" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DynamicLimits.table.R33" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "DynamicLimits.table.R33" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "DynamicLimits.table.R33"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.DynamicLimits.table_R33

/-! ## `DynamicLimits.table.R35` (re-authored blind)

Text: "| 35 | Fast-rewiring record has the dimension of a coarse-graining |" -/
namespace Alignment.Shadows.DynamicLimits.table_R35

@[sa_reference "DynamicLimits.table.R35"]
def T : Prop := ∀ (m : DynamicEBCM) (e : EpiModel), m.fastRewiringLimit.dim = (coarseGrain e).dim

/-- S1: the fast-rewiring record has the dimension of every coarse-graining. -/
@[sa_shadow "DynamicLimits.table.R35" 1]
def S1 : Prop := ∀ (m : DynamicEBCM) (e : EpiModel), m.fastRewiringLimit.dim = (coarseGrain e).dim

@[sa_ref_forward "DynamicLimits.table.R35" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "DynamicLimits.table.R35"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynamicLimits.table_R35

/-! ## `DynamicLimits.table.R36` (re-authored blind)

Text: "| 36 | For Poisson, the stored T·κ equals the static R₀ |" -/
namespace Alignment.Shadows.DynamicLimits.table_R36

@[sa_reference "DynamicLimits.table.R36"]
def T : Prop :=
  (∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
      (DynamicEBCM.mk p (PGFData.poisson κ hκ)).fastRewiringLimit.R0 = p.β / (p.β + p.γ) * κ) ∧
  (∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
      (DynamicEBCM.mk p (PGFData.poisson κ hκ)).fastRewiringLimit.R0 =
        (DynamicEBCM.mk p (PGFData.poisson κ hκ)).staticLimit.R0)

/-- S1: for Poisson, the stored value is `T·κ`. -/
@[sa_shadow "DynamicLimits.table.R36" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
    (DynamicEBCM.mk p (PGFData.poisson κ hκ)).fastRewiringLimit.R0 = p.β / (p.β + p.γ) * κ
/-- S2: for Poisson, the stored value equals the static R₀. -/
@[sa_shadow "DynamicLimits.table.R36" 2]
def S2 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
    (DynamicEBCM.mk p (PGFData.poisson κ hκ)).fastRewiringLimit.R0 =
      (DynamicEBCM.mk p (PGFData.poisson κ hκ)).staticLimit.R0

@[sa_ref_forward "DynamicLimits.table.R36" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DynamicLimits.table.R36" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "DynamicLimits.table.R36"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.DynamicLimits.table_R36

/-! ## `DynamicLimits.table.R37` (re-authored blind)

Text: "| 37 | Some record has T·κ ≠ static R₀; MFSH R₀ > static R₀ |" -/
namespace Alignment.Shadows.DynamicLimits.table_R37

open Alignment.Shadows.DynamicLimits.Shared2

@[sa_reference "DynamicLimits.table.R37"]
def T : Prop :=
  (∀ m : DynamicEBCM, m.fastRewiringLimit.R0 = m.disease.β / (m.disease.β + m.disease.γ) * m.pgf.mean) ∧
  (∃ m : DynamicEBCM, m.fastRewiringLimit.R0 ≠ m.staticLimit.R0) ∧
  (∀ m : DynamicEBCM, m.staticLimit.R0 < mfshR0 m.disease m.pgf)

/-- S1: the stored fast-rewiring value is `T·κ`. -/
@[sa_shadow "DynamicLimits.table.R37" 1]
def S1 : Prop :=
  ∀ m : DynamicEBCM, m.fastRewiringLimit.R0 = m.disease.β / (m.disease.β + m.disease.γ) * m.pgf.mean
/-- S2: some record has `T·κ ≠` static R₀. -/
@[sa_shadow "DynamicLimits.table.R37" 2]
def S2 : Prop := ∃ m : DynamicEBCM, m.fastRewiringLimit.R0 ≠ m.staticLimit.R0
/-- S3: MFSH R₀ > static R₀ for every record. -/
@[sa_shadow "DynamicLimits.table.R37" 3]
def S3 : Prop := ∀ m : DynamicEBCM, m.staticLimit.R0 < mfshR0 m.disease m.pgf

@[sa_ref_forward "DynamicLimits.table.R37" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DynamicLimits.table.R37" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "DynamicLimits.table.R37" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "DynamicLimits.table.R37"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.DynamicLimits.table_R37

/-! ## `DynamicLimits.r0EdgeSwapZero` (blind)

Text: "At rewiring rate η = 0 the edge-swapping R₀ is the static-limit R₀ T·ψ''(1)/ψ'(1)."

S1: the edge-swapping R₀ at η = 0 is `T·ψ''(1)/ψ'(1)`; S2: it is the R₀ of the static-limit record
of the dynamic model with the same data. -/
namespace Alignment.Shadows.DynamicLimits.r0EdgeSwapZero

open Alignment.Shadows.DynamicLimits.Shared2

@[sa_reference "DynamicLimits.r0EdgeSwapZero"]
def T : Prop :=
  (∀ (p : SIRParams) (ψ : PGFData), edgeSwapR0 p ψ 0 = staticR0 p ψ) ∧
  (∀ (p : SIRParams) (ψ : PGFData), edgeSwapR0 p ψ 0 = (DynamicEBCM.mk p ψ).staticLimit.R0)

/-- S1: at η = 0 the edge-swapping R₀ is `T·ψ''(1)/ψ'(1)`. -/
@[sa_shadow "DynamicLimits.r0EdgeSwapZero" 1]
def S1 : Prop := ∀ (p : SIRParams) (ψ : PGFData), edgeSwapR0 p ψ 0 = staticR0 p ψ
/-- S2: at η = 0 it is the static-limit record's R₀. -/
@[sa_shadow "DynamicLimits.r0EdgeSwapZero" 2]
def S2 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData), edgeSwapR0 p ψ 0 = (DynamicEBCM.mk p ψ).staticLimit.R0

@[sa_ref_forward "DynamicLimits.r0EdgeSwapZero" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "DynamicLimits.r0EdgeSwapZero" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "DynamicLimits.r0EdgeSwapZero"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.DynamicLimits.r0EdgeSwapZero

/-! ## `DynamicLimits.r0EdgeSwapTendstoMfsh` (blind)

Text: "As the rewiring rate η → ∞, the edge-swapping R₀ tends to the MFSH R₀
(β/γ)(ψ''(1)/ψ'(1) + 1)." -/
namespace Alignment.Shadows.DynamicLimits.r0EdgeSwapTendstoMfsh

open Alignment.Shadows.DynamicLimits.Shared2 Filter Topology

@[sa_reference "DynamicLimits.r0EdgeSwapTendstoMfsh"]
def T : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData),
    Tendsto (fun η : ℝ => edgeSwapR0R p ψ η) atTop (𝓝 ((mfshR0 p ψ : ℚ) : ℝ))

/-- S1: `R₀(η) → (β/γ)(ψ''(1)/ψ'(1) + 1)` as η → ∞. -/
@[sa_shadow "DynamicLimits.r0EdgeSwapTendstoMfsh" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData),
    Tendsto (fun η : ℝ => edgeSwapR0R p ψ η) atTop (𝓝 ((mfshR0 p ψ : ℚ) : ℝ))

@[sa_ref_forward "DynamicLimits.r0EdgeSwapTendstoMfsh" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "DynamicLimits.r0EdgeSwapTendstoMfsh"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynamicLimits.r0EdgeSwapTendstoMfsh

/-! ## `DynamicLimits.r0StaticLtMfsh` (blind)

Text: "The MFSH (fast-rewiring) R₀ exceeds the static-limit R₀ for every degree record:
(β/γ)(ψ''(1)/ψ'(1) + 1) > β/(β+γ) · ψ''(1)/ψ'(1)." -/
namespace Alignment.Shadows.DynamicLimits.r0StaticLtMfsh

open Alignment.Shadows.DynamicLimits.Shared2

@[sa_reference "DynamicLimits.r0StaticLtMfsh"]
def T : Prop := ∀ (p : SIRParams) (ψ : PGFData), staticR0 p ψ < mfshR0 p ψ

/-- S1: the MFSH R₀ exceeds the static-limit R₀. -/
@[sa_shadow "DynamicLimits.r0StaticLtMfsh" 1]
def S1 : Prop := ∀ (p : SIRParams) (ψ : PGFData), staticR0 p ψ < mfshR0 p ψ

@[sa_ref_forward "DynamicLimits.r0StaticLtMfsh" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "DynamicLimits.r0StaticLtMfsh"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynamicLimits.r0StaticLtMfsh

/-! ## `DynamicLimits.r0MfshPoisson` (blind)

Text: "For Poisson degrees the MFSH (fast-rewiring) R₀ is (β/γ)(κ + 1)." -/
namespace Alignment.Shadows.DynamicLimits.r0MfshPoisson

open Alignment.Shadows.DynamicLimits.Shared2

@[sa_reference "DynamicLimits.r0MfshPoisson"]
def T : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ), mfshR0 p (PGFData.poisson κ hκ) = p.β / p.γ * (κ + 1)

/-- S1: for Poisson degrees, the MFSH R₀ is `(β/γ)(κ + 1)`. -/
@[sa_shadow "DynamicLimits.r0MfshPoisson" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ), mfshR0 p (PGFData.poisson κ hκ) = p.β / p.γ * (κ + 1)

@[sa_ref_forward "DynamicLimits.r0MfshPoisson" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "DynamicLimits.r0MfshPoisson"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.DynamicLimits.r0MfshPoisson

end
