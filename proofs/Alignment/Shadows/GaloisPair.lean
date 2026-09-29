import Alignment.Registry
import EBCMCategory.GaloisPair

/-!
# Blind shadow sets for group `GaloisPair`

Written blind. The author read only the claims' entries in `Alignment/claims_blind.yaml` (fields
`id, group, source, text`), `Alignment/DataTypes/GaloisPair.md`, `Alignment/README.md`,
`Alignment/Example/ExampleShadows.lean` and `SA-PASS_SKILL.md`. The only Lean information used
came from `#check` on the data types and operations listed in `DataTypes/GaloisPair.md`.

Vocabulary (from `DataTypes/GaloisPair.md`):

* `EpiModel` has fields `dim : ℕ` and `R0 : ℚ`, with its `Preorder` instance (refinement, `≤`).
* F = `coarseGrain : EpiModel → EpiModel` ("Projects any model to a 3-dimensional node model,
  preserving R₀").
* G = `poissonLift : EpiModel → EpiModel` ("Embeds a node model into the canonical 4D edge
  model with Poisson degree distribution").
* `nodeModel : SIRParams → ℚ → EpiModel` ("A node-based SIR model: 3 state variables").
* `edgeModel : SIRParams → PGFData → EpiModel` ("An edge-based SIR model: 4 state variables").

Reading conventions used for every claim below:

* `F ∘ G ∘ F = F` and similar equations are read literally, as equalities of functions
  `EpiModel → EpiModel`. They are equivalent to the pointwise statements by `funext`/`congrFun`.
* "Φ preserves R₀ (exactly)" is read as `∀ M, (Φ M).R0 = M.R0`. "Exactly" means equality, not
  an approximation or an inequality.
* F and G are total on `EpiModel`, and F's docstring says it projects *any* model, so the primary
  reading of every universal claim quantifies over all of `EpiModel`.
* Where the text names the model kind with a variable letter (`N` for node models in Result 10,
  `E` for edge models in Result 11), the restricted reading over the vocabulary's node/edge
  model constructors (`nodeModel`, `edgeModel`) is added as a separate shadow. It is implied by
  the universal reading, so it does not change `T`.
* "G ∘ F ≠ id (the connection is lossy)": besides the literal function inequality on
  `EpiModel`, the reading on edge models (the domain of G ∘ F in the Node/Edge connection) is a
  separate shadow. That reading is *stronger*: the round trip must fail to be the identity on the
  edge models built by `edgeModel`, not only on some arbitrary `EpiModel`.

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace). Ids of that pass not formalised (remarks on proof status, on which notions the library
defines, or cited results needing models the vocabulary lacks): `R14c`.
-/

/-! ## Header prose (module docstring) -/

namespace Alignment.Shadows.GaloisPair.header_idempotency

/-! ### `GaloisPair.header.idempotency`

Blind text: "F ∘ G ∘ F = F and G ∘ F ∘ G = G (idempotency)" -/

/-- Intended statement: both idempotency equations hold as equalities of functions. -/
@[sa_reference "GaloisPair.header.idempotency"]
def T : Prop :=
  coarseGrain ∘ poissonLift ∘ coarseGrain = coarseGrain ∧
    poissonLift ∘ coarseGrain ∘ poissonLift = poissonLift

/-- S1: F ∘ G ∘ F = F. -/
@[sa_shadow "GaloisPair.header.idempotency" 1]
def S1 : Prop := coarseGrain ∘ poissonLift ∘ coarseGrain = coarseGrain

/-- S2: G ∘ F ∘ G = G. -/
@[sa_shadow "GaloisPair.header.idempotency" 2]
def S2 : Prop := poissonLift ∘ coarseGrain ∘ poissonLift = poissonLift

@[sa_ref_forward "GaloisPair.header.idempotency" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "GaloisPair.header.idempotency" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "GaloisPair.header.idempotency"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.GaloisPair.header_idempotency

namespace Alignment.Shadows.GaloisPair.header_FGPreservesR0

/-! ### `GaloisPair.header.FGPreservesR0`

Blind text: "F ∘ G preserves R₀ exactly" -/

-- AMBIGUITY: "F ∘ G preserves R₀" - over all models or only node models (F ∘ G is the Node
-- round trip)? Read over all of `EpiModel`, since F and G are total there. The node-only
-- reading is weaker and implied, so it is not a separate shadow.

/-- Intended statement: for every model M, the round trip F ∘ G leaves R₀ unchanged. -/
@[sa_reference "GaloisPair.header.FGPreservesR0"]
def T : Prop := ∀ M : EpiModel, ((coarseGrain ∘ poissonLift) M).R0 = M.R0

/-- S1: F ∘ G preserves R₀ exactly, for every model. -/
@[sa_shadow "GaloisPair.header.FGPreservesR0" 1]
def S1 : Prop := ∀ M : EpiModel, ((coarseGrain ∘ poissonLift) M).R0 = M.R0

@[sa_ref_forward "GaloisPair.header.FGPreservesR0" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "GaloisPair.header.FGPreservesR0"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.GaloisPair.header_FGPreservesR0

/-! ## Header table rows -/

namespace Alignment.Shadows.GaloisPair.table_R9

/-! ### `GaloisPair.table.R9`

Blind text: "| 9 | G is monotone |" -/

/-- Intended statement: G is monotone for the refinement preorder on `EpiModel`. -/
@[sa_reference "GaloisPair.table.R9"]
def T : Prop := Monotone poissonLift

/-- S1: `M ≤ M'` implies `G M ≤ G M'`. -/
@[sa_shadow "GaloisPair.table.R9" 1]
def S1 : Prop := ∀ M M' : EpiModel, M ≤ M' → poissonLift M ≤ poissonLift M'

@[sa_ref_forward "GaloisPair.table.R9" 1]
theorem ref_fwd1 : T → S1 := fun t _ _ h => t h

@[sa_complete "GaloisPair.table.R9"]
theorem complete (s1 : S1) : T := fun M M' h => s1 M M' h

end Alignment.Shadows.GaloisPair.table_R9

namespace Alignment.Shadows.GaloisPair.table_R10

/-! ### `GaloisPair.table.R10`

Blind text: "| 10 | Counit: F(G(N)).dim = 3 |" -/

-- AMBIGUITY: "F(G(N))": N over all models (S1) or over node models only (S2, the models built
-- by `nodeModel`; the letter N and "Counit" suggest node models). Both are required. S2 is
-- implied by S1.
-- AMBIGUITY: "Counit:" read as a label naming the composite F ∘ G, not as a claim that an
-- adjunction counit F(G(N)) ≤ N exists. The asserted content is the dimension equation.

/-- Intended statement: the round trip F(G(N)) is 3-dimensional, for every model N and in
particular for every node model. -/
@[sa_reference "GaloisPair.table.R10"]
def T : Prop :=
  (∀ N : EpiModel, (coarseGrain (poissonLift N)).dim = 3) ∧
    ∀ (p : SIRParams) (r : ℚ), (coarseGrain (poissonLift (nodeModel p r))).dim = 3

/-- S1: F(G(N)).dim = 3 for every model N. -/
@[sa_shadow "GaloisPair.table.R10" 1]
def S1 : Prop := ∀ N : EpiModel, (coarseGrain (poissonLift N)).dim = 3

/-- S2: F(G(N)).dim = 3 for every node model N = `nodeModel p r`. -/
@[sa_shadow "GaloisPair.table.R10" 2]
def S2 : Prop := ∀ (p : SIRParams) (r : ℚ), (coarseGrain (poissonLift (nodeModel p r))).dim = 3

@[sa_ref_forward "GaloisPair.table.R10" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "GaloisPair.table.R10" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "GaloisPair.table.R10"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.GaloisPair.table_R10

namespace Alignment.Shadows.GaloisPair.table_R11

/-! ### `GaloisPair.table.R11`

Blind text: "| 11 | G(F(E)).dim = 4 for all E |" -/

-- AMBIGUITY: "for all E": E over all models (S1) or over edge models only (S2, the models built
-- by `edgeModel`; the letter E suggests edge models). Both are required. S2 is implied by S1.

/-- Intended statement: G(F(E)) is 4-dimensional for every model E and in particular for every
edge model. -/
@[sa_reference "GaloisPair.table.R11"]
def T : Prop :=
  (∀ E : EpiModel, (poissonLift (coarseGrain E)).dim = 4) ∧
    ∀ (p : SIRParams) (ψ : PGFData), (poissonLift (coarseGrain (edgeModel p ψ))).dim = 4

/-- S1: G(F(E)).dim = 4 for every model E. -/
@[sa_shadow "GaloisPair.table.R11" 1]
def S1 : Prop := ∀ E : EpiModel, (poissonLift (coarseGrain E)).dim = 4

/-- S2: G(F(E)).dim = 4 for every edge model E = `edgeModel p ψ`. -/
@[sa_shadow "GaloisPair.table.R11" 2]
def S2 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData), (poissonLift (coarseGrain (edgeModel p ψ))).dim = 4

@[sa_ref_forward "GaloisPair.table.R11" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "GaloisPair.table.R11" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "GaloisPair.table.R11"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.GaloisPair.table_R11

namespace Alignment.Shadows.GaloisPair.table_R12

/-! ### `GaloisPair.table.R12`

Blind text: "| 12 | Idempotency: F ∘ G ∘ F = F |" -/

/-- Intended statement: F ∘ G ∘ F = F as functions. -/
@[sa_reference "GaloisPair.table.R12"]
def T : Prop := coarseGrain ∘ poissonLift ∘ coarseGrain = coarseGrain

/-- S1: F ∘ G ∘ F = F. -/
@[sa_shadow "GaloisPair.table.R12" 1]
def S1 : Prop := coarseGrain ∘ poissonLift ∘ coarseGrain = coarseGrain

@[sa_ref_forward "GaloisPair.table.R12" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "GaloisPair.table.R12"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.GaloisPair.table_R12

namespace Alignment.Shadows.GaloisPair.table_R13

/-! ### `GaloisPair.table.R13`

Blind text: "| 13 | Idempotency: G ∘ F ∘ G = G |" -/

/-- Intended statement: G ∘ F ∘ G = G as functions. -/
@[sa_reference "GaloisPair.table.R13"]
def T : Prop := poissonLift ∘ coarseGrain ∘ poissonLift = poissonLift

/-- S1: G ∘ F ∘ G = G. -/
@[sa_shadow "GaloisPair.table.R13" 1]
def S1 : Prop := poissonLift ∘ coarseGrain ∘ poissonLift = poissonLift

@[sa_ref_forward "GaloisPair.table.R13" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "GaloisPair.table.R13"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.GaloisPair.table_R13

namespace Alignment.Shadows.GaloisPair.table_R15

/-! ### `GaloisPair.table.R15`

Blind text: "| 15 | Round-trip preserves R₀ |" -/

-- AMBIGUITY: "Round-trip": there are two round trips, F ∘ G and G ∘ F. Read as F ∘ G, because the
-- row abbreviates Result 15 ("The round-trip F ∘ G preserves R₀ exactly") and matches the header
-- prose ("F ∘ G preserves R₀ exactly"). The row has no "exactly", but "preserves" is still read
-- as equality.

/-- Intended statement: the round trip F ∘ G leaves R₀ unchanged for every model. -/
@[sa_reference "GaloisPair.table.R15"]
def T : Prop := ∀ M : EpiModel, ((coarseGrain ∘ poissonLift) M).R0 = M.R0

/-- S1: F ∘ G preserves R₀ for every model. -/
@[sa_shadow "GaloisPair.table.R15" 1]
def S1 : Prop := ∀ M : EpiModel, ((coarseGrain ∘ poissonLift) M).R0 = M.R0

@[sa_ref_forward "GaloisPair.table.R15" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "GaloisPair.table.R15"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.GaloisPair.table_R15

/-! ## Numbered results (theorem docstrings) -/

namespace Alignment.Shadows.GaloisPair.R9

/-! ### `GaloisPair.R9`

Blind text: "**Result 9.** G is (trivially) monotone." -/

-- AMBIGUITY: "(trivially)" read as a remark about how hard the proof is, not as part of the
-- statement. The order is the refinement `Preorder` on `EpiModel` from DataTypes.

/-- Intended statement: G is monotone for the refinement preorder on `EpiModel`. -/
@[sa_reference "GaloisPair.R9"]
def T : Prop := Monotone poissonLift

/-- S1: `M ≤ M'` implies `G M ≤ G M'`. -/
@[sa_shadow "GaloisPair.R9" 1]
def S1 : Prop := ∀ M M' : EpiModel, M ≤ M' → poissonLift M ≤ poissonLift M'

@[sa_ref_forward "GaloisPair.R9" 1]
theorem ref_fwd1 : T → S1 := fun t _ _ h => t h

@[sa_complete "GaloisPair.R9"]
theorem complete (s1 : S1) : T := fun M M' h => s1 M M' h

end Alignment.Shadows.GaloisPair.R9

namespace Alignment.Shadows.GaloisPair.R10

/-! ### `GaloisPair.R10`

Blind text: "**Result 10.** Counit: F(G(N)).dim = 3." -/

-- AMBIGUITY: "F(G(N))": N over all models (S1) or over node models only (S2, the models built
-- by `nodeModel`). Both are required. S2 is implied by S1.
-- AMBIGUITY: "Counit:" read as a label naming the composite F ∘ G, not as a claim that an
-- adjunction counit F(G(N)) ≤ N exists. The asserted content is the dimension equation.

/-- Intended statement: F(G(N)) is 3-dimensional for every model N and in particular for every
node model. -/
@[sa_reference "GaloisPair.R10"]
def T : Prop :=
  (∀ N : EpiModel, (coarseGrain (poissonLift N)).dim = 3) ∧
    ∀ (p : SIRParams) (r : ℚ), (coarseGrain (poissonLift (nodeModel p r))).dim = 3

/-- S1: F(G(N)).dim = 3 for every model N. -/
@[sa_shadow "GaloisPair.R10" 1]
def S1 : Prop := ∀ N : EpiModel, (coarseGrain (poissonLift N)).dim = 3

/-- S2: F(G(N)).dim = 3 for every node model N = `nodeModel p r`. -/
@[sa_shadow "GaloisPair.R10" 2]
def S2 : Prop := ∀ (p : SIRParams) (r : ℚ), (coarseGrain (poissonLift (nodeModel p r))).dim = 3

@[sa_ref_forward "GaloisPair.R10" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "GaloisPair.R10" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "GaloisPair.R10"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.GaloisPair.R10

namespace Alignment.Shadows.GaloisPair.R11

/-! ### `GaloisPair.R11`

Blind text: "**Result 11.** G(F(E)).dim = 4 for all E." -/

-- AMBIGUITY: "for all E": E over all models (S1) or over edge models only (S2, the models built
-- by `edgeModel`). Both are required. S2 is implied by S1.

/-- Intended statement: G(F(E)) is 4-dimensional for every model E and in particular for every
edge model. -/
@[sa_reference "GaloisPair.R11"]
def T : Prop :=
  (∀ E : EpiModel, (poissonLift (coarseGrain E)).dim = 4) ∧
    ∀ (p : SIRParams) (ψ : PGFData), (poissonLift (coarseGrain (edgeModel p ψ))).dim = 4

/-- S1: G(F(E)).dim = 4 for every model E. -/
@[sa_shadow "GaloisPair.R11" 1]
def S1 : Prop := ∀ E : EpiModel, (poissonLift (coarseGrain E)).dim = 4

/-- S2: G(F(E)).dim = 4 for every edge model E = `edgeModel p ψ`. -/
@[sa_shadow "GaloisPair.R11" 2]
def S2 : Prop :=
  ∀ (p : SIRParams) (ψ : PGFData), (poissonLift (coarseGrain (edgeModel p ψ))).dim = 4

@[sa_ref_forward "GaloisPair.R11" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "GaloisPair.R11" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "GaloisPair.R11"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.GaloisPair.R11

namespace Alignment.Shadows.GaloisPair.R12

/-! ### `GaloisPair.R12`

Blind text: "**Result 12.** F ∘ G ∘ F = F (left idempotency)." -/

/-- Intended statement: F ∘ G ∘ F = F as functions. -/
@[sa_reference "GaloisPair.R12"]
def T : Prop := coarseGrain ∘ poissonLift ∘ coarseGrain = coarseGrain

/-- S1: F ∘ G ∘ F = F. -/
@[sa_shadow "GaloisPair.R12" 1]
def S1 : Prop := coarseGrain ∘ poissonLift ∘ coarseGrain = coarseGrain

@[sa_ref_forward "GaloisPair.R12" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "GaloisPair.R12"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.GaloisPair.R12

namespace Alignment.Shadows.GaloisPair.R13

/-! ### `GaloisPair.R13`

Blind text: "**Result 13.** G ∘ F ∘ G = G (right idempotency)." -/

/-- Intended statement: G ∘ F ∘ G = G as functions. -/
@[sa_reference "GaloisPair.R13"]
def T : Prop := poissonLift ∘ coarseGrain ∘ poissonLift = poissonLift

/-- S1: G ∘ F ∘ G = G. -/
@[sa_shadow "GaloisPair.R13" 1]
def S1 : Prop := poissonLift ∘ coarseGrain ∘ poissonLift = poissonLift

@[sa_ref_forward "GaloisPair.R13" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "GaloisPair.R13"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.GaloisPair.R13

namespace Alignment.Shadows.GaloisPair.coarseGrainR0

/-! ### `GaloisPair.coarseGrainR0`

Blind text: "F preserves R₀." -/

/-- Intended statement: for every model M, F(M) has the same R₀ as M. -/
@[sa_reference "GaloisPair.coarseGrainR0"]
def T : Prop := ∀ M : EpiModel, (coarseGrain M).R0 = M.R0

/-- S1: F preserves R₀ for every model. -/
@[sa_shadow "GaloisPair.coarseGrainR0" 1]
def S1 : Prop := ∀ M : EpiModel, (coarseGrain M).R0 = M.R0

@[sa_ref_forward "GaloisPair.coarseGrainR0" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "GaloisPair.coarseGrainR0"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.GaloisPair.coarseGrainR0

namespace Alignment.Shadows.GaloisPair.poissonLiftR0

/-! ### `GaloisPair.poissonLiftR0`

Blind text: "G preserves R₀." -/

-- AMBIGUITY: "G preserves R₀": over all models, or only the node models that G is described as
-- lifting? Read over all of `EpiModel` (G is total there). The node-only reading is weaker and
-- implied, so it is not a separate shadow.

/-- Intended statement: for every model M, G(M) has the same R₀ as M. -/
@[sa_reference "GaloisPair.poissonLiftR0"]
def T : Prop := ∀ M : EpiModel, (poissonLift M).R0 = M.R0

/-- S1: G preserves R₀ for every model. -/
@[sa_shadow "GaloisPair.poissonLiftR0" 1]
def S1 : Prop := ∀ M : EpiModel, (poissonLift M).R0 = M.R0

@[sa_ref_forward "GaloisPair.poissonLiftR0" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "GaloisPair.poissonLiftR0"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.GaloisPair.poissonLiftR0

namespace Alignment.Shadows.GaloisPair.R15

/-! ### `GaloisPair.R15`

Blind text: "**Result 15.** The round-trip F ∘ G preserves R₀ exactly." -/

/-- Intended statement: for every model M, (F ∘ G)(M) has exactly the R₀ of M. -/
@[sa_reference "GaloisPair.R15"]
def T : Prop := ∀ M : EpiModel, ((coarseGrain ∘ poissonLift) M).R0 = M.R0

/-- S1: F ∘ G preserves R₀ exactly, for every model. -/
@[sa_shadow "GaloisPair.R15" 1]
def S1 : Prop := ∀ M : EpiModel, ((coarseGrain ∘ poissonLift) M).R0 = M.R0

@[sa_ref_forward "GaloisPair.R15" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "GaloisPair.R15"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.GaloisPair.R15

noncomputable section

/-! ## `GaloisPair.R14a` (re-authored blind)

Text: "**Result 14.** G ∘ F ≠ id: G ∘ F sets the dimension of every record to 4."

F = `coarseGrain`, G = `poissonLift`. -/
namespace Alignment.Shadows.GaloisPair.R14a

@[sa_reference "GaloisPair.R14a"]
def T : Prop :=
  poissonLift ∘ coarseGrain ≠ id ∧ ∀ e : EpiModel, (poissonLift (coarseGrain e)).dim = 4

/-- S1: `G ∘ F ≠ id`. -/
@[sa_shadow "GaloisPair.R14a" 1]
def S1 : Prop := poissonLift ∘ coarseGrain ≠ id
/-- S2: `G ∘ F` sets every dimension to 4. -/
@[sa_shadow "GaloisPair.R14a" 2]
def S2 : Prop := ∀ e : EpiModel, (poissonLift (coarseGrain e)).dim = 4

@[sa_ref_forward "GaloisPair.R14a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "GaloisPair.R14a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "GaloisPair.R14a"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.GaloisPair.R14a

/-! ## `GaloisPair.R14b` (blind)

Text: "Witness: a record of dimension 10 maps to dimension 3 via F and back to dimension 4 via G."

-- AMBIGUITY: "a record" read existentially (a witness), as the word "Witness" says. -/
namespace Alignment.Shadows.GaloisPair.R14b

@[sa_reference "GaloisPair.R14b"]
def T : Prop :=
  ∃ e : EpiModel, e.dim = 10 ∧ (coarseGrain e).dim = 3 ∧ (poissonLift (coarseGrain e)).dim = 4

/-- S1: a dimension-10 record goes to dimension 3 under F and to dimension 4 under G ∘ F. -/
@[sa_shadow "GaloisPair.R14b" 1]
def S1 : Prop :=
  ∃ e : EpiModel, e.dim = 10 ∧ (coarseGrain e).dim = 3 ∧ (poissonLift (coarseGrain e)).dim = 4

@[sa_ref_forward "GaloisPair.R14b" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "GaloisPair.R14b"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.GaloisPair.R14b

/-! ## `GaloisPair.header.GFLossy` (re-authored blind)

Text: "G ∘ F ≠ id (G ∘ F sets every dimension to 4)" -/
namespace Alignment.Shadows.GaloisPair.header_GFLossy

@[sa_reference "GaloisPair.header.GFLossy"]
def T : Prop :=
  poissonLift ∘ coarseGrain ≠ id ∧ ∀ e : EpiModel, (poissonLift (coarseGrain e)).dim = 4

/-- S1: `G ∘ F ≠ id`. -/
@[sa_shadow "GaloisPair.header.GFLossy" 1]
def S1 : Prop := poissonLift ∘ coarseGrain ≠ id
/-- S2: `G ∘ F` sets every dimension to 4. -/
@[sa_shadow "GaloisPair.header.GFLossy" 2]
def S2 : Prop := ∀ e : EpiModel, (poissonLift (coarseGrain e)).dim = 4

@[sa_ref_forward "GaloisPair.header.GFLossy" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "GaloisPair.header.GFLossy" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "GaloisPair.header.GFLossy"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.GaloisPair.header_GFLossy

/-! ## `GaloisPair.header.galoisConnection` (blind)

Text: "F and G are not a Galois connection for the dimension preorder: for E = ⟨10, r⟩ and
N = ⟨3, r⟩, F(E) ≤ N holds but E ≤ G(N) fails (`not_galoisConnection_coarseGrain_poissonLift`)."

The preorder is the `EpiModel` refinement order; r ranges over all R₀ values. -/
namespace Alignment.Shadows.GaloisPair.header_galoisConnection

@[sa_reference "GaloisPair.header.galoisConnection"]
def T : Prop :=
  ¬ GaloisConnection coarseGrain poissonLift ∧
  (∀ r : ℚ, coarseGrain ⟨10, r⟩ ≤ ⟨3, r⟩) ∧ (∀ r : ℚ, ¬ (⟨10, r⟩ : EpiModel) ≤ poissonLift ⟨3, r⟩)

/-- S1: F and G are not a Galois connection. -/
@[sa_shadow "GaloisPair.header.galoisConnection" 1]
def S1 : Prop := ¬ GaloisConnection coarseGrain poissonLift
/-- S2: `F⟨10, r⟩ ≤ ⟨3, r⟩`. -/
@[sa_shadow "GaloisPair.header.galoisConnection" 2]
def S2 : Prop := ∀ r : ℚ, coarseGrain ⟨10, r⟩ ≤ ⟨3, r⟩
/-- S3: `⟨10, r⟩ ≤ G⟨3, r⟩` fails. -/
@[sa_shadow "GaloisPair.header.galoisConnection" 3]
def S3 : Prop := ∀ r : ℚ, ¬ (⟨10, r⟩ : EpiModel) ≤ poissonLift ⟨3, r⟩

@[sa_ref_forward "GaloisPair.header.galoisConnection" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "GaloisPair.header.galoisConnection" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "GaloisPair.header.galoisConnection" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2
@[sa_complete "GaloisPair.header.galoisConnection"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.GaloisPair.header_galoisConnection

/-! ## `GaloisPair.table.R14` (re-authored blind)

Text: "| 14 | G ∘ F ≠ id (G ∘ F forgets the dimension) |"

"Forgets the dimension": the dimension of `G(F(e))` does not depend on `e`. -/
namespace Alignment.Shadows.GaloisPair.table_R14

@[sa_reference "GaloisPair.table.R14"]
def T : Prop :=
  poissonLift ∘ coarseGrain ≠ id ∧
  ∀ e e' : EpiModel, (poissonLift (coarseGrain e)).dim = (poissonLift (coarseGrain e')).dim

/-- S1: `G ∘ F ≠ id`. -/
@[sa_shadow "GaloisPair.table.R14" 1]
def S1 : Prop := poissonLift ∘ coarseGrain ≠ id
/-- S2: `G ∘ F` forgets the dimension. -/
@[sa_shadow "GaloisPair.table.R14" 2]
def S2 : Prop :=
  ∀ e e' : EpiModel, (poissonLift (coarseGrain e)).dim = (poissonLift (coarseGrain e')).dim

@[sa_ref_forward "GaloisPair.table.R14" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "GaloisPair.table.R14" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "GaloisPair.table.R14"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.GaloisPair.table_R14

/-! ## `GaloisPair.fgEqSelfOfDimThree` (blind)

Text: "F ∘ G is the identity on records of dimension 3." -/
namespace Alignment.Shadows.GaloisPair.fgEqSelfOfDimThree

@[sa_reference "GaloisPair.fgEqSelfOfDimThree"]
def T : Prop := ∀ e : EpiModel, e.dim = 3 → coarseGrain (poissonLift e) = e

/-- S1: `F(G(e)) = e` whenever `e.dim = 3`. -/
@[sa_shadow "GaloisPair.fgEqSelfOfDimThree" 1]
def S1 : Prop := ∀ e : EpiModel, e.dim = 3 → coarseGrain (poissonLift e) = e

@[sa_ref_forward "GaloisPair.fgEqSelfOfDimThree" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "GaloisPair.fgEqSelfOfDimThree"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.GaloisPair.fgEqSelfOfDimThree

/-! ## `GaloisPair.notGaloisConnectionCoarseGrainPoissonLift` (blind)

Text: "F and G are not a Galois connection for the dimension preorder on `EpiModel`: for
E = ⟨10, 1⟩ and N = ⟨3, 1⟩, F(E) ≤ N holds but E ≤ G(N) fails." -/
namespace Alignment.Shadows.GaloisPair.notGaloisConnectionCoarseGrainPoissonLift

@[sa_reference "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift"]
def T : Prop :=
  ¬ GaloisConnection coarseGrain poissonLift ∧ coarseGrain ⟨10, 1⟩ ≤ ⟨3, 1⟩ ∧
    ¬ (⟨10, 1⟩ : EpiModel) ≤ poissonLift ⟨3, 1⟩

/-- S1: F and G are not a Galois connection. -/
@[sa_shadow "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift" 1]
def S1 : Prop := ¬ GaloisConnection coarseGrain poissonLift
/-- S2: `F⟨10, 1⟩ ≤ ⟨3, 1⟩`. -/
@[sa_shadow "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift" 2]
def S2 : Prop := coarseGrain ⟨10, 1⟩ ≤ ⟨3, 1⟩
/-- S3: `⟨10, 1⟩ ≤ G⟨3, 1⟩` fails. -/
@[sa_shadow "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift" 3]
def S3 : Prop := ¬ (⟨10, 1⟩ : EpiModel) ≤ poissonLift ⟨3, 1⟩

@[sa_ref_forward "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift" 1] theorem ref_fwd1 :
    T → S1 := fun t => t.1
@[sa_ref_forward "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift" 2] theorem ref_fwd2 :
    T → S2 := fun t => t.2.1
@[sa_ref_forward "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift" 3] theorem ref_fwd3 :
    T → S3 := fun t => t.2.2
@[sa_complete "GaloisPair.notGaloisConnectionCoarseGrainPoissonLift"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.GaloisPair.notGaloisConnectionCoarseGrainPoissonLift

/-! ## `GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain` (blind)

Text: "G and F are not a Galois connection in the other order either: for E = N = ⟨3, 1⟩,
E ≤ F(N) holds but G(E) ≤ N fails." -/
namespace Alignment.Shadows.GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain

@[sa_reference "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain"]
def T : Prop :=
  ¬ GaloisConnection poissonLift coarseGrain ∧ (⟨3, 1⟩ : EpiModel) ≤ coarseGrain ⟨3, 1⟩ ∧
    ¬ poissonLift ⟨3, 1⟩ ≤ ⟨3, 1⟩

/-- S1: G and F are not a Galois connection. -/
@[sa_shadow "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain" 1]
def S1 : Prop := ¬ GaloisConnection poissonLift coarseGrain
/-- S2: `⟨3, 1⟩ ≤ F⟨3, 1⟩`. -/
@[sa_shadow "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain" 2]
def S2 : Prop := (⟨3, 1⟩ : EpiModel) ≤ coarseGrain ⟨3, 1⟩
/-- S3: `G⟨3, 1⟩ ≤ ⟨3, 1⟩` fails. -/
@[sa_shadow "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain" 3]
def S3 : Prop := ¬ poissonLift ⟨3, 1⟩ ≤ ⟨3, 1⟩

@[sa_ref_forward "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain" 1] theorem ref_fwd1 :
    T → S1 := fun t => t.1
@[sa_ref_forward "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain" 2] theorem ref_fwd2 :
    T → S2 := fun t => t.2.1
@[sa_ref_forward "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain" 3] theorem ref_fwd3 :
    T → S3 := fun t => t.2.2
@[sa_complete "GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.GaloisPair.notGaloisConnectionPoissonLiftCoarseGrain

end
