import Alignment.Registry
import EBCMCategory.Obstructions
import EBCMCategory.MarginalisationDynamicalGap   -- F3Kℝ, F4Kℝ, u₁, MℝLinCLM, IsFlow, Equivariant (DataTypes/Docs.md, MarginalisationDynamicalGap.md)

/-!
# Blind shadow sets: group `Obstructions`

Written blind from `Alignment/claims_blind.yaml` (id, source, text), `Alignment/DataTypes/Obstructions.md`,
`Alignment/README.md` and `Alignment/Example/ExampleShadows.lean` only.

Vocabulary (opaque operations under test, from `DataTypes/Obstructions.md`):

* `standardEbcmValid n t i : Prop` -- "the standard EBCM (4 ODE variables) is valid".
* `ebcmExists n t i : Prop` -- "an EBCM variant exists (as ODE or PDE)".
* `systemRequired t i : SystemType` -- "ODE / PDE / impossible".
* `extensionDim n t : ℕ` -- "number of (ODE) variables"; returns `0` for PDE systems
  (infinite-dimensional). Hence "an ODE system (finite dimension)" at `(n, t)` is `0 < extensionDim n t`
  and "infinite-dimensional" is `extensionDim n t = 0`.
* `MarginalisationObstruction.{M_witness, F4_Kirkwood, F3_Kirkwood}` on `U4 = Idx4 → ℚ`,
  `U3 = Idx3 → ℚ`.

"The standard EBCM" is the configuration-model / Markovian / uniform case, and its number of
variables is `extensionDim .configurationModel .markovian`.

Conventions used throughout (each flagged where it matters):

* "X breaks the standard EBCM" is read in two ways, both required: with the other two
  assumptions at their standard values (specific), and for every value of the other two
  parameters (universal).
* "A variant works / handles X" is read with the other assumptions at their standard values,
  unless the text fixes some parameters and leaves others free, in which case the free ones are
  quantified universally.
* "(ODE)" / "still an ODE system" is read both as finite ODE dimension at that network
  (`0 < extensionDim n t`) and as the system type (`systemRequired t .uniform = .ode`).
* "All EBCM variants" includes the standard EBCM, so `standardEbcmValid` is also required to fail.

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace). Ids of that pass not formalised (remarks on proof status, on which notions the library
defines, or cited results needing models the vocabulary lacks): `R19c`,
`header.clusteringAddsVariables`, `header.witnessCollapse`, `kirkwoodObstructionWitnessValue-b`.
-/

/-! ## `Obstructions.table.R17`

Text: "| 17 | Standard ODE EBCM valid under all three assumptions |" -/
namespace Alignment.Shadows.Obstructions.table_R17

-- AMBIGUITY: "Standard ODE EBCM" is taken as the name of the standard EBCM (not a separate
-- claim about the system type). "under all three assumptions" = configuration model +
-- Markovian + uniform (sufficiency only; the row does not claim necessity).

@[sa_reference "Obstructions.table.R17"]
def T : Prop := standardEbcmValid .configurationModel .markovian .uniform

/-- S1: the standard EBCM is valid for configuration model + Markovian + uniform initials. -/
@[sa_shadow "Obstructions.table.R17" 1]
def S1 : Prop := standardEbcmValid .configurationModel .markovian .uniform

@[sa_ref_forward "Obstructions.table.R17" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Obstructions.table.R17"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Obstructions.table_R17

/-! ## `Obstructions.table.R19`

Text: "| 19 | Non-Markovian: ODE fails, PDE EBCM works (exact) |" -/
namespace Alignment.Shadows.Obstructions.table_R19

-- AMBIGUITY: "ODE fails" read as: no ODE system suffices (S1), and the standard ODE EBCM fails,
-- both on the configuration model with uniform initials (S2) and for every network / initial
-- type (S3).
-- AMBIGUITY: "PDE EBCM works" read with the other assumptions standard (configuration model,
-- uniform initials).
-- VOCAB-GAP: "(exact)" (as opposed to approximate) cannot be expressed separately; it is covered
-- only by `systemRequired … = .pde` and `ebcmExists`.

@[sa_reference "Obstructions.table.R19"]
def T : Prop :=
  systemRequired .generalNonMarkov .uniform ≠ .ode ∧
  ¬ standardEbcmValid .configurationModel .generalNonMarkov .uniform ∧
  (∀ (n : NetworkType) (i : InitCondType), ¬ standardEbcmValid n .generalNonMarkov i) ∧
  systemRequired .generalNonMarkov .uniform = .pde ∧
  ebcmExists .configurationModel .generalNonMarkov .uniform

/-- S1: for non-Markovian dynamics (uniform initials) the required system is not an ODE. -/
@[sa_shadow "Obstructions.table.R19" 1]
def S1 : Prop := systemRequired .generalNonMarkov .uniform ≠ .ode

/-- S2: the standard ODE EBCM fails for non-Markovian dynamics (configuration model, uniform). -/
@[sa_shadow "Obstructions.table.R19" 2]
def S2 : Prop := ¬ standardEbcmValid .configurationModel .generalNonMarkov .uniform

/-- S3: the standard ODE EBCM fails for non-Markovian dynamics on any network, any initials. -/
@[sa_shadow "Obstructions.table.R19" 3]
def S3 : Prop := ∀ (n : NetworkType) (i : InitCondType), ¬ standardEbcmValid n .generalNonMarkov i

/-- S4: the required system for non-Markovian dynamics (uniform initials) is a PDE. -/
@[sa_shadow "Obstructions.table.R19" 4]
def S4 : Prop := systemRequired .generalNonMarkov .uniform = .pde

/-- S5: the PDE EBCM works: a variant exists (configuration model, non-Markovian, uniform). -/
@[sa_shadow "Obstructions.table.R19" 5]
def S5 : Prop := ebcmExists .configurationModel .generalNonMarkov .uniform

@[sa_ref_forward "Obstructions.table.R19" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.table.R19" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.table.R19" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Obstructions.table.R19" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "Obstructions.table.R19" 5]
theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2
@[sa_complete "Obstructions.table.R19"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.Obstructions.table_R19

/-! ## `Obstructions.table.R20`

Text: "| 20 | Localised initials: genuine obstruction (all variants) |" -/
namespace Alignment.Shadows.Obstructions.table_R20

-- AMBIGUITY: "genuine obstruction (all variants)" read as: no EBCM variant exists for localised
-- initials on any network with any transition type (S1), the system type is "impossible" (S2),
-- and "all variants" includes the standard EBCM (S3).

@[sa_reference "Obstructions.table.R20"]
def T : Prop :=
  (∀ (n : NetworkType) (t : TransitionType), ¬ ebcmExists n t .localised) ∧
  (∀ t : TransitionType, systemRequired t .localised = .impossible) ∧
  (∀ (n : NetworkType) (t : TransitionType), ¬ standardEbcmValid n t .localised)

/-- S1: no EBCM variant exists with localised initials (any network, any transition). -/
@[sa_shadow "Obstructions.table.R20" 1]
def S1 : Prop := ∀ (n : NetworkType) (t : TransitionType), ¬ ebcmExists n t .localised

/-- S2: with localised initials the required system type is `impossible`. -/
@[sa_shadow "Obstructions.table.R20" 2]
def S2 : Prop := ∀ t : TransitionType, systemRequired t .localised = .impossible

/-- S3: the standard EBCM also fails with localised initials. -/
@[sa_shadow "Obstructions.table.R20" 3]
def S3 : Prop := ∀ (n : NetworkType) (t : TransitionType), ¬ standardEbcmValid n t .localised

@[sa_ref_forward "Obstructions.table.R20" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.table.R20" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.table.R20" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Obstructions.table.R20"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Obstructions.table_R20

/-! ## `Obstructions.table.R21`

Text: "| 21 | Degree correlations: multi-type EBCM works (ODE) |" -/
namespace Alignment.Shadows.Obstructions.table_R21

-- AMBIGUITY: "works" read with Markovian dynamics and uniform initials. "(ODE)" read both as
-- finite ODE dimension on the degree-correlated network (S2) and as the system type (S3).

@[sa_reference "Obstructions.table.R21"]
def T : Prop :=
  ebcmExists .degreeCorrelated .markovian .uniform ∧
  0 < extensionDim .degreeCorrelated .markovian ∧
  systemRequired .markovian .uniform = .ode

/-- S1: the multi-type EBCM works: a variant exists for degree-correlated networks. -/
@[sa_shadow "Obstructions.table.R21" 1]
def S1 : Prop := ebcmExists .degreeCorrelated .markovian .uniform

/-- S2: (ODE) the degree-correlated variant has a finite ODE dimension. -/
@[sa_shadow "Obstructions.table.R21" 2]
def S2 : Prop := 0 < extensionDim .degreeCorrelated .markovian

/-- S3: (ODE) the system type for Markovian + uniform is ODE. -/
@[sa_shadow "Obstructions.table.R21" 3]
def S3 : Prop := systemRequired .markovian .uniform = .ode

@[sa_ref_forward "Obstructions.table.R21" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.table.R21" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.table.R21" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Obstructions.table.R21"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Obstructions.table_R21

/-! ## `Obstructions.R17`

Text: "**Result 17.** The standard EBCM is valid under all correct assumptions." -/
namespace Alignment.Shadows.Obstructions.R17

-- "all correct assumptions" = configuration model + Markovian + uniform (sufficiency only).

@[sa_reference "Obstructions.R17"]
def T : Prop := standardEbcmValid .configurationModel .markovian .uniform

/-- S1: the standard EBCM is valid for configuration model + Markovian + uniform initials. -/
@[sa_shadow "Obstructions.R17" 1]
def S1 : Prop := standardEbcmValid .configurationModel .markovian .uniform

@[sa_ref_forward "Obstructions.R17" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Obstructions.R17"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Obstructions.R17

/-! ## `Obstructions.R18a`

Text: "**Result 18.** Clustering breaks the *standard* EBCM," -/
namespace Alignment.Shadows.Obstructions.R18a

-- AMBIGUITY: "Clustering breaks the standard EBCM" read both as: with the other two assumptions
-- standard (S1), and whatever the transition / initial types (S2).

@[sa_reference "Obstructions.R18a"]
def T : Prop :=
  ¬ standardEbcmValid .clusteredTriangles .markovian .uniform ∧
  ∀ (t : TransitionType) (i : InitCondType), ¬ standardEbcmValid .clusteredTriangles t i

/-- S1: the standard EBCM is invalid on a clustered network (Markovian, uniform). -/
@[sa_shadow "Obstructions.R18a" 1]
def S1 : Prop := ¬ standardEbcmValid .clusteredTriangles .markovian .uniform

/-- S2: the standard EBCM is invalid on a clustered network for all transition / initial types. -/
@[sa_shadow "Obstructions.R18a" 2]
def S2 : Prop :=
  ∀ (t : TransitionType) (i : InitCondType), ¬ standardEbcmValid .clusteredTriangles t i

@[sa_ref_forward "Obstructions.R18a" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R18a" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Obstructions.R18a"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Obstructions.R18a

/-! ## `Obstructions.R18b`

Text: "but NOT the EBCM framework. [...] But an EBCM variant exists for clustered networks." -/
namespace Alignment.Shadows.Obstructions.R18b

-- AMBIGUITY: "an EBCM variant exists for clustered networks" read with the other assumptions
-- standard (Markovian, uniform); with localised initials no variant exists (Result 20).

@[sa_reference "Obstructions.R18b"]
def T : Prop := ebcmExists .clusteredTriangles .markovian .uniform

/-- S1: an EBCM variant exists for clustered networks (Markovian, uniform). -/
@[sa_shadow "Obstructions.R18b" 1]
def S1 : Prop := ebcmExists .clusteredTriangles .markovian .uniform

@[sa_ref_forward "Obstructions.R18b" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Obstructions.R18b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Obstructions.R18b

/-! ## `Obstructions.R18c`

Text: "The triangle EBCM handles it with more variables." -/
namespace Alignment.Shadows.Obstructions.R18c

-- "it" = clustering. "more variables" = more than the standard EBCM
-- (`extensionDim .configurationModel .markovian`).

@[sa_reference "Obstructions.R18c"]
def T : Prop :=
  ebcmExists .clusteredTriangles .markovian .uniform ∧
  extensionDim .configurationModel .markovian < extensionDim .clusteredTriangles .markovian

/-- S1: the triangle EBCM handles clustering: a variant exists (Markovian, uniform). -/
@[sa_shadow "Obstructions.R18c" 1]
def S1 : Prop := ebcmExists .clusteredTriangles .markovian .uniform

/-- S2: it needs more ODE variables than the standard EBCM. -/
@[sa_shadow "Obstructions.R18c" 2]
def S2 : Prop :=
  extensionDim .configurationModel .markovian < extensionDim .clusteredTriangles .markovian

@[sa_ref_forward "Obstructions.R18c" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R18c" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Obstructions.R18c"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Obstructions.R18c

/-! ## `Obstructions.R21a`

Text: "**Result 21.** Degree correlations break the standard EBCM," -/
namespace Alignment.Shadows.Obstructions.R21a

-- AMBIGUITY: read both with the other two assumptions standard (S1) and whatever the transition
-- / initial types (S2).

@[sa_reference "Obstructions.R21a"]
def T : Prop :=
  ¬ standardEbcmValid .degreeCorrelated .markovian .uniform ∧
  ∀ (t : TransitionType) (i : InitCondType), ¬ standardEbcmValid .degreeCorrelated t i

/-- S1: the standard EBCM is invalid on a degree-correlated network (Markovian, uniform). -/
@[sa_shadow "Obstructions.R21a" 1]
def S1 : Prop := ¬ standardEbcmValid .degreeCorrelated .markovian .uniform

/-- S2: the standard EBCM is invalid on a degree-correlated network for all transition / initial
types. -/
@[sa_shadow "Obstructions.R21a" 2]
def S2 : Prop :=
  ∀ (t : TransitionType) (i : InitCondType), ¬ standardEbcmValid .degreeCorrelated t i

@[sa_ref_forward "Obstructions.R21a" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R21a" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Obstructions.R21a"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Obstructions.R21a

/-! ## `Obstructions.R21b`

Text: "**Degree correlations**: Multi-type EBCM of Miller & Volz (2013) with mixing matrix. Still an
ODE system. [...] but multi-type EBCM handles them." -/
namespace Alignment.Shadows.Obstructions.R21b

-- The citation "of Miller & Volz (2013) with mixing matrix" is not checkable.
-- VOCAB-GAP: the multi-type construction and its mixing matrix are not in DataTypes; only
-- existence (`ebcmExists`) and dimension / system type are expressible.
-- AMBIGUITY: "handles them" read with Markovian dynamics and uniform initials. "Still an ODE
-- system" read both as finite ODE dimension on the degree-correlated network (S2) and as the
-- system type (S3).

@[sa_reference "Obstructions.R21b"]
def T : Prop :=
  ebcmExists .degreeCorrelated .markovian .uniform ∧
  0 < extensionDim .degreeCorrelated .markovian ∧
  systemRequired .markovian .uniform = .ode

/-- S1: the multi-type EBCM handles degree correlations: a variant exists. -/
@[sa_shadow "Obstructions.R21b" 1]
def S1 : Prop := ebcmExists .degreeCorrelated .markovian .uniform

/-- S2: still an ODE system: finite, positive ODE dimension on the degree-correlated network. -/
@[sa_shadow "Obstructions.R21b" 2]
def S2 : Prop := 0 < extensionDim .degreeCorrelated .markovian

/-- S3: still an ODE system: the system type for Markovian + uniform is ODE. -/
@[sa_shadow "Obstructions.R21b" 3]
def S3 : Prop := systemRequired .markovian .uniform = .ode

@[sa_ref_forward "Obstructions.R21b" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R21b" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.R21b" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Obstructions.R21b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Obstructions.R21b

/-! ## `Obstructions.R19a`

Text: "The system becomes a **PDE** (von Foerster age-structured equation) rather than an ODE, with
infinite-dimensional state space. [...] **Result 19.** Non-Markovian dynamics change the system
type from ODE to PDE," -/
namespace Alignment.Shadows.Obstructions.R19a

-- "from ODE" = the Markovian baseline (uniform initials) is an ODE (S2).
-- "infinite-dimensional state space" is expressed through the DataTypes convention that
-- `extensionDim` returns 0 for PDE (infinite-dimensional) systems (S3), for every network.
-- VOCAB-GAP: the von Foerster equation itself is not expressible with DataTypes.

@[sa_reference "Obstructions.R19a"]
def T : Prop :=
  systemRequired .generalNonMarkov .uniform = .pde ∧
  systemRequired .markovian .uniform = .ode ∧
  ∀ n : NetworkType, extensionDim n .generalNonMarkov = 0

/-- S1: non-Markovian dynamics (uniform initials) require a PDE. -/
@[sa_shadow "Obstructions.R19a" 1]
def S1 : Prop := systemRequired .generalNonMarkov .uniform = .pde

/-- S2: the Markovian baseline (uniform initials) is an ODE. -/
@[sa_shadow "Obstructions.R19a" 2]
def S2 : Prop := systemRequired .markovian .uniform = .ode

/-- S3: the non-Markovian state space is infinite-dimensional on every network (sentinel 0). -/
@[sa_shadow "Obstructions.R19a" 3]
def S3 : Prop := ∀ n : NetworkType, extensionDim n .generalNonMarkov = 0

@[sa_ref_forward "Obstructions.R19a" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R19a" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.R19a" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Obstructions.R19a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Obstructions.R19a

/-! ## `Obstructions.R19b`

Text: "Changes the *type* of system, not an absolute obstruction: [...] but the EBCM framework
still works exactly. [...] Non-Markovian + uniform: an EBCM exists (as a PDE system)." -/
namespace Alignment.Shadows.Obstructions.R19b

-- AMBIGUITY: "Non-Markovian + uniform: an EBCM exists" leaves the network free. Read both on the
-- configuration model (S1, only assumption 2 relaxed) and for every network type (S2).
-- "Changes the type of system": the non-Markovian system type differs from the Markovian one (S4).
-- VOCAB-GAP: "works exactly" (no approximation) is not separately expressible.

@[sa_reference "Obstructions.R19b"]
def T : Prop :=
  ebcmExists .configurationModel .generalNonMarkov .uniform ∧
  (∀ n : NetworkType, ebcmExists n .generalNonMarkov .uniform) ∧
  systemRequired .generalNonMarkov .uniform = .pde ∧
  systemRequired .generalNonMarkov .uniform ≠ systemRequired .markovian .uniform

/-- S1: non-Markovian + uniform: an EBCM variant exists on the configuration model. -/
@[sa_shadow "Obstructions.R19b" 1]
def S1 : Prop := ebcmExists .configurationModel .generalNonMarkov .uniform

/-- S2: non-Markovian + uniform: an EBCM variant exists on every network type. -/
@[sa_shadow "Obstructions.R19b" 2]
def S2 : Prop := ∀ n : NetworkType, ebcmExists n .generalNonMarkov .uniform

/-- S3: the variant is a PDE system. -/
@[sa_shadow "Obstructions.R19b" 3]
def S3 : Prop := systemRequired .generalNonMarkov .uniform = .pde

/-- S4: non-Markovian dynamics change the system type relative to Markovian dynamics. -/
@[sa_shadow "Obstructions.R19b" 4]
def S4 : Prop := systemRequired .generalNonMarkov .uniform ≠ systemRequired .markovian .uniform

@[sa_ref_forward "Obstructions.R19b" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R19b" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.R19b" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Obstructions.R19b" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "Obstructions.R19b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.Obstructions.R19b

/-! ## `Obstructions.erlangIsOde`

Text: "The Erlang-staged approximation recovers an ODE system." -/
namespace Alignment.Shadows.Obstructions.erlangIsOde

-- AMBIGUITY: "an ODE system" read both as the system type with uniform initials (S1) and as a
-- finite ODE dimension on every network (S2).
-- VOCAB-GAP: `erlangStaged` carries no stage count n, so "for every n" cannot be expressed.

@[sa_reference "Obstructions.erlangIsOde"]
def T : Prop :=
  systemRequired .erlangStaged .uniform = .ode ∧
  ∀ n : NetworkType, 0 < extensionDim n .erlangStaged

/-- S1: Erlang-staged dynamics (uniform initials) require an ODE. -/
@[sa_shadow "Obstructions.erlangIsOde" 1]
def S1 : Prop := systemRequired .erlangStaged .uniform = .ode

/-- S2: the Erlang-staged variant has a finite, positive ODE dimension on every network. -/
@[sa_shadow "Obstructions.erlangIsOde" 2]
def S2 : Prop := ∀ n : NetworkType, 0 < extensionDim n .erlangStaged

@[sa_ref_forward "Obstructions.erlangIsOde" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.erlangIsOde" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Obstructions.erlangIsOde"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Obstructions.erlangIsOde

/-! ## `Obstructions.R20b`

Text: "They break ALL EBCM variants (ODE and PDE alike)" -/
namespace Alignment.Shadows.Obstructions.R20b

-- "They" = localised initial conditions. "ALL EBCM variants" = no variant exists (S1), including
-- the standard EBCM (S2). "ODE and PDE alike" = the system type is neither ODE (S3) nor PDE (S4),
-- for every transition type.

@[sa_reference "Obstructions.R20b"]
def T : Prop :=
  (∀ (n : NetworkType) (t : TransitionType), ¬ ebcmExists n t .localised) ∧
  (∀ (n : NetworkType) (t : TransitionType), ¬ standardEbcmValid n t .localised) ∧
  (∀ t : TransitionType, systemRequired t .localised ≠ .ode) ∧
  (∀ t : TransitionType, systemRequired t .localised ≠ .pde)

/-- S1: with localised initials no EBCM variant exists (any network, any transition). -/
@[sa_shadow "Obstructions.R20b" 1]
def S1 : Prop := ∀ (n : NetworkType) (t : TransitionType), ¬ ebcmExists n t .localised

/-- S2: with localised initials the standard EBCM is invalid. -/
@[sa_shadow "Obstructions.R20b" 2]
def S2 : Prop := ∀ (n : NetworkType) (t : TransitionType), ¬ standardEbcmValid n t .localised

/-- S3: with localised initials no ODE system works. -/
@[sa_shadow "Obstructions.R20b" 3]
def S3 : Prop := ∀ t : TransitionType, systemRequired t .localised ≠ .ode

/-- S4: with localised initials no PDE system works. -/
@[sa_shadow "Obstructions.R20b" 4]
def S4 : Prop := ∀ t : TransitionType, systemRequired t .localised ≠ .pde

@[sa_ref_forward "Obstructions.R20b" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R20b" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.R20b" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Obstructions.R20b" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "Obstructions.R20b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.Obstructions.R20b

/-! ## `Obstructions.standardMostCompact`

Text: "The standard EBCM is the most compact ODE variant." -/
namespace Alignment.Shadows.Obstructions.standardMostCompact

-- "ODE variant" = a (network, transition) combination with finite ODE dimension,
-- `0 < extensionDim n t` (0 encodes PDE / infinite-dimensional).
-- The standard EBCM is itself an ODE variant (S1).
-- AMBIGUITY: "the most compact" read as a minimum, i.e. no ODE variant has fewer variables (S2),
-- and, because of the definite article, as the unique minimum: every other ODE variant has
-- strictly more variables (S3).

@[sa_reference "Obstructions.standardMostCompact"]
def T : Prop :=
  0 < extensionDim .configurationModel .markovian ∧
  (∀ (n : NetworkType) (t : TransitionType), 0 < extensionDim n t →
      extensionDim .configurationModel .markovian ≤ extensionDim n t) ∧
  (∀ (n : NetworkType) (t : TransitionType), 0 < extensionDim n t →
      ¬ (n = .configurationModel ∧ t = .markovian) →
      extensionDim .configurationModel .markovian < extensionDim n t)

/-- S1: the standard EBCM is an ODE variant (finite, positive dimension). -/
@[sa_shadow "Obstructions.standardMostCompact" 1]
def S1 : Prop := 0 < extensionDim .configurationModel .markovian

/-- S2: no ODE variant needs fewer variables than the standard EBCM. -/
@[sa_shadow "Obstructions.standardMostCompact" 2]
def S2 : Prop :=
  ∀ (n : NetworkType) (t : TransitionType), 0 < extensionDim n t →
    extensionDim .configurationModel .markovian ≤ extensionDim n t

/-- S3: every other ODE variant needs strictly more variables than the standard EBCM. -/
@[sa_shadow "Obstructions.standardMostCompact" 3]
def S3 : Prop :=
  ∀ (n : NetworkType) (t : TransitionType), 0 < extensionDim n t →
    ¬ (n = .configurationModel ∧ t = .markovian) →
    extensionDim .configurationModel .markovian < extensionDim n t

@[sa_ref_forward "Obstructions.standardMostCompact" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.standardMostCompact" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.standardMostCompact" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Obstructions.standardMostCompact"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Obstructions.standardMostCompact

/-! ## `Obstructions.R24a`

Text: "**Result 24.** The Erlang approximation turns the PDE into an ODE at the cost of extra
variables." -/
namespace Alignment.Shadows.Obstructions.R24a

-- "the PDE" = the general non-Markovian system (uniform initials) is a PDE (S2, presupposed).
-- "turns … into an ODE" = the Erlang-staged system type is ODE (S1).
-- AMBIGUITY: "extra variables" read as relative to the Markovian ODE on the same network, for
-- every network (S3).
-- VOCAB-GAP: `erlangStaged` carries no stage count n.

@[sa_reference "Obstructions.R24a"]
def T : Prop :=
  systemRequired .erlangStaged .uniform = .ode ∧
  systemRequired .generalNonMarkov .uniform = .pde ∧
  ∀ n : NetworkType, extensionDim n .markovian < extensionDim n .erlangStaged

/-- S1: the Erlang approximation gives an ODE (uniform initials). -/
@[sa_shadow "Obstructions.R24a" 1]
def S1 : Prop := systemRequired .erlangStaged .uniform = .ode

/-- S2: the system being approximated (general non-Markovian, uniform) is a PDE. -/
@[sa_shadow "Obstructions.R24a" 2]
def S2 : Prop := systemRequired .generalNonMarkov .uniform = .pde

/-- S3: the Erlang ODE needs more variables than the Markovian ODE on every network. -/
@[sa_shadow "Obstructions.R24a" 3]
def S3 : Prop := ∀ n : NetworkType, extensionDim n .markovian < extensionDim n .erlangStaged

@[sa_ref_forward "Obstructions.R24a" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R24a" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.R24a" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Obstructions.R24a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Obstructions.R24a

/-! ## `Obstructions.R24c`

Text: "Here we show the Erlang variant always needs more variables than the Markovian variant on
the same network." -/
namespace Alignment.Shadows.Obstructions.R24c

-- "always" = for every network type.

@[sa_reference "Obstructions.R24c"]
def T : Prop := ∀ n : NetworkType, extensionDim n .markovian < extensionDim n .erlangStaged

/-- S1: on every network, the Erlang variant has strictly more variables than the Markovian one. -/
@[sa_shadow "Obstructions.R24c" 1]
def S1 : Prop := ∀ n : NetworkType, extensionDim n .markovian < extensionDim n .erlangStaged

@[sa_ref_forward "Obstructions.R24c" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Obstructions.R24c"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Obstructions.R24c

/-! ## `Obstructions.R23a`

Text: "**Result 23.** Complete classification of what system type is needed." -/
namespace Alignment.Shadows.Obstructions.R23a

-- AMBIGUITY: the sentence is the heading of the classification that follows (R23b-d). "Complete"
-- is read as: the case table covers every (transition, initial) combination:
-- uniform + Markovian → ODE (S1), uniform + Erlang → ODE (S2), uniform + general → PDE (S3),
-- localised + any transition → impossible (S4). These four cases exhaust all six combinations.

@[sa_reference "Obstructions.R23a"]
def T : Prop :=
  systemRequired .markovian .uniform = .ode ∧
  systemRequired .erlangStaged .uniform = .ode ∧
  systemRequired .generalNonMarkov .uniform = .pde ∧
  ∀ t : TransitionType, systemRequired t .localised = .impossible

/-- S1: uniform + Markovian → ODE. -/
@[sa_shadow "Obstructions.R23a" 1]
def S1 : Prop := systemRequired .markovian .uniform = .ode

/-- S2: uniform + Erlang-staged → ODE. -/
@[sa_shadow "Obstructions.R23a" 2]
def S2 : Prop := systemRequired .erlangStaged .uniform = .ode

/-- S3: uniform + general non-Markov → PDE. -/
@[sa_shadow "Obstructions.R23a" 3]
def S3 : Prop := systemRequired .generalNonMarkov .uniform = .pde

/-- S4: localised → impossible, for every transition type. -/
@[sa_shadow "Obstructions.R23a" 4]
def S4 : Prop := ∀ t : TransitionType, systemRequired t .localised = .impossible

@[sa_ref_forward "Obstructions.R23a" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R23a" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.R23a" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Obstructions.R23a" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "Obstructions.R23a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.Obstructions.R23a

/-! ## `Obstructions.R23b`

Text: "Uniform + Markovian/Erlang → ODE (always works)" -/
namespace Alignment.Shadows.Obstructions.R23b

-- "always works" = an EBCM variant exists on every network type, for both transition types.

@[sa_reference "Obstructions.R23b"]
def T : Prop :=
  systemRequired .markovian .uniform = .ode ∧
  systemRequired .erlangStaged .uniform = .ode ∧
  (∀ n : NetworkType, ebcmExists n .markovian .uniform) ∧
  (∀ n : NetworkType, ebcmExists n .erlangStaged .uniform)

/-- S1: uniform + Markovian → ODE. -/
@[sa_shadow "Obstructions.R23b" 1]
def S1 : Prop := systemRequired .markovian .uniform = .ode

/-- S2: uniform + Erlang-staged → ODE. -/
@[sa_shadow "Obstructions.R23b" 2]
def S2 : Prop := systemRequired .erlangStaged .uniform = .ode

/-- S3: uniform + Markovian always works: a variant exists on every network. -/
@[sa_shadow "Obstructions.R23b" 3]
def S3 : Prop := ∀ n : NetworkType, ebcmExists n .markovian .uniform

/-- S4: uniform + Erlang-staged always works: a variant exists on every network. -/
@[sa_shadow "Obstructions.R23b" 4]
def S4 : Prop := ∀ n : NetworkType, ebcmExists n .erlangStaged .uniform

@[sa_ref_forward "Obstructions.R23b" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R23b" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.R23b" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Obstructions.R23b" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "Obstructions.R23b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.Obstructions.R23b

/-! ## `Obstructions.R23c`

Text: "Uniform + general non-Markov → PDE (always works, infinite-dim)" -/
namespace Alignment.Shadows.Obstructions.R23c

-- "always works" = a variant exists on every network type (S2).
-- "infinite-dim" uses the DataTypes convention `extensionDim … = 0` for PDE systems (S3).

@[sa_reference "Obstructions.R23c"]
def T : Prop :=
  systemRequired .generalNonMarkov .uniform = .pde ∧
  (∀ n : NetworkType, ebcmExists n .generalNonMarkov .uniform) ∧
  (∀ n : NetworkType, extensionDim n .generalNonMarkov = 0)

/-- S1: uniform + general non-Markov → PDE. -/
@[sa_shadow "Obstructions.R23c" 1]
def S1 : Prop := systemRequired .generalNonMarkov .uniform = .pde

/-- S2: it always works: a variant exists on every network. -/
@[sa_shadow "Obstructions.R23c" 2]
def S2 : Prop := ∀ n : NetworkType, ebcmExists n .generalNonMarkov .uniform

/-- S3: it is infinite-dimensional on every network (sentinel 0). -/
@[sa_shadow "Obstructions.R23c" 3]
def S3 : Prop := ∀ n : NetworkType, extensionDim n .generalNonMarkov = 0

@[sa_ref_forward "Obstructions.R23c" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R23c" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.R23c" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Obstructions.R23c"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Obstructions.R23c

/-! ## `Obstructions.R25a`

Text: "**Result 25 — Theorem T2 (Marginalisation obstruction).** There exists a state at which
`M ∘ F₄_Kirkwood ≠ F₃_Kirkwood ∘ M`." -/
namespace Alignment.Shadows.Obstructions.R25a

open MarginalisationObstruction

@[sa_reference "Obstructions.R25a"]
def T : Prop := ∃ u : U4, M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u)

/-- S1: some order-4 state u has M (F₄ u) ≠ F₃ (M u). -/
@[sa_shadow "Obstructions.R25a" 1]
def S1 : Prop := ∃ u : U4, M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u)

@[sa_ref_forward "Obstructions.R25a" 1]
theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Obstructions.R25a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Obstructions.R25a

/-! ## `Obstructions.R25b`

Text: "Witness: `u = (a ↦ 1, b ↦ 3)`. * `M (F₄_Kirkwood u) (c) = 1·3 + 3 = 6`. *
`F₃_Kirkwood (M u) (c) = (1+3)² / 4 = 4`. The diagram fails by `6 ≠ 4`." -/
namespace Alignment.Shadows.Obstructions.R25b

open MarginalisationObstruction

-- The witness is "the state u with u(a) = 1 and u(b) = 3". It is stated through its values, so the
-- shadows do not depend on how u is written down. The intermediate expressions `1·3 + 3` and
-- `(1+3)²/4` are ℚ arithmetic equal to 6 and 4.

@[sa_reference "Obstructions.R25b"]
def T : Prop :=
  (∀ u : U4, u Idx4.a = 1 → u Idx4.b = 3 → M_witness (F4_Kirkwood u) Idx3.c = 6) ∧
  (∀ u : U4, u Idx4.a = 1 → u Idx4.b = 3 → F3_Kirkwood (M_witness u) Idx3.c = 4) ∧
  (∀ u : U4, u Idx4.a = 1 → u Idx4.b = 3 → M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u))

/-- S1: at the witness, M (F₄ u) (c) = 6. -/
@[sa_shadow "Obstructions.R25b" 1]
def S1 : Prop :=
  ∀ u : U4, u Idx4.a = 1 → u Idx4.b = 3 → M_witness (F4_Kirkwood u) Idx3.c = 6

/-- S2: at the witness, F₃ (M u) (c) = 4. -/
@[sa_shadow "Obstructions.R25b" 2]
def S2 : Prop :=
  ∀ u : U4, u Idx4.a = 1 → u Idx4.b = 3 → F3_Kirkwood (M_witness u) Idx3.c = 4

/-- S3: at the witness, the diagram fails: M (F₄ u) ≠ F₃ (M u). -/
@[sa_shadow "Obstructions.R25b" 3]
def S3 : Prop :=
  ∀ u : U4, u Idx4.a = 1 → u Idx4.b = 3 → M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u)

@[sa_ref_forward "Obstructions.R25b" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R25b" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.R25b" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Obstructions.R25b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Obstructions.R25b

/-! ## `Obstructions.kirkwoodObstructionWitnessValue-a`

Text: "The witness explicitly evaluated: the LHS minus the RHS is a fixed nonzero rational." -/
namespace Alignment.Shadows.Obstructions.kirkwoodObstructionWitnessValue_a

open MarginalisationObstruction

-- "The witness" = the Theorem-T2 witness u with u(a) = 1, u(b) = 3 (R25b), LHS = M (F₄ u) (c),
-- RHS = F₃ (M u) (c).
-- AMBIGUITY: "a fixed nonzero rational" read both as "LHS − RHS ≠ 0" (S1) and, because the
-- text says "explicitly evaluated" and "fixed", as a specific value. From the same passage (R25b),
-- that value is 6 − 4 = 2 (S2).

@[sa_reference "Obstructions.kirkwoodObstructionWitnessValue-a"]
def T : Prop :=
  (∀ u : U4, u Idx4.a = 1 → u Idx4.b = 3 →
      M_witness (F4_Kirkwood u) Idx3.c - F3_Kirkwood (M_witness u) Idx3.c ≠ 0) ∧
  (∀ u : U4, u Idx4.a = 1 → u Idx4.b = 3 →
      M_witness (F4_Kirkwood u) Idx3.c - F3_Kirkwood (M_witness u) Idx3.c = 2)

/-- S1: at the witness, LHS − RHS is nonzero. -/
@[sa_shadow "Obstructions.kirkwoodObstructionWitnessValue-a" 1]
def S1 : Prop :=
  ∀ u : U4, u Idx4.a = 1 → u Idx4.b = 3 →
    M_witness (F4_Kirkwood u) Idx3.c - F3_Kirkwood (M_witness u) Idx3.c ≠ 0

/-- S2: at the witness, LHS − RHS is the fixed rational 2 (= 6 − 4). -/
@[sa_shadow "Obstructions.kirkwoodObstructionWitnessValue-a" 2]
def S2 : Prop :=
  ∀ u : U4, u Idx4.a = 1 → u Idx4.b = 3 →
    M_witness (F4_Kirkwood u) Idx3.c - F3_Kirkwood (M_witness u) Idx3.c = 2

@[sa_ref_forward "Obstructions.kirkwoodObstructionWitnessValue-a" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.kirkwoodObstructionWitnessValue-a" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Obstructions.kirkwoodObstructionWitnessValue-a"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Obstructions.kirkwoodObstructionWitnessValue_a

noncomputable section

/-! ## `Obstructions.R20a` (re-authored blind)

Text: "Localised initial conditions (assumption 3) Among the three standard assumptions, only
localised seeding has no EBCM variant. [...] **Result 20.** Among the three standard assumptions,
only localised seeding has no EBCM variant."

S1: with localised seeding no EBCM variant exists, for any network and transition type; S2: relaxing
the other two assumptions (any network type, any transition type) with uniform seeding still leaves
an EBCM variant. -/
namespace Alignment.Shadows.Obstructions.R20a

@[sa_reference "Obstructions.R20a"]
def T : Prop :=
  (∀ (n : NetworkType) (t : TransitionType), ¬ ebcmExists n t .localised) ∧
  (∀ (n : NetworkType) (t : TransitionType), ebcmExists n t .uniform)

/-- S1: localised seeding has no EBCM variant. -/
@[sa_shadow "Obstructions.R20a" 1]
def S1 : Prop := ∀ (n : NetworkType) (t : TransitionType), ¬ ebcmExists n t .localised
/-- S2: every network and transition type has an EBCM variant under uniform seeding. -/
@[sa_shadow "Obstructions.R20a" 2]
def S2 : Prop := ∀ (n : NetworkType) (t : TransitionType), ebcmExists n t .uniform

@[sa_ref_forward "Obstructions.R20a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R20a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Obstructions.R20a"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Obstructions.R20a

/-! ## `Obstructions.R22a` (re-authored blind)

Text: "**Result 22.** In the hard-coded table `extensionDim`, the triangle-clustered EBCM has 13
variables, more than 3·4 − 1 for the standard EBCM."

-- AMBIGUITY: the transition type is not named; read as Markovian (the standard EBCM's). -/
namespace Alignment.Shadows.Obstructions.R22a

@[sa_reference "Obstructions.R22a"]
def T : Prop :=
  extensionDim .clusteredTriangles .markovian = 13 ∧
    extensionDim .configurationModel .markovian = 4 ∧
    3 * extensionDim .configurationModel .markovian - 1 < extensionDim .clusteredTriangles .markovian

/-- S1: the triangle-clustered EBCM has 13 variables in the table. -/
@[sa_shadow "Obstructions.R22a" 1]
def S1 : Prop := extensionDim .clusteredTriangles .markovian = 13
/-- S2: the standard EBCM has 4 variables in the table. -/
@[sa_shadow "Obstructions.R22a" 2]
def S2 : Prop := extensionDim .configurationModel .markovian = 4
/-- S3: 13 exceeds 3·4 − 1. -/
@[sa_shadow "Obstructions.R22a" 3]
def S3 : Prop :=
  3 * extensionDim .configurationModel .markovian - 1 < extensionDim .clusteredTriangles .markovian

@[sa_ref_forward "Obstructions.R22a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R22a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.R22a" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Obstructions.R22a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Obstructions.R22a

/-! ## `Obstructions.R23d` (re-authored blind)

Text: "Localised → impossible (by definition of `systemRequired`)" -/
namespace Alignment.Shadows.Obstructions.R23d

@[sa_reference "Obstructions.R23d"]
def T : Prop := ∀ t : TransitionType, systemRequired t .localised = .impossible

/-- S1: localised seeding requires an impossible system, for every transition type. -/
@[sa_shadow "Obstructions.R23d" 1]
def S1 : Prop := ∀ t : TransitionType, systemRequired t .localised = .impossible

@[sa_ref_forward "Obstructions.R23d" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Obstructions.R23d"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Obstructions.R23d

/-! ## `Obstructions.R24b` (blind)

Text: "The ODE approximation via n-stage Erlang needs 2n + 2 variables in the counting convention
of `extensionDim` (θ, n edge stages φ_{I_j}, n node stages I_j, and R): 4 for n = 1 and 6 for
n = 2. [...] For an n-stage Erlang infectious period on a configuration model, the standard 4
variables become 2n + 2 (θ, n edge stages φ_{I_j}, n node stages I_j, and R)."

-- AMBIGUITY: `extensionDim` has no stage count (`erlangStaged` carries no n). Read as: the
standard (one-stage, Markovian) configuration-model entry is the n = 1 count 2·1 + 2 = 4 (S1), and
the Erlang entry follows the 2n + 2 convention for some n ≥ 2 (S2). -/
namespace Alignment.Shadows.Obstructions.R24b

@[sa_reference "Obstructions.R24b"]
def T : Prop :=
  extensionDim .configurationModel .markovian = 2 * 1 + 2 ∧
    ∃ n : ℕ, 2 ≤ n ∧ extensionDim .configurationModel .erlangStaged = 2 * n + 2

/-- S1: the one-stage (standard) count is 2·1 + 2 = 4. -/
@[sa_shadow "Obstructions.R24b" 1]
def S1 : Prop := extensionDim .configurationModel .markovian = 2 * 1 + 2
/-- S2: the Erlang-staged count is 2n + 2 for some n ≥ 2. -/
@[sa_shadow "Obstructions.R24b" 2]
def S2 : Prop := ∃ n : ℕ, 2 ≤ n ∧ extensionDim .configurationModel .erlangStaged = 2 * n + 2

@[sa_ref_forward "Obstructions.R24b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.R24b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "Obstructions.R24b"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Obstructions.R24b

/-! ## `Obstructions.header.T1ImpliesTrajectoryFailure` (blind)

Text: "Theorem T1 (`dynamic_marginalisation_iff_equivariance` in `MarginalisationFunctor.lean`)
needs global flows of both systems, and the order-3 surrogate `c ↦ c²/4` has none
(`no_flow_F3Kℝ`), so T1 does not apply to this witness. The local statement does hold: for any local
solutions of the two surrogate systems from `u` and `M u`, `M · u₄(t) ≠ u₃(t)` for all small `t > 0`
(`MarginalisationDynamicalGap.witness_localGap_ge`). [...]"

Over ℝ (the surrogates `F4Kℝ`, `F3Kℝ`, `MℝLinCLM` of `MarginalisationDynamicalGap`, witness state
`u₁`). S1: `F3Kℝ` has no global flow; S2: local solutions (ψ 0 = start, derivative `F (ψ t)` for
`|t| < δ`) from `u₁` and `M u₁` satisfy `M ψ₄(t) ≠ ψ₃(t)` on some `(0, τ]`. That T1 needs flows is
a remark about its hypotheses. -/
namespace Alignment.Shadows.Obstructions.header_T1ImpliesTrajectoryFailure

open EBCMCategory.Marginalisation EBCMCategory.MarginalisationCharacterization
open EBCMCategory.MarginalisationDynamicalGap

/-- `ψ` is a local solution of `F` through `v`. -/
def LocalSol {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (F : V → V) (v : V)
    (ψ : ℝ → V) : Prop :=
  ψ 0 = v ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → HasDerivAt ψ (F (ψ t)) t

@[sa_reference "Obstructions.header.T1ImpliesTrajectoryFailure"]
def T : Prop :=
  (∀ φ₃ : U3ℝ → ℝ → U3ℝ, ¬ IsFlow F3Kℝ φ₃) ∧
  (∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
      ∃ τ : ℝ, 0 < τ ∧ ∀ t : ℝ, 0 < t → t ≤ τ → MℝLinCLM (ψ₄ t) ≠ ψ₃ t)

/-- S1: the order-3 surrogate has no global flow. -/
@[sa_shadow "Obstructions.header.T1ImpliesTrajectoryFailure" 1]
def S1 : Prop := ∀ φ₃ : U3ℝ → ℝ → U3ℝ, ¬ IsFlow F3Kℝ φ₃
/-- S2: local surrogate trajectories disagree for all small t > 0. -/
@[sa_shadow "Obstructions.header.T1ImpliesTrajectoryFailure" 2]
def S2 : Prop :=
  ∀ (ψ₄ : ℝ → U4ℝ) (ψ₃ : ℝ → U3ℝ), LocalSol F4Kℝ u₁ ψ₄ → LocalSol F3Kℝ (MℝLinCLM u₁) ψ₃ →
    ∃ τ : ℝ, 0 < τ ∧ ∀ t : ℝ, 0 < t → t ≤ τ → MℝLinCLM (ψ₄ t) ≠ ψ₃ t

@[sa_ref_forward "Obstructions.header.T1ImpliesTrajectoryFailure" 1] theorem ref_fwd1 :
    T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.header.T1ImpliesTrajectoryFailure" 2] theorem ref_fwd2 :
    T → S2 := fun t => t.2
@[sa_complete "Obstructions.header.T1ImpliesTrajectoryFailure"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Obstructions.header_T1ImpliesTrajectoryFailure

/-! ## `Obstructions.header.kirkwoodHierarchyInconsistent` (re-authored blind)

Text: "For a two-variable surrogate of a closed order-4 moment system and a one-variable surrogate
of a closed order-3 system (defined below), the closed dynamics do **not** project consistently
under the surrogate marginalisation `M(a,b) = a + b`. [...] does **not** commute at the witness
state."

S1: `M(a,b) = a + b` (`M_witness`); S2: the closed dynamics do not project consistently (some state
where `M ∘ F₄ ≠ F₃ ∘ M`); S3: they do not commute at the witness state.
-- AMBIGUITY: the witness state is not given in the quoted text; read as `(a, b) = (1, 3)`, the
witness point `u₁` of the marginalisation modules. -/
namespace Alignment.Shadows.Obstructions.header_kirkwoodHierarchyInconsistent

open MarginalisationObstruction

/-- The witness state `(a, b) = (1, 3)`. -/
def wQ : U4 := fun i =>
  match i with
  | Idx4.a => 1
  | Idx4.b => 3

@[sa_reference "Obstructions.header.kirkwoodHierarchyInconsistent"]
def T : Prop :=
  (∀ u : U4, M_witness u Idx3.c = u Idx4.a + u Idx4.b) ∧
  (∃ u : U4, M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u)) ∧
  M_witness (F4_Kirkwood wQ) ≠ F3_Kirkwood (M_witness wQ)

/-- S1: the surrogate marginalisation is `M(a,b) = a + b`. -/
@[sa_shadow "Obstructions.header.kirkwoodHierarchyInconsistent" 1]
def S1 : Prop := ∀ u : U4, M_witness u Idx3.c = u Idx4.a + u Idx4.b
/-- S2: the closed dynamics do not project consistently. -/
@[sa_shadow "Obstructions.header.kirkwoodHierarchyInconsistent" 2]
def S2 : Prop := ∃ u : U4, M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u)
/-- S3: they do not commute at the witness state. -/
@[sa_shadow "Obstructions.header.kirkwoodHierarchyInconsistent" 3]
def S3 : Prop := M_witness (F4_Kirkwood wQ) ≠ F3_Kirkwood (M_witness wQ)

@[sa_ref_forward "Obstructions.header.kirkwoodHierarchyInconsistent" 1] theorem ref_fwd1 :
    T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.header.kirkwoodHierarchyInconsistent" 2] theorem ref_fwd2 :
    T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.header.kirkwoodHierarchyInconsistent" 3] theorem ref_fwd3 :
    T → S3 := fun t => t.2.2
@[sa_complete "Obstructions.header.kirkwoodHierarchyInconsistent"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Obstructions.header_kirkwoodHierarchyInconsistent

/-! ## `Obstructions.header.networkNotObstruction` (re-authored blind)

Text: "Network structure (assumption 1) For the specific network classes below an EBCM variant is
known, at a dimension cost; this is a literature summary, not a statement about network structure
in general:"

The network classes are the constructors of `NetworkType`. S1: each has an EBCM variant (Markovian
dynamics, uniform seeding); S2 ("at a dimension cost"): each non-configuration-model class needs
more ODE variables than the standard EBCM. -- AMBIGUITY: the cost is read with Markovian dynamics. -/
namespace Alignment.Shadows.Obstructions.header_networkNotObstruction

@[sa_reference "Obstructions.header.networkNotObstruction"]
def T : Prop :=
  (∀ n : NetworkType, ebcmExists n .markovian .uniform) ∧
  (∀ n : NetworkType, n ≠ .configurationModel →
      extensionDim .configurationModel .markovian < extensionDim n .markovian)

/-- S1: every listed network class has an EBCM variant. -/
@[sa_shadow "Obstructions.header.networkNotObstruction" 1]
def S1 : Prop := ∀ n : NetworkType, ebcmExists n .markovian .uniform
/-- S2: at a dimension cost. -/
@[sa_shadow "Obstructions.header.networkNotObstruction" 2]
def S2 : Prop :=
  ∀ n : NetworkType, n ≠ .configurationModel →
    extensionDim .configurationModel .markovian < extensionDim n .markovian

@[sa_ref_forward "Obstructions.header.networkNotObstruction" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "Obstructions.header.networkNotObstruction" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2
@[sa_complete "Obstructions.header.networkNotObstruction"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.Obstructions.header_networkNotObstruction

/-! ## `Obstructions.header.smallestFaithfulWitness` (blind)

Text: "This is one arithmetic witness for one pair of surrogate fields, not a general law: with
`M = id` a quadratic field commutes with itself, and at the witness state the quadratic field
`c ↦ 3c²/8` agrees with `M ∘ F₄` (both give 6; `MarginalisationDynamicalGap.kirkwoodForm_matches_at_witness`)."

Over ℝ (the cited result is about `F4Kℝ`, `MℝLinCLM`, witness `u₁`). S1: with `M = id` on ℝ,
`x ↦ x²` commutes with itself (`Equivariant`); S2: `c ↦ 3c²/8` agrees with `M ∘ F4Kℝ` at `u₁`; S3:
both give 6. -/
namespace Alignment.Shadows.Obstructions.header_smallestFaithfulWitness

open EBCMCategory.Marginalisation EBCMCategory.MarginalisationCharacterization
open EBCMCategory.MarginalisationDynamicalGap MarginalisationObstruction

/-- The closure `c ↦ 3c²/8`. -/
def C3match (v : U3ℝ) : U3ℝ := fun _ => 3 * v Idx3.c ^ 2 / 8

@[sa_reference "Obstructions.header.smallestFaithfulWitness"]
def T : Prop :=
  Equivariant (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (fun x => x ^ 2) (fun x => x ^ 2) ∧
    MℝLinCLM (F4Kℝ u₁) = C3match (MℝLinCLM u₁) ∧ MℝLinCLM (F4Kℝ u₁) = fun _ => 6

/-- S1: with `M = id`, a quadratic field commutes with itself. -/
@[sa_shadow "Obstructions.header.smallestFaithfulWitness" 1]
def S1 : Prop := Equivariant (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (fun x => x ^ 2) (fun x => x ^ 2)
/-- S2: `c ↦ 3c²/8` agrees with `M ∘ F₄` at the witness. -/
@[sa_shadow "Obstructions.header.smallestFaithfulWitness" 2]
def S2 : Prop := MℝLinCLM (F4Kℝ u₁) = C3match (MℝLinCLM u₁)
/-- S3: both give 6. -/
@[sa_shadow "Obstructions.header.smallestFaithfulWitness" 3]
def S3 : Prop := MℝLinCLM (F4Kℝ u₁) = fun _ => 6

@[sa_ref_forward "Obstructions.header.smallestFaithfulWitness" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "Obstructions.header.smallestFaithfulWitness" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "Obstructions.header.smallestFaithfulWitness" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2
@[sa_complete "Obstructions.header.smallestFaithfulWitness"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Obstructions.header_smallestFaithfulWitness

/-! ## `Obstructions.header.surrogateForms` (blind)

Text: "The surrogate right-hand sides are chosen, not derived from a closure: `F₄(a,b) = (a·b, b)`
is bilinear, as a pair-Kirkwood closure is, and `F₃(c) = c²/4` is quadratic."

The component formulas of `F4_Kirkwood` and `F3_Kirkwood`; "chosen, not derived" is a remark. -/
namespace Alignment.Shadows.Obstructions.header_surrogateForms

open MarginalisationObstruction

@[sa_reference "Obstructions.header.surrogateForms"]
def T : Prop :=
  (∀ u : U4, F4_Kirkwood u Idx4.a = u Idx4.a * u Idx4.b) ∧
  (∀ u : U4, F4_Kirkwood u Idx4.b = u Idx4.b) ∧
  (∀ v : U3, F3_Kirkwood v Idx3.c = v Idx3.c ^ 2 / 4)

/-- S1: the a-component of `F₄` is `a·b`. -/
@[sa_shadow "Obstructions.header.surrogateForms" 1]
def S1 : Prop := ∀ u : U4, F4_Kirkwood u Idx4.a = u Idx4.a * u Idx4.b
/-- S2: the b-component of `F₄` is `b`. -/
@[sa_shadow "Obstructions.header.surrogateForms" 2]
def S2 : Prop := ∀ u : U4, F4_Kirkwood u Idx4.b = u Idx4.b
/-- S3: `F₃(c) = c²/4`. -/
@[sa_shadow "Obstructions.header.surrogateForms" 3]
def S3 : Prop := ∀ v : U3, F3_Kirkwood v Idx3.c = v Idx3.c ^ 2 / 4

@[sa_ref_forward "Obstructions.header.surrogateForms" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.header.surrogateForms" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "Obstructions.header.surrogateForms" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2
@[sa_complete "Obstructions.header.surrogateForms"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Obstructions.header_surrogateForms

/-! ## `Obstructions.markovIsOde` (re-authored blind)

Text: "Markovian dynamics with uniform initial infection give an ODE system." -/
namespace Alignment.Shadows.Obstructions.markovIsOde

@[sa_reference "Obstructions.markovIsOde"]
def T : Prop := systemRequired .markovian .uniform = .ode

/-- S1: Markovian + uniform requires an ODE system. -/
@[sa_shadow "Obstructions.markovIsOde" 1]
def S1 : Prop := systemRequired .markovian .uniform = .ode

@[sa_ref_forward "Obstructions.markovIsOde" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Obstructions.markovIsOde"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Obstructions.markovIsOde

/-! ## `Obstructions.table.R18` (re-authored blind)

Text: "| 18 | Triangle clustering: standard fails, triangle EBCM (ODE) |"

S1: the standard EBCM is not valid on triangle-clustered networks (any dynamics and seeding); S2: a
triangle EBCM exists (Markovian, uniform); S3: it is an ODE (finite nonzero dimension in
`extensionDim`, which returns 0 for PDE systems). -/
namespace Alignment.Shadows.Obstructions.table_R18

@[sa_reference "Obstructions.table.R18"]
def T : Prop :=
  (∀ (t : TransitionType) (i : InitCondType), ¬ standardEbcmValid .clusteredTriangles t i) ∧
  ebcmExists .clusteredTriangles .markovian .uniform ∧
  extensionDim .clusteredTriangles .markovian ≠ 0

/-- S1: the standard EBCM fails on triangle-clustered networks. -/
@[sa_shadow "Obstructions.table.R18" 1]
def S1 : Prop := ∀ (t : TransitionType) (i : InitCondType), ¬ standardEbcmValid .clusteredTriangles t i
/-- S2: a triangle EBCM exists. -/
@[sa_shadow "Obstructions.table.R18" 2]
def S2 : Prop := ebcmExists .clusteredTriangles .markovian .uniform
/-- S3: the triangle EBCM is an ODE system. -/
@[sa_shadow "Obstructions.table.R18" 3]
def S3 : Prop := extensionDim .clusteredTriangles .markovian ≠ 0

@[sa_ref_forward "Obstructions.table.R18" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.table.R18" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.table.R18" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Obstructions.table.R18"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Obstructions.table_R18

/-! ## `Obstructions.table.R22` (re-authored blind)

Text: "| 22 | Hard-coded counts: clustered (13) > 3·standard (4) − 1 |" -/
namespace Alignment.Shadows.Obstructions.table_R22

@[sa_reference "Obstructions.table.R22"]
def T : Prop :=
  extensionDim .clusteredTriangles .markovian = 13 ∧
    extensionDim .configurationModel .markovian = 4 ∧
    3 * extensionDim .configurationModel .markovian - 1 < extensionDim .clusteredTriangles .markovian

/-- S1: clustered count 13. -/
@[sa_shadow "Obstructions.table.R22" 1]
def S1 : Prop := extensionDim .clusteredTriangles .markovian = 13
/-- S2: standard count 4. -/
@[sa_shadow "Obstructions.table.R22" 2]
def S2 : Prop := extensionDim .configurationModel .markovian = 4
/-- S3: clustered > 3·standard − 1. -/
@[sa_shadow "Obstructions.table.R22" 3]
def S3 : Prop :=
  3 * extensionDim .configurationModel .markovian - 1 < extensionDim .clusteredTriangles .markovian

@[sa_ref_forward "Obstructions.table.R22" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.table.R22" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.table.R22" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "Obstructions.table.R22"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.Obstructions.table_R22

/-! ## `Obstructions.table.R23` (re-authored blind)

Text: "| 23 | `systemRequired` is ODE, PDE or impossible as tabulated |"

Every value of `SystemType` is one of the three, so the content is the tabulation (from the
`TransitionType` / `InitCondType` descriptions): Markovian and Erlang-staged with uniform seeding
→ ODE; general non-Markovian with uniform seeding → PDE; localised seeding → impossible. -/
namespace Alignment.Shadows.Obstructions.table_R23

@[sa_reference "Obstructions.table.R23"]
def T : Prop :=
  systemRequired .markovian .uniform = .ode ∧ systemRequired .erlangStaged .uniform = .ode ∧
    systemRequired .generalNonMarkov .uniform = .pde ∧
    ∀ t : TransitionType, systemRequired t .localised = .impossible

/-- S1: Markovian → ODE. -/
@[sa_shadow "Obstructions.table.R23" 1]
def S1 : Prop := systemRequired .markovian .uniform = .ode
/-- S2: Erlang-staged → ODE. -/
@[sa_shadow "Obstructions.table.R23" 2]
def S2 : Prop := systemRequired .erlangStaged .uniform = .ode
/-- S3: general non-Markovian → PDE. -/
@[sa_shadow "Obstructions.table.R23" 3]
def S3 : Prop := systemRequired .generalNonMarkov .uniform = .pde
/-- S4: localised → impossible. -/
@[sa_shadow "Obstructions.table.R23" 4]
def S4 : Prop := ∀ t : TransitionType, systemRequired t .localised = .impossible

@[sa_ref_forward "Obstructions.table.R23" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "Obstructions.table.R23" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "Obstructions.table.R23" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "Obstructions.table.R23" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "Obstructions.table.R23"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.Obstructions.table_R23

/-! ## `Obstructions.table.R24` (blind)

Text: "| 24 | Erlang staging needs more variables than Markovian |"

-- AMBIGUITY: the network type is not named; read for the configuration model (the setting of the
standard EBCM and of Result 24). -/
namespace Alignment.Shadows.Obstructions.table_R24

@[sa_reference "Obstructions.table.R24"]
def T : Prop :=
  extensionDim .configurationModel .markovian < extensionDim .configurationModel .erlangStaged

/-- S1: Erlang staging needs more variables than Markovian dynamics. -/
@[sa_shadow "Obstructions.table.R24" 1]
def S1 : Prop :=
  extensionDim .configurationModel .markovian < extensionDim .configurationModel .erlangStaged

@[sa_ref_forward "Obstructions.table.R24" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "Obstructions.table.R24"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.Obstructions.table_R24

end
