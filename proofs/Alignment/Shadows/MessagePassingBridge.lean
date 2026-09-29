import Alignment.Registry
import EBCMCategory.MessagePassingBridge
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Blind shadow sets: group `MessagePassingBridge`

Written blind (SA-PASS role 2). Sources read: `Alignment/README.md`, `SA-PASS_SKILL.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/MessagePassingBridge.md`, the
`claims_blind.yaml` entries of this group, and Sherborne et al. (J. Math. Biol. 2018,
`papers/s00285-017-1155-0.md`, Sect. 3, Eqs. 14, 18, 22) for the meaning of `[SI]`, `z`, `G₁`.

Vocabulary: `EpiProcess.f_mp` (the text's f(a)), `EpiProcess.f_ebcm` (the text's f̂(a)),
`mpToEBCM`/`ebcmToMP` (the bridge maps H₁ ↦ Θ, Θ ↦ H₁), `ModelFamily.requiredAssumptions`
("the assumptions required for each model to be exact"), `ModelFamily.effectiveDim`,
`SIRParams.transmissibility`, `edgeModel` (EBCM), `nodeModel` (node-based / mass-action SIR),
`PGFData.poisson`. The hierarchy order (most general first) is the one of the `ModelFamily`
docstring and the module header: MP, EBCM PDE, EBCM ODE, DSA, pairwise, mass-action.

Claims about `[SI]` and trajectories are stated with Mathlib derivatives (`HasDerivAt`), since the
library has no MP/EBCM/pairwise dynamics.

Re-authored blind (second pass, from the current claim texts, `DataTypes/*.md`, the README,
`SA-PASS_SKILL.md`, `Example/ExampleShadows.lean` and background papers only): the blocks marked
"(re-authored blind)" or "(blind)" near the end of this file (with any `Shared2` helper
namespace). Ids of that pass not formalised (remarks on proof status, on which notions the library
defines, or cited results needing models the vocabulary lacks): `R68c`, `summary.nonPT`.
-/

namespace Alignment.Shadows.MessagePassingBridge.Common

/-- A model family is exact ("in its validity regime") in a scenario in which exactly the
assumptions of `A` hold: every assumption it requires is among them (reading of the `Assumption`
docstring "What assumptions are needed for each model to be exact"). -/
def exactUnder (m : ModelFamily) (A : List Assumption) : Prop :=
  ∀ a ∈ m.requiredAssumptions, a ∈ A

/-- The "Markov + PT" scenario on configuration-model networks: the ambient configuration-model
setting, Markovian transmission and recovery, and a PT degree distribution (Poisson is not
assumed). -/
def markovPT : List Assumption :=
  [Assumption.configModel, Assumption.markovTransmission, Assumption.markovRecovery,
    Assumption.poissonType]

/-- The re-parametrised pairwise susceptible equation obtained from the MP message
(Sherborne et al. Eq. 18 with `[S] = ψ(H₁)`): if the message trajectory `H` satisfies
`dH/dt = -β·[SI]/ψ'(H)` (Eq. 18, where `ψ'(H₁) = z⟨k⟩N·G₁(H₁)` for `ψ = zN·G₀`), then the
node-level susceptibles `S(t) = ψ(H(t))` satisfy the pairwise equation `dS/dt = -β·[SI]`.
`ψ` ranges over all functions differentiable at `H t` (no PGF property is used by the text). -/
def PairwiseFromMessage : Prop :=
  ∀ (ψ H SI : ℝ → ℝ) (β t dψ : ℝ),
    HasDerivAt ψ dψ (H t) → dψ ≠ 0 →
    HasDerivAt H (-β * SI t / dψ) t →
    HasDerivAt (fun s => ψ (H s)) (-β * SI t) t

end Alignment.Shadows.MessagePassingBridge.Common

/-! ## Header table rows -/

namespace Alignment.Shadows.MessagePassingBridge.table_R60

/-! Blind text: "| 60 | Hazard-density identity: f(a) = f̂(a) |"

`EpiProcess` abstracts the processes at a single age point; f is `f_mp`, f̂ is `f_ebcm`.
-- VOCAB-GAP: the age dependence (f and f̂ as functions of a, with ξ = exp(-∫ hazard)) is not
-- expressible through `EpiProcess`; the identity is stated for every `EpiProcess` value (every
-- age point of every process). -/

@[sa_reference "MessagePassingBridge.table.R60"]
def T : Prop := ∀ e : EpiProcess, e.f_mp = e.f_ebcm

/-- S1: f(a) = f̂(a) for every process at every age point. -/
@[sa_shadow "MessagePassingBridge.table.R60" 1]
def S1 : Prop := ∀ e : EpiProcess, e.f_mp = e.f_ebcm

@[sa_ref_forward "MessagePassingBridge.table.R60" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MessagePassingBridge.table.R60"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MessagePassingBridge.table_R60

namespace Alignment.Shadows.MessagePassingBridge.table_R61

/-! Blind text: "| 61 | MP ≡ EBCM: message = edge probability |"

-- AMBIGUITY: "MP ≡ EBCM" read as the header's "‖ : isomorphism (lossless, both directions)" of
-- the bridge maps (S3, S4: both round trips are the identity); "message = edge probability" read
-- as: the bridge maps send the message H₁ to an edge probability Θ of the same value and back
-- (S1, S2).
-- VOCAB-GAP: the trajectory-level reading ("MP and EBCM produce identical trajectories") is not
-- expressible (no MP/EBCM dynamics in the vocabulary); not shadowed. -/

@[sa_reference "MessagePassingBridge.table.R61"]
def T : Prop :=
  (∀ m : MPState, (mpToEBCM m).Θ = m.H₁) ∧
  (∀ e : EBCMState, (ebcmToMP e).H₁ = e.Θ) ∧
  (∀ m : MPState, ebcmToMP (mpToEBCM m) = m) ∧
  (∀ e : EBCMState, mpToEBCM (ebcmToMP e) = e)

/-- S1: MP → EBCM: the edge probability equals the message. -/
@[sa_shadow "MessagePassingBridge.table.R61" 1]
def S1 : Prop := ∀ m : MPState, (mpToEBCM m).Θ = m.H₁

/-- S2: EBCM → MP: the message equals the edge probability. -/
@[sa_shadow "MessagePassingBridge.table.R61" 2]
def S2 : Prop := ∀ e : EBCMState, (ebcmToMP e).H₁ = e.Θ

/-- S3: MP → EBCM → MP is the identity. -/
@[sa_shadow "MessagePassingBridge.table.R61" 3]
def S3 : Prop := ∀ m : MPState, ebcmToMP (mpToEBCM m) = m

/-- S4: EBCM → MP → EBCM is the identity. -/
@[sa_shadow "MessagePassingBridge.table.R61" 4]
def S4 : Prop := ∀ e : EBCMState, mpToEBCM (ebcmToMP e) = e

@[sa_ref_forward "MessagePassingBridge.table.R61" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MessagePassingBridge.table.R61" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MessagePassingBridge.table.R61" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1

@[sa_ref_forward "MessagePassingBridge.table.R61" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2

@[sa_complete "MessagePassingBridge.table.R61"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.MessagePassingBridge.table_R61

namespace Alignment.Shadows.MessagePassingBridge.table_R62

open Alignment.Shadows.MessagePassingBridge.Common

/-! Blind text: "| 62 | Re-parametrised pairwise from MP |"

-- AMBIGUITY: the row is a title. Read as: the pairwise variable [SI], defined from the MP message
-- through Sherborne et al. Eq. 18, turns the MP model into the pairwise susceptible equation
-- d[S]/dt = -β·[SI] with [S] = ψ(H₁) (the checkable core of the re-parametrisation).
-- VOCAB-GAP: the full re-parametrised system (Eq. 22: equations for H₁, [SI], [I] with the
-- integral terms in q, g) is not expressible with the DataTypes; stated with `HasDerivAt`. -/

@[sa_reference "MessagePassingBridge.table.R62"]
def T : Prop := PairwiseFromMessage

/-- S1: with Eq. 18, S(t) = ψ(H₁(t)) satisfies dS/dt = -β·[SI]. -/
@[sa_shadow "MessagePassingBridge.table.R62" 1]
def S1 : Prop :=
  ∀ (ψ H SI : ℝ → ℝ) (β t dψ : ℝ),
    HasDerivAt ψ dψ (H t) → dψ ≠ 0 →
    HasDerivAt H (-β * SI t / dψ) t →
    HasDerivAt (fun s => ψ (H s)) (-β * SI t) t

@[sa_ref_forward "MessagePassingBridge.table.R62" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MessagePassingBridge.table.R62"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MessagePassingBridge.table_R62

namespace Alignment.Shadows.MessagePassingBridge.table_R63

/-! Blind text: "| 63 | Markovian specialization to Volz ODE |"

-- AMBIGUITY: read through the assumption vocabulary: the Volz ODE (`ebcmODE`, "Markovian EBCM") is
-- the specialisation of the EBCM PDE (`ebcmPDE`, "Non-Markovian EBCM ... any τ(a), q(a)") obtained
-- by adding the Markovian assumptions: the ODE requires Markovian transmission and recovery
-- (S1, S2), the PDE requires neither (S3, S4), and the ODE keeps every PDE assumption (S5,
-- "specialization").
-- VOCAB-GAP: the dynamical collapse PDE → ODE itself is not expressible (no dynamics). -/

@[sa_reference "MessagePassingBridge.table.R63"]
def T : Prop :=
  Assumption.markovTransmission ∈ ModelFamily.ebcmODE.requiredAssumptions ∧
  Assumption.markovRecovery ∈ ModelFamily.ebcmODE.requiredAssumptions ∧
  Assumption.markovTransmission ∉ ModelFamily.ebcmPDE.requiredAssumptions ∧
  Assumption.markovRecovery ∉ ModelFamily.ebcmPDE.requiredAssumptions ∧
  (∀ a ∈ ModelFamily.ebcmPDE.requiredAssumptions, a ∈ ModelFamily.ebcmODE.requiredAssumptions)

/-- S1: the Volz ODE requires Markovian transmission. -/
@[sa_shadow "MessagePassingBridge.table.R63" 1]
def S1 : Prop := Assumption.markovTransmission ∈ ModelFamily.ebcmODE.requiredAssumptions

/-- S2: the Volz ODE requires Markovian recovery. -/
@[sa_shadow "MessagePassingBridge.table.R63" 2]
def S2 : Prop := Assumption.markovRecovery ∈ ModelFamily.ebcmODE.requiredAssumptions

/-- S3: the (non-Markovian) EBCM PDE does not require Markovian transmission. -/
@[sa_shadow "MessagePassingBridge.table.R63" 3]
def S3 : Prop := Assumption.markovTransmission ∉ ModelFamily.ebcmPDE.requiredAssumptions

/-- S4: the (non-Markovian) EBCM PDE does not require Markovian recovery. -/
@[sa_shadow "MessagePassingBridge.table.R63" 4]
def S4 : Prop := Assumption.markovRecovery ∉ ModelFamily.ebcmPDE.requiredAssumptions

/-- S5: specialisation: every assumption of the EBCM PDE is also required by the Volz ODE. -/
@[sa_shadow "MessagePassingBridge.table.R63" 5]
def S5 : Prop :=
  ∀ a ∈ ModelFamily.ebcmPDE.requiredAssumptions, a ∈ ModelFamily.ebcmODE.requiredAssumptions

@[sa_ref_forward "MessagePassingBridge.table.R63" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MessagePassingBridge.table.R63" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MessagePassingBridge.table.R63" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1

@[sa_ref_forward "MessagePassingBridge.table.R63" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1

@[sa_ref_forward "MessagePassingBridge.table.R63" 5]
theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2

@[sa_complete "MessagePassingBridge.table.R63"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.MessagePassingBridge.table_R63

namespace Alignment.Shadows.MessagePassingBridge.table_R66

open Alignment.Shadows.MessagePassingBridge.Common

/-! Blind text: "| 66 | The bridge: [SI] connects MP/EBCM to pairwise world |"

-- AMBIGUITY: "connects" read as: [SI], defined from the MP message / EBCM edge probability
-- H₁ = Θ via Sherborne et al. Eq. 18, makes the node-level susceptibles S = ψ(H₁) obey the
-- pairwise equation dS/dt = -β·[SI].
-- VOCAB-GAP: no pairwise dynamics in the DataTypes; stated with `HasDerivAt`. -/

@[sa_reference "MessagePassingBridge.table.R66"]
def T : Prop := PairwiseFromMessage

/-- S1: with Eq. 18, S(t) = ψ(H₁(t)) satisfies dS/dt = -β·[SI]. -/
@[sa_shadow "MessagePassingBridge.table.R66" 1]
def S1 : Prop :=
  ∀ (ψ H SI : ℝ → ℝ) (β t dψ : ℝ),
    HasDerivAt ψ dψ (H t) → dψ ≠ 0 →
    HasDerivAt H (-β * SI t / dψ) t →
    HasDerivAt (fun s => ψ (H s)) (-β * SI t) t

@[sa_ref_forward "MessagePassingBridge.table.R66" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MessagePassingBridge.table.R66"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MessagePassingBridge.table_R66

namespace Alignment.Shadows.MessagePassingBridge.table_R67

/-! Blind text: "| 67 | Pairwise requires PT; MP/EBCM do not |"

-- AMBIGUITY: "EBCM" read as both EBCM families, the PDE (`ebcmPDE`) and the ODE (`ebcmODE`);
-- "requires PT" read as `poissonType ∈ requiredAssumptions`. -/

@[sa_reference "MessagePassingBridge.table.R67"]
def T : Prop :=
  Assumption.poissonType ∈ ModelFamily.pairwise.requiredAssumptions ∧
  Assumption.poissonType ∉ ModelFamily.messagePassing.requiredAssumptions ∧
  Assumption.poissonType ∉ ModelFamily.ebcmPDE.requiredAssumptions ∧
  Assumption.poissonType ∉ ModelFamily.ebcmODE.requiredAssumptions

/-- S1: pairwise requires PT. -/
@[sa_shadow "MessagePassingBridge.table.R67" 1]
def S1 : Prop := Assumption.poissonType ∈ ModelFamily.pairwise.requiredAssumptions

/-- S2: MP does not require PT. -/
@[sa_shadow "MessagePassingBridge.table.R67" 2]
def S2 : Prop := Assumption.poissonType ∉ ModelFamily.messagePassing.requiredAssumptions

/-- S3: the EBCM PDE does not require PT. -/
@[sa_shadow "MessagePassingBridge.table.R67" 3]
def S3 : Prop := Assumption.poissonType ∉ ModelFamily.ebcmPDE.requiredAssumptions

/-- S4: the EBCM ODE does not require PT. -/
@[sa_shadow "MessagePassingBridge.table.R67" 4]
def S4 : Prop := Assumption.poissonType ∉ ModelFamily.ebcmODE.requiredAssumptions

@[sa_ref_forward "MessagePassingBridge.table.R67" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MessagePassingBridge.table.R67" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MessagePassingBridge.table.R67" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1

@[sa_ref_forward "MessagePassingBridge.table.R67" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2

@[sa_complete "MessagePassingBridge.table.R67"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.MessagePassingBridge.table_R67

namespace Alignment.Shadows.MessagePassingBridge.R60

/-! Blind text: "**Result 60.** The hazard-density identity: f(a) = f̂(a). [...]
f(a) = τ(a)·ξ_q(a) = ζ(a)·ξ_τ(a)·ξ_q(a) = f̂(a)"

f is `f_mp`, f̂ is `f_ebcm`; τ(a) = ζ(a)·ξ_τ(a) (the `EpiProcess` docstring's definition of the
transmission density; τ is not a field). The displayed chain gives three requirements: the
identity (S1), its first link f = τ·ξ_q = ζ·ξ_τ·ξ_q (S2) and its last link ζ·ξ_τ·ξ_q = f̂ (S3).
-- VOCAB-GAP: age dependence abstracted to a single age point (`EpiProcess`), as for table.R60. -/

@[sa_reference "MessagePassingBridge.R60"]
def T : Prop :=
  ∀ e : EpiProcess,
    e.f_mp = e.f_ebcm ∧ e.f_mp = (e.ζ * e.ξ_τ) * e.ξ_q ∧ e.ζ * e.ξ_τ * e.ξ_q = e.f_ebcm

/-- S1: f(a) = f̂(a). -/
@[sa_shadow "MessagePassingBridge.R60" 1]
def S1 : Prop := ∀ e : EpiProcess, e.f_mp = e.f_ebcm

/-- S2: f(a) = τ(a)·ξ_q(a) with τ(a) = ζ(a)·ξ_τ(a). -/
@[sa_shadow "MessagePassingBridge.R60" 2]
def S2 : Prop := ∀ e : EpiProcess, e.f_mp = (e.ζ * e.ξ_τ) * e.ξ_q

/-- S3: ζ(a)·ξ_τ(a)·ξ_q(a) = f̂(a). -/
@[sa_shadow "MessagePassingBridge.R60" 3]
def S3 : Prop := ∀ e : EpiProcess, e.ζ * e.ξ_τ * e.ξ_q = e.f_ebcm

@[sa_ref_forward "MessagePassingBridge.R60" 1]
theorem ref_fwd1 : T → S1 := fun t e => (t e).1

@[sa_ref_forward "MessagePassingBridge.R60" 2]
theorem ref_fwd2 : T → S2 := fun t e => (t e).2.1

@[sa_ref_forward "MessagePassingBridge.R60" 3]
theorem ref_fwd3 : T → S3 := fun t e => (t e).2.2

@[sa_complete "MessagePassingBridge.R60"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := fun e => ⟨s1 e, s2 e, s3 e⟩

end Alignment.Shadows.MessagePassingBridge.R60

namespace Alignment.Shadows.MessagePassingBridge.R61a

/-! Blind text: "**Result 61.** The MP ↔ EBCM bridge is an isomorphism."

-- AMBIGUITY: "isomorphism" read as: the two bridge maps `mpToEBCM`, `ebcmToMP` are mutually
-- inverse (both round trips are the identity), rather than merely "some bijection exists". -/

@[sa_reference "MessagePassingBridge.R61a"]
def T : Prop :=
  (∀ m : MPState, ebcmToMP (mpToEBCM m) = m) ∧ (∀ e : EBCMState, mpToEBCM (ebcmToMP e) = e)

/-- S1: MP → EBCM → MP is the identity (`ebcmToMP` is a left inverse of `mpToEBCM`). -/
@[sa_shadow "MessagePassingBridge.R61a" 1]
def S1 : Prop := ∀ m : MPState, ebcmToMP (mpToEBCM m) = m

/-- S2: EBCM → MP → EBCM is the identity (`ebcmToMP` is a right inverse of `mpToEBCM`). -/
@[sa_shadow "MessagePassingBridge.R61a" 2]
def S2 : Prop := ∀ e : EBCMState, mpToEBCM (ebcmToMP e) = e

@[sa_ref_forward "MessagePassingBridge.R61a" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MessagePassingBridge.R61a" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "MessagePassingBridge.R61a"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MessagePassingBridge.R61a

namespace Alignment.Shadows.MessagePassingBridge.R61b

/-! Blind text: "Round-trip EBCM → MP → EBCM is the identity." -/

@[sa_reference "MessagePassingBridge.R61b"]
def T : Prop := ∀ e : EBCMState, mpToEBCM (ebcmToMP e) = e

/-- S1: for every EBCM state, EBCM → MP → EBCM returns it. -/
@[sa_shadow "MessagePassingBridge.R61b" 1]
def S1 : Prop := ∀ e : EBCMState, mpToEBCM (ebcmToMP e) = e

@[sa_ref_forward "MessagePassingBridge.R61b" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MessagePassingBridge.R61b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MessagePassingBridge.R61b

namespace Alignment.Shadows.MessagePassingBridge.ebcmMpRoundtrip

/-! Blind text: "Round-trip MP → EBCM → MP is the identity." -/

@[sa_reference "MessagePassingBridge.ebcmMpRoundtrip"]
def T : Prop := ∀ m : MPState, ebcmToMP (mpToEBCM m) = m

/-- S1: for every MP state, MP → EBCM → MP returns it. -/
@[sa_shadow "MessagePassingBridge.ebcmMpRoundtrip" 1]
def S1 : Prop := ∀ m : MPState, ebcmToMP (mpToEBCM m) = m

@[sa_ref_forward "MessagePassingBridge.ebcmMpRoundtrip" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MessagePassingBridge.ebcmMpRoundtrip"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MessagePassingBridge.ebcmMpRoundtrip

namespace Alignment.Shadows.MessagePassingBridge.R62d

/-! Blind text: "For the algebraic content: given S = ψ(Θ) and ψ' = mean degree derivative at Θ, the
edge-level [SI] relates to node-level I via the chain rule: dS/dt = ψ'(Θ)·dΘ/dt = -β·[SI]."

-- AMBIGUITY: the text gives no explicit link between [SI] and Θ; read with the message relation
-- of the same result (Sherborne et al. Eq. 18 with [S] = ψ(H₁), H₁ = Θ): dΘ/dt = -β·[SI]/ψ'(Θ).
-- (An EBCM-style link [SI] = ψ'(Θ)·φ_I, dΘ/dt = -β·φ_I is not in the text and not shadowed.)
-- AMBIGUITY: "For the algebraic content" read as the rational identity of the second equality
-- (S1, over ℚ like all library quantities); "via the chain rule: dS/dt = ψ'(Θ)·dΘ/dt" read as the
-- analytic chain rule for S = ψ ∘ Θ (S2, over ℝ, `HasDerivAt`). Both readings are required.
-- ψ ranges over all functions differentiable at Θ(t) (no PGF property is used). -/

@[sa_reference "MessagePassingBridge.R62d"]
def T : Prop :=
  (∀ (β dψ dΘ SI : ℚ), dψ ≠ 0 → dΘ = -β * SI / dψ → dψ * dΘ = -β * SI) ∧
  (∀ (ψ Θ : ℝ → ℝ) (t dψ dΘ : ℝ),
    HasDerivAt ψ dψ (Θ t) → HasDerivAt Θ dΘ t → HasDerivAt (fun s => ψ (Θ s)) (dψ * dΘ) t)

/-- S1 (algebraic content): if dΘ/dt = -β·[SI]/ψ'(Θ) (ψ'(Θ) ≠ 0), then ψ'(Θ)·dΘ/dt = -β·[SI]. -/
@[sa_shadow "MessagePassingBridge.R62d" 1]
def S1 : Prop := ∀ (β dψ dΘ SI : ℚ), dψ ≠ 0 → dΘ = -β * SI / dψ → dψ * dΘ = -β * SI

/-- S2 (chain rule): for S(t) = ψ(Θ(t)), dS/dt = ψ'(Θ(t))·dΘ/dt. -/
@[sa_shadow "MessagePassingBridge.R62d" 2]
def S2 : Prop :=
  ∀ (ψ Θ : ℝ → ℝ) (t dψ dΘ : ℝ),
    HasDerivAt ψ dψ (Θ t) → HasDerivAt Θ dΘ t → HasDerivAt (fun s => ψ (Θ s)) (dψ * dΘ) t

@[sa_ref_forward "MessagePassingBridge.R62d" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MessagePassingBridge.R62d" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "MessagePassingBridge.R62d"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MessagePassingBridge.R62d

namespace Alignment.Shadows.MessagePassingBridge.R63d

open MeasureTheory

/-! Blind text: "We verify: T = β/(β+γ) is the Markovian transmissibility."

T is `SIRParams.transmissibility`.
-- AMBIGUITY: read as two requirements: (S1) T equals β/(β+γ); (S2) T "is the Markovian
-- transmissibility", i.e. equals ∫₀^∞ f(a) da for the Markovian kernels, f(a) = τ(a)·ξ_q(a) with
-- τ(a) = β·exp(-βa) and ξ_q(a) = exp(-γa).
-- VOCAB-GAP: the integral over ages is not expressible with the DataTypes; stated with the
-- Bochner integral over `Set.Ioi 0` and real casts. -/

@[sa_reference "MessagePassingBridge.R63d"]
def T : Prop :=
  (∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)) ∧
  (∀ p : SIRParams,
    ∫ a in Set.Ioi (0 : ℝ), ((p.β : ℝ) * Real.exp (-(p.β : ℝ) * a)) * Real.exp (-(p.γ : ℝ) * a) =
      ((p.transmissibility : ℚ) : ℝ))

/-- S1: T = β/(β+γ). -/
@[sa_shadow "MessagePassingBridge.R63d" 1]
def S1 : Prop := ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ)

/-- S2: T is the Markovian transmissibility ∫₀^∞ β·e^{-βa}·e^{-γa} da. -/
@[sa_shadow "MessagePassingBridge.R63d" 2]
def S2 : Prop :=
  ∀ p : SIRParams,
    ∫ a in Set.Ioi (0 : ℝ), ((p.β : ℝ) * Real.exp (-(p.β : ℝ) * a)) * Real.exp (-(p.γ : ℝ) * a) =
      ((p.transmissibility : ℚ) : ℝ)

@[sa_ref_forward "MessagePassingBridge.R63d" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MessagePassingBridge.R63d" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "MessagePassingBridge.R63d"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MessagePassingBridge.R63d

namespace Alignment.Shadows.MessagePassingBridge.markovEbcmDim

/-! Blind text: "The Markovian EBCM dimension: 3 core variables (Θ, p_I, p_S) plus 2 output variables
(S, I)."

The Markovian EBCM is `ModelFamily.ebcmODE` ("Markovian EBCM: Volz's 3-variable ODE"), its
dimension `effectiveDim`.
-- AMBIGUITY: "dimension: 3 core ... plus 2 output" read as total dimension 3 + 2.
-- VOCAB-GAP: the core count 3 on its own has no counterpart in the DataTypes. -/

@[sa_reference "MessagePassingBridge.markovEbcmDim"]
def T : Prop := ModelFamily.ebcmODE.effectiveDim = 3 + 2

/-- S1: the Markovian EBCM has dimension 3 + 2. -/
@[sa_shadow "MessagePassingBridge.markovEbcmDim" 1]
def S1 : Prop := ModelFamily.ebcmODE.effectiveDim = 3 + 2

@[sa_ref_forward "MessagePassingBridge.markovEbcmDim" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MessagePassingBridge.markovEbcmDim"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MessagePassingBridge.markovEbcmDim

namespace Alignment.Shadows.MessagePassingBridge.pdeToOdeReduction

/-! Blind text: "The non-Markovian EBCM is infinite-dimensional (PDE). Markovian specialization
reduces ∞ → 3 core variables. This is a massive dimensional reduction."

-- VOCAB-GAP: `effectiveDim` is ℕ-valued, so "infinite-dimensional" cannot be stated; "3 core
-- variables" has no counterpart (`effectiveDim` counts core + output); "massive" is not
-- quantified. The checkable part: the Markovian specialisation (`ebcmODE`) has strictly smaller
-- dimension than the non-Markovian EBCM (`ebcmPDE`). -/

@[sa_reference "MessagePassingBridge.pdeToOdeReduction"]
def T : Prop := ModelFamily.ebcmODE.effectiveDim < ModelFamily.ebcmPDE.effectiveDim

/-- S1: the specialisation PDE → ODE strictly reduces the dimension. -/
@[sa_shadow "MessagePassingBridge.pdeToOdeReduction" 1]
def S1 : Prop := ModelFamily.ebcmODE.effectiveDim < ModelFamily.ebcmPDE.effectiveDim

@[sa_ref_forward "MessagePassingBridge.pdeToOdeReduction" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MessagePassingBridge.pdeToOdeReduction"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MessagePassingBridge.pdeToOdeReduction

namespace Alignment.Shadows.MessagePassingBridge.R65

/-! Blind text: "**Result 65.** The dimension tower is monotonically decreasing as we specialize."

"The dimension tower" is the tower of table row 65: MP ≥ EBCM(PDE) ≥ ODE ≥ SIR, dimensions
`effectiveDim`.
-- AMBIGUITY: "monotonically decreasing" read as non-increasing (the tower is written with "≥"; MP
-- and the PDE are both infinite-dimensional, so strictness cannot be intended there). The tower is
-- the four listed levels; a reading along all six hierarchy levels (including DSA and pairwise)
-- is not shadowed, since the text names "the dimension tower". -/

@[sa_reference "MessagePassingBridge.R65"]
def T : Prop :=
  ModelFamily.ebcmPDE.effectiveDim ≤ ModelFamily.messagePassing.effectiveDim ∧
  ModelFamily.ebcmODE.effectiveDim ≤ ModelFamily.ebcmPDE.effectiveDim ∧
  ModelFamily.massAction.effectiveDim ≤ ModelFamily.ebcmODE.effectiveDim

/-- S1: MP → EBCM PDE does not increase the dimension. -/
@[sa_shadow "MessagePassingBridge.R65" 1]
def S1 : Prop := ModelFamily.ebcmPDE.effectiveDim ≤ ModelFamily.messagePassing.effectiveDim

/-- S2: EBCM PDE → EBCM ODE does not increase the dimension. -/
@[sa_shadow "MessagePassingBridge.R65" 2]
def S2 : Prop := ModelFamily.ebcmODE.effectiveDim ≤ ModelFamily.ebcmPDE.effectiveDim

/-- S3: EBCM ODE → mass-action SIR does not increase the dimension. -/
@[sa_shadow "MessagePassingBridge.R65" 3]
def S3 : Prop := ModelFamily.massAction.effectiveDim ≤ ModelFamily.ebcmODE.effectiveDim

@[sa_ref_forward "MessagePassingBridge.R65" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MessagePassingBridge.R65" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MessagePassingBridge.R65" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2

@[sa_complete "MessagePassingBridge.R65"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.MessagePassingBridge.R65

namespace Alignment.Shadows.MessagePassingBridge.R66a

open Alignment.Shadows.MessagePassingBridge.Common

/-! Blind text: "**Result 66.** The [SI] bridge connects MP/EBCM to pairwise."

-- AMBIGUITY: as table.R66: [SI], defined from the MP message / EBCM edge probability H₁ = Θ via
-- Sherborne et al. Eq. 18, makes S = ψ(H₁) obey the pairwise equation dS/dt = -β·[SI].
-- VOCAB-GAP: no pairwise dynamics in the DataTypes; stated with `HasDerivAt`. -/

@[sa_reference "MessagePassingBridge.R66a"]
def T : Prop := PairwiseFromMessage

/-- S1: with Eq. 18, S(t) = ψ(H₁(t)) satisfies dS/dt = -β·[SI]. -/
@[sa_shadow "MessagePassingBridge.R66a" 1]
def S1 : Prop :=
  ∀ (ψ H SI : ℝ → ℝ) (β t dψ : ℝ),
    HasDerivAt ψ dψ (H t) → dψ ≠ 0 →
    HasDerivAt H (-β * SI t / dψ) t →
    HasDerivAt (fun s => ψ (H s)) (-β * SI t) t

@[sa_ref_forward "MessagePassingBridge.R66a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MessagePassingBridge.R66a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MessagePassingBridge.R66a

namespace Alignment.Shadows.MessagePassingBridge.R67

/-! Blind text: "**Result 67.** Pairwise requires PT; MP/EBCM do not. The number of additional
assumptions for pairwise beyond EBCM ODE."

-- AMBIGUITY: "EBCM" read as both EBCM families (PDE and ODE), as for table.R67.
-- AMBIGUITY: "The number of additional assumptions for pairwise beyond EBCM ODE" states no value;
-- read as presupposing that there are additional assumptions, i.e. pairwise requires strictly
-- more assumptions (count) than the EBCM ODE (S5). -/

@[sa_reference "MessagePassingBridge.R67"]
def T : Prop :=
  Assumption.poissonType ∈ ModelFamily.pairwise.requiredAssumptions ∧
  Assumption.poissonType ∉ ModelFamily.messagePassing.requiredAssumptions ∧
  Assumption.poissonType ∉ ModelFamily.ebcmPDE.requiredAssumptions ∧
  Assumption.poissonType ∉ ModelFamily.ebcmODE.requiredAssumptions ∧
  ModelFamily.ebcmODE.requiredAssumptions.length < ModelFamily.pairwise.requiredAssumptions.length

/-- S1: pairwise requires PT. -/
@[sa_shadow "MessagePassingBridge.R67" 1]
def S1 : Prop := Assumption.poissonType ∈ ModelFamily.pairwise.requiredAssumptions

/-- S2: MP does not require PT. -/
@[sa_shadow "MessagePassingBridge.R67" 2]
def S2 : Prop := Assumption.poissonType ∉ ModelFamily.messagePassing.requiredAssumptions

/-- S3: the EBCM PDE does not require PT. -/
@[sa_shadow "MessagePassingBridge.R67" 3]
def S3 : Prop := Assumption.poissonType ∉ ModelFamily.ebcmPDE.requiredAssumptions

/-- S4: the EBCM ODE does not require PT. -/
@[sa_shadow "MessagePassingBridge.R67" 4]
def S4 : Prop := Assumption.poissonType ∉ ModelFamily.ebcmODE.requiredAssumptions

/-- S5: pairwise has additional assumptions beyond the EBCM ODE (strictly more). -/
@[sa_shadow "MessagePassingBridge.R67" 5]
def S5 : Prop :=
  ModelFamily.ebcmODE.requiredAssumptions.length < ModelFamily.pairwise.requiredAssumptions.length

@[sa_ref_forward "MessagePassingBridge.R67" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "MessagePassingBridge.R67" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2.1

@[sa_ref_forward "MessagePassingBridge.R67" 3]
theorem ref_fwd3 : T → S3 := fun t => t.2.2.1

@[sa_ref_forward "MessagePassingBridge.R67" 4]
theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1

@[sa_ref_forward "MessagePassingBridge.R67" 5]
theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2

@[sa_complete "MessagePassingBridge.R67"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.MessagePassingBridge.R67

/-! ### `MessagePassingBridge.R68a` — not shadowed

Blind text: "**Result 68.** Under full Markov + Poisson assumptions, ALL six models in the hierarchy
produce identical trajectories."

VOCAB-GAP: identical trajectories of the six model families cannot be stated: the library has no
dynamics and the text does not define the six systems. The only vocabulary-level surrogate ("every
model is exact, i.e. all its required assumptions hold, under full Markov + Poisson") is a
tautology: with Markov transmission and recovery, Poisson degree (hence PT) and the ambient
configuration-model setting, all five `Assumption` constructors hold, so the surrogate holds for
any `requiredAssumptions`. A tautological shadow is not falsifiable, so no shadow set is given. -/

namespace Alignment.Shadows.MessagePassingBridge.poissonMarkovR0Agree

/-! Blind text: "For Poisson networks with Markov dynamics, the EBCM R₀ equals the mass-action R₀.
This follows from Result 4 in EpiCategory."

EBCM model: `edgeModel p ψ`; mass-action (node-based) model: `nodeModel p κ`; Poisson network with
mean degree κ: `PGFData.poisson κ hκ`; Markov dynamics: rates `p : SIRParams`.
-- AMBIGUITY: the mass-action model is taken with the same mean degree κ as the Poisson network.
-- "This follows from Result 4 in EpiCategory" is a citation (proof route), not checkable. -/

@[sa_reference "MessagePassingBridge.poissonMarkovR0Agree"]
def T : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
    (edgeModel p (PGFData.poisson κ hκ)).R0 = (nodeModel p κ).R0

/-- S1: for all rates and all mean degrees κ > 0, EBCM R₀ on the Poisson network = mass-action R₀. -/
@[sa_shadow "MessagePassingBridge.poissonMarkovR0Agree" 1]
def S1 : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (hκ : 0 < κ),
    (edgeModel p (PGFData.poisson κ hκ)).R0 = (nodeModel p κ).R0

@[sa_ref_forward "MessagePassingBridge.poissonMarkovR0Agree" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "MessagePassingBridge.poissonMarkovR0Agree"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MessagePassingBridge.poissonMarkovR0Agree

noncomputable section

/-! ## Shared notions for the re-authored MessagePassingBridge blocks (blind)

Not registered; inlined by the audit. The library has no model dynamics, so the Poisson EBCM and
classical SIR are written in primitive terms (Rempała 2023, `papers/2310.13866v1.md`): per-edge
rates β̃ = `p.β`, γ̃ = `p.γ` (an `SIRParams`), mean degree κ; `θ̇ = −β̃θ + β̃e^{κ(θ−1)} + γ̃(1−θ)`,
`S = e^{κ(θ−1)}`, `φ_I = −θ̇/β̃`; classical SIR `Ṡ = −βSI`, `İ = βSI − γI`; network recovery
`Ṙ = γ̃(1 − S − R)`. -/
namespace Alignment.Shadows.MessagePassingBridge.Shared2

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

/-- Mass action matches S(t) after reparametrisation, with I := φ_I. -/
def SMatch : Prop :=
  ∀ (p : SIRParams) (κ : ℚ) (θ : ℝ → ℝ), 0 < κ → (∀ t, HasDerivAt θ (ebcmRHS p κ (θ t)) t) →
    IsSIR ((κ : ℝ) * p.β) ((p.β : ℝ) + p.γ) (fun t => Sof κ (θ t)) (fun t => phiI p κ (θ t))

/-- The mass-action infected curve φ_I is not the network prevalence (for some solution). -/
def IDiffer : Prop :=
  ∃ (p : SIRParams) (κ : ℚ) (θ R : ℝ → ℝ) (t : ℝ), 0 < κ ∧
    (∀ s, HasDerivAt θ (ebcmRHS p κ (θ s)) s) ∧
    (∀ s, HasDerivAt R ((p.γ : ℝ) * (1 - Sof κ (θ s) - R s)) s) ∧
    phiI p κ (θ t) ≠ 1 - Sof κ (θ t) - R t

end Alignment.Shadows.MessagePassingBridge.Shared2

/-! ## `MessagePassingBridge.R64` (re-authored blind)

Text: "**Result 64.** Every model family requires at most as many listed assumptions as mass action
(a comparison of list lengths only). The lists are not nested: pairwise needs `poissonType`, mass
action `poissonDegree` instead."

-- AMBIGUITY: "instead" read as: `poissonType` is required by pairwise but not by mass action,
and mass action requires `poissonDegree`; "not nested" as: the pairwise list is not contained in
the mass-action list. -/
namespace Alignment.Shadows.MessagePassingBridge.R64

@[sa_reference "MessagePassingBridge.R64"]
def T : Prop :=
  (∀ m : ModelFamily,
      m.requiredAssumptions.length ≤ ModelFamily.massAction.requiredAssumptions.length) ∧
  Assumption.poissonType ∈ ModelFamily.pairwise.requiredAssumptions ∧
  Assumption.poissonType ∉ ModelFamily.massAction.requiredAssumptions ∧
  Assumption.poissonDegree ∈ ModelFamily.massAction.requiredAssumptions ∧
  ¬ ModelFamily.pairwise.requiredAssumptions ⊆ ModelFamily.massAction.requiredAssumptions

/-- S1: no family requires more listed assumptions than mass action. -/
@[sa_shadow "MessagePassingBridge.R64" 1]
def S1 : Prop :=
  ∀ m : ModelFamily, m.requiredAssumptions.length ≤ ModelFamily.massAction.requiredAssumptions.length
/-- S2: pairwise needs `poissonType`. -/
@[sa_shadow "MessagePassingBridge.R64" 2]
def S2 : Prop := Assumption.poissonType ∈ ModelFamily.pairwise.requiredAssumptions
/-- S3: mass action does not list `poissonType`. -/
@[sa_shadow "MessagePassingBridge.R64" 3]
def S3 : Prop := Assumption.poissonType ∉ ModelFamily.massAction.requiredAssumptions
/-- S4: mass action needs `poissonDegree`. -/
@[sa_shadow "MessagePassingBridge.R64" 4]
def S4 : Prop := Assumption.poissonDegree ∈ ModelFamily.massAction.requiredAssumptions
/-- S5: the pairwise list is not contained in the mass-action list. -/
@[sa_shadow "MessagePassingBridge.R64" 5]
def S5 : Prop :=
  ¬ ModelFamily.pairwise.requiredAssumptions ⊆ ModelFamily.massAction.requiredAssumptions

@[sa_ref_forward "MessagePassingBridge.R64" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MessagePassingBridge.R64" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "MessagePassingBridge.R64" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "MessagePassingBridge.R64" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "MessagePassingBridge.R64" 5] theorem ref_fwd5 : T → S5 := fun t => t.2.2.2.2
@[sa_complete "MessagePassingBridge.R64"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.MessagePassingBridge.R64

/-! ## `MessagePassingBridge.R66e` (re-authored blind)

Text: "The Lean theorem only compares assumption-list lengths: message passing needs fewer listed
assumptions than pairwise."

The first clause describes the Lean statement; the requirement is the strict comparison of list
lengths. -/
namespace Alignment.Shadows.MessagePassingBridge.R66e

@[sa_reference "MessagePassingBridge.R66e"]
def T : Prop :=
  ModelFamily.messagePassing.requiredAssumptions.length <
    ModelFamily.pairwise.requiredAssumptions.length

/-- S1: message passing lists fewer assumptions than pairwise. -/
@[sa_shadow "MessagePassingBridge.R66e" 1]
def S1 : Prop :=
  ModelFamily.messagePassing.requiredAssumptions.length <
    ModelFamily.pairwise.requiredAssumptions.length

@[sa_ref_forward "MessagePassingBridge.R66e" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "MessagePassingBridge.R66e"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MessagePassingBridge.R66e

/-! ## `MessagePassingBridge.R68a` (blind)

Text: "**Result 68.** Under full Markov + Poisson assumptions, MP, EBCM, DSA and pairwise agree. Mass
action matches only S(t), and only after reparametrisation: with per-edge rates β̃, γ̃ and mean degree
κ, the mass-action rates are β = κβ̃ and γ = β̃ + γ̃, and the mass-action I(t) corresponds to φ_I, not
to the network prevalence (Rempała 2023)."

The agreement of MP, EBCM, DSA and pairwise needs model dynamics the library does not define and is
not formalised. S1: along every Poisson EBCM solution, `(S, φ_I)` solves classical SIR with
β = κβ̃, γ = β̃ + γ̃; S2: φ_I is not the network prevalence (for some solution). -/
namespace Alignment.Shadows.MessagePassingBridge.R68a

open Alignment.Shadows.MessagePassingBridge.Shared2

@[sa_reference "MessagePassingBridge.R68a"]
def T : Prop := SMatch ∧ IDiffer

/-- S1: mass action matches S(t) after reparametrisation, with I := φ_I. -/
@[sa_shadow "MessagePassingBridge.R68a" 1]
def S1 : Prop := SMatch
/-- S2: the mass-action I(t) is not the network prevalence. -/
@[sa_shadow "MessagePassingBridge.R68a" 2]
def S2 : Prop := IDiffer

@[sa_ref_forward "MessagePassingBridge.R68a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MessagePassingBridge.R68a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "MessagePassingBridge.R68a"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MessagePassingBridge.R68a

/-! ## `MessagePassingBridge.R68b` (blind)

Text: "This is the maximum-equivalence scenario: * MP ≡ EBCM (always, by Sherborne et al.) *
EBCM ODE = EBCM PDE (Markov collapses PDE → ODE) * EBCM ≡ DSA (always for finite variance, by Kiss
et al.) * DSA ≡ Pairwise (PT closure is exact, by Kiss et al.) * Pairwise → Mass-action SIR
(Poisson: κ = 1; S(t) agrees after reparametrisation, the infected curves differ)"

Formalised: MP ≡ EBCM at the level of the vocabulary (equal transmission kernels `f_mp = f_ebcm`,
and the bridge maps H₁ ↔ Θ are mutually inverse); Poisson: κ = 1 (`closureKappa`); S(t) agrees
after reparametrisation and the infected curves differ (as in R68a). The ODE = PDE, EBCM ≡ DSA and
DSA ≡ pairwise items need model dynamics the library does not define and are not formalised. -/
namespace Alignment.Shadows.MessagePassingBridge.R68b

open Alignment.Shadows.MessagePassingBridge.Shared2

@[sa_reference "MessagePassingBridge.R68b"]
def T : Prop :=
  (∀ e : EpiProcess, e.f_mp = e.f_ebcm) ∧ (∀ s : MPState, ebcmToMP (mpToEBCM s) = s) ∧
  (∀ s : EBCMState, mpToEBCM (ebcmToMP s) = s) ∧
  (∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).closureKappa = 1) ∧ SMatch ∧ IDiffer

/-- S1: MP ≡ EBCM: the transmission kernels agree. -/
@[sa_shadow "MessagePassingBridge.R68b" 1]
def S1 : Prop := ∀ e : EpiProcess, e.f_mp = e.f_ebcm
/-- S2: MP → EBCM → MP is the identity. -/
@[sa_shadow "MessagePassingBridge.R68b" 2]
def S2 : Prop := ∀ s : MPState, ebcmToMP (mpToEBCM s) = s
/-- S3: EBCM → MP → EBCM is the identity. -/
@[sa_shadow "MessagePassingBridge.R68b" 3]
def S3 : Prop := ∀ s : EBCMState, mpToEBCM (ebcmToMP s) = s
/-- S4: Poisson: κ = 1. -/
@[sa_shadow "MessagePassingBridge.R68b" 4]
def S4 : Prop := ∀ (κ : ℚ) (hκ : 0 < κ), (PGFData.poisson κ hκ).closureKappa = 1
/-- S5: S(t) agrees with mass action after reparametrisation. -/
@[sa_shadow "MessagePassingBridge.R68b" 5]
def S5 : Prop := SMatch
/-- S6: the infected curves differ. -/
@[sa_shadow "MessagePassingBridge.R68b" 6]
def S6 : Prop := IDiffer

@[sa_ref_forward "MessagePassingBridge.R68b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MessagePassingBridge.R68b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "MessagePassingBridge.R68b" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "MessagePassingBridge.R68b" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2.1
@[sa_ref_forward "MessagePassingBridge.R68b" 5] theorem ref_fwd5 : T → S5 :=
  fun t => t.2.2.2.2.1
@[sa_ref_forward "MessagePassingBridge.R68b" 6] theorem ref_fwd6 : T → S6 :=
  fun t => t.2.2.2.2.2
@[sa_complete "MessagePassingBridge.R68b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T :=
  ⟨s1, s2, s3, s4, s5, s6⟩

end Alignment.Shadows.MessagePassingBridge.R68b

/-! ## `MessagePassingBridge.table.R64` (re-authored blind)

Text: "| 64 | Assumption-list lengths: none exceeds mass action |" -/
namespace Alignment.Shadows.MessagePassingBridge.table_R64

@[sa_reference "MessagePassingBridge.table.R64"]
def T : Prop :=
  ∀ m : ModelFamily, m.requiredAssumptions.length ≤ ModelFamily.massAction.requiredAssumptions.length

/-- S1: no family's assumption list is longer than mass action's. -/
@[sa_shadow "MessagePassingBridge.table.R64" 1]
def S1 : Prop :=
  ∀ m : ModelFamily, m.requiredAssumptions.length ≤ ModelFamily.massAction.requiredAssumptions.length

@[sa_ref_forward "MessagePassingBridge.table.R64" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "MessagePassingBridge.table.R64"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.MessagePassingBridge.table_R64

/-! ## `MessagePassingBridge.table.R65` (re-authored blind)

Text: "| 65 | Dimension lookup table: SIR(2) ≤ Pairwise(4) ≤ ODE(5) ≤ PDE(∞) |"

Dimensions are `ModelFamily.effectiveDim`; SIR = `massAction`, ODE = `ebcmODE`, PDE = `ebcmPDE`.
PDE(∞) has no value in ℕ; only its place in the chain is required. -/
namespace Alignment.Shadows.MessagePassingBridge.table_R65

@[sa_reference "MessagePassingBridge.table.R65"]
def T : Prop :=
  ModelFamily.massAction.effectiveDim = 2 ∧ ModelFamily.pairwise.effectiveDim = 4 ∧
    ModelFamily.ebcmODE.effectiveDim = 5 ∧
    ModelFamily.massAction.effectiveDim ≤ ModelFamily.pairwise.effectiveDim ∧
    ModelFamily.pairwise.effectiveDim ≤ ModelFamily.ebcmODE.effectiveDim ∧
    ModelFamily.ebcmODE.effectiveDim ≤ ModelFamily.ebcmPDE.effectiveDim

/-- S1: SIR has dimension 2. -/
@[sa_shadow "MessagePassingBridge.table.R65" 1]
def S1 : Prop := ModelFamily.massAction.effectiveDim = 2
/-- S2: pairwise has dimension 4. -/
@[sa_shadow "MessagePassingBridge.table.R65" 2]
def S2 : Prop := ModelFamily.pairwise.effectiveDim = 4
/-- S3: the EBCM ODE has dimension 5. -/
@[sa_shadow "MessagePassingBridge.table.R65" 3]
def S3 : Prop := ModelFamily.ebcmODE.effectiveDim = 5
/-- S4: SIR ≤ pairwise. -/
@[sa_shadow "MessagePassingBridge.table.R65" 4]
def S4 : Prop := ModelFamily.massAction.effectiveDim ≤ ModelFamily.pairwise.effectiveDim
/-- S5: pairwise ≤ ODE. -/
@[sa_shadow "MessagePassingBridge.table.R65" 5]
def S5 : Prop := ModelFamily.pairwise.effectiveDim ≤ ModelFamily.ebcmODE.effectiveDim
/-- S6: ODE ≤ PDE. -/
@[sa_shadow "MessagePassingBridge.table.R65" 6]
def S6 : Prop := ModelFamily.ebcmODE.effectiveDim ≤ ModelFamily.ebcmPDE.effectiveDim

@[sa_ref_forward "MessagePassingBridge.table.R65" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MessagePassingBridge.table.R65" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "MessagePassingBridge.table.R65" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "MessagePassingBridge.table.R65" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2.1
@[sa_ref_forward "MessagePassingBridge.table.R65" 5] theorem ref_fwd5 : T → S5 :=
  fun t => t.2.2.2.2.1
@[sa_ref_forward "MessagePassingBridge.table.R65" 6] theorem ref_fwd6 : T → S6 :=
  fun t => t.2.2.2.2.2
@[sa_complete "MessagePassingBridge.table.R65"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T :=
  ⟨s1, s2, s3, s4, s5, s6⟩

end Alignment.Shadows.MessagePassingBridge.table_R65

/-! ## `MessagePassingBridge.table.R68` (re-authored blind)

Text: "| 68 | Equivalence chain for Markov + Poisson (informal; mass action matches S(t) only) |"

The equivalence chain is marked informal; formalised is the parenthesis: mass action matches S(t)
after reparametrisation (S1), and only S(t): the infected curves differ (S2). -/
namespace Alignment.Shadows.MessagePassingBridge.table_R68

open Alignment.Shadows.MessagePassingBridge.Shared2

@[sa_reference "MessagePassingBridge.table.R68"]
def T : Prop := SMatch ∧ IDiffer

/-- S1: mass action matches S(t). -/
@[sa_shadow "MessagePassingBridge.table.R68" 1]
def S1 : Prop := SMatch
/-- S2: only S(t): the infected curves differ. -/
@[sa_shadow "MessagePassingBridge.table.R68" 2]
def S2 : Prop := IDiffer

@[sa_ref_forward "MessagePassingBridge.table.R68" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "MessagePassingBridge.table.R68" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "MessagePassingBridge.table.R68"] theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.MessagePassingBridge.table_R68

end
