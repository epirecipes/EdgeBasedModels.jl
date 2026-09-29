import Alignment.Registry
import Alignment.Shadows.MessagePassingBridge

/-!
# Checkers: group `MessagePassingBridge`

Written by the checker author (SA-PASS role 3, non-blind). For each claim: the `sa_claim`
registration (verbatim registry text, `impl` list in registry order), structural forward and
backward checkers, and `sa_fail_*` records where the implementation says something different
from the blind shadow.

No bridges are declared: every passing check only needs definitional unfolding of the trusted
definitions that occur in the implementation theorem (`EpiProcess.f_mp`, `ebcmToMP`,
`mpToEBCM`, `SIRParams.transmissibility`).

Policy used for the recorded failures:
* A forward check is recorded as failed when `T̂` does not state `Sᵢ`. This includes the case where
  `Sᵢ` is a closed fact about the hard-coded tables (`requiredAssumptions`, `effectiveDim`)
  that holds by kernel computation alone, while `T̂` is about other entries or is a tautology.
  Passing such a check by pushing `h` through a definitional coincidence of numerals (for
  example `len pairwise ≡ len massAction ≡ 4`) would exploit audit limitation 1. It would not be
  evidence of alignment, so it is not done.
* Transitivity (`Nat.le_trans`), reflexivity (`Nat.le.refl`), `List.Mem` constructors and
  the derivative calculus (`HasDerivAt.comp`) are library content and not structural.
-/

/-! ## Header table rows -/

namespace Alignment.Shadows.MessagePassingBridge.table_R60

sa_claim "MessagePassingBridge.table.R60" group "MessagePassingBridge" required
  text "| 60 | Hazard-density identity: f(a) = f̂(a) |"
  impl hazard_density_identity

@[sa_forward "MessagePassingBridge.table.R60" 1]
theorem fwd1 (h : sa_impl% "MessagePassingBridge.table.R60") : S1 := fun e => h e

@[sa_backward "MessagePassingBridge.table.R60"]
theorem bwd (s1 : S1) : sa_impl% "MessagePassingBridge.table.R60" := fun e => s1 e

end Alignment.Shadows.MessagePassingBridge.table_R60

namespace Alignment.Shadows.MessagePassingBridge.table_R61

sa_claim "MessagePassingBridge.table.R61" group "MessagePassingBridge" required
  text "| 61 | MP ≡ EBCM: message = edge probability |"
  impl mp_ebcm_roundtrip ebcm_mp_roundtrip

/-- The H₁-component of the MP round trip `ebcmToMP (mpToEBCM m) = m` is, by the definition of
`ebcmToMP` (`H₁ := s.Θ`), the statement `(mpToEBCM m).Θ = m.H₁`. -/
@[sa_forward "MessagePassingBridge.table.R61" 1]
theorem fwd1 (h : sa_impl% "MessagePassingBridge.table.R61") : S1 :=
  fun m => congrArg MPState.H₁ (h.2 m)

/-- The Θ-component of the EBCM round trip, by the definition of `mpToEBCM` (`Θ := s.H₁`). -/
@[sa_forward "MessagePassingBridge.table.R61" 2]
theorem fwd2 (h : sa_impl% "MessagePassingBridge.table.R61") : S2 :=
  fun e => congrArg EBCMState.Θ (h.1 e)

@[sa_forward "MessagePassingBridge.table.R61" 3]
theorem fwd3 (h : sa_impl% "MessagePassingBridge.table.R61") : S3 := fun m => h.2 m

@[sa_forward "MessagePassingBridge.table.R61" 4]
theorem fwd4 (h : sa_impl% "MessagePassingBridge.table.R61") : S4 := fun e => h.1 e

@[sa_backward "MessagePassingBridge.table.R61"]
theorem bwd (_s1 : S1) (_s2 : S2) (s3 : S3) (s4 : S4) : sa_impl% "MessagePassingBridge.table.R61" :=
  ⟨fun e => s4 e, fun m => s3 m⟩

end Alignment.Shadows.MessagePassingBridge.table_R61

namespace Alignment.Shadows.MessagePassingBridge.table_R62

sa_claim "MessagePassingBridge.table.R62" group "MessagePassingBridge" required
  text "| 62 | Re-parametrised pairwise from MP |"
  impl chain_rule_bridge

sa_fail_forward "MessagePassingBridge.table.R62" 1 "impl (chain_rule_bridge) is the rational identity psi_prime * (-beta * SI_over_N / psi_prime) = -beta * SI_over_N under psi_prime ≠ 0 and beta ≠ 0: three free numbers in ℚ, with no function ψ, no trajectory H₁(t), no [SI](t) and no derivative. S1 requires the analytic statement over ℝ that S(t) = ψ(H(t)) has HasDerivAt value -β·[SI](t) when H satisfies Eq. 18 (dH/dt = -β·[SI]/ψ'(H)). That is the chain rule HasDerivAt.comp plus the algebra, and the impl supplies only the algebra, over ℚ and with the extra hypothesis β ≠ 0. There is no structural derivation."
sa_fail_backward "MessagePassingBridge.table.R62" "impl is a ℚ-valued algebraic identity for arbitrary psi_prime, SI_over_N, beta. S1 speaks only about real functions and HasDerivAt. Recovering the rational identity from S1 would need explicit differentiable witnesses (e.g. linear ψ, H), uniqueness of derivatives (HasDerivAt.unique) and injectivity of the cast ℚ → ℝ, all library content. The impl is about a different notion (free-scalar algebra, not derivatives)."

end Alignment.Shadows.MessagePassingBridge.table_R62

namespace Alignment.Shadows.MessagePassingBridge.table_R63

sa_claim "MessagePassingBridge.table.R63" group "MessagePassingBridge" required
  text "| 63 | Markovian specialization to Volz ODE |"
  impl markov_transmissibility

sa_fail_forward "MessagePassingBridge.table.R63" 1 "impl (markov_transmissibility) is the definitional identity ∀ p : SIRParams, p.transmissibility = p.β / (p.β + p.γ) (rfl). It never mentions ModelFamily or requiredAssumptions. S1 (markovTransmission ∈ ebcmODE.requiredAssumptions) is a fact about the assumption table that impl does not state. Any proof would ignore h (vacuous), and List.Mem constructors are library content."
sa_fail_forward "MessagePassingBridge.table.R63" 2 "impl is only p.transmissibility = p.β / (p.β + p.γ) (rfl) and says nothing about assumptions. S2 (markovRecovery ∈ ebcmODE.requiredAssumptions) is not stated by impl. Any proof would ignore h (vacuous)."
sa_fail_forward "MessagePassingBridge.table.R63" 3 "impl is only p.transmissibility = p.β / (p.β + p.γ) (rfl). S3 (markovTransmission ∉ ebcmPDE.requiredAssumptions) is a non-membership fact about the assumption table that impl does not mention. A proof would need case analysis on List.Mem (library) and would ignore h."
sa_fail_forward "MessagePassingBridge.table.R63" 4 "impl is only p.transmissibility = p.β / (p.β + p.γ) (rfl). S4 (markovRecovery ∉ ebcmPDE.requiredAssumptions) is not stated by impl. A proof would ignore h."
sa_fail_forward "MessagePassingBridge.table.R63" 5 "impl is only p.transmissibility = p.β / (p.β + p.γ) (rfl). S5 (every ebcmPDE assumption is an ebcmODE assumption, i.e. the ODE is a specialisation of the PDE) is an inclusion of assumption lists that impl does not state. A proof would ignore h."

/-- The implementation is a definitional identity (`transmissibility` unfolds to `β / (β + γ)`),
so it follows from the shadows trivially. -/
@[sa_backward "MessagePassingBridge.table.R63"]
theorem bwd (_s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) (_s5 : S5) :
    sa_impl% "MessagePassingBridge.table.R63" :=
  fun _ => rfl

end Alignment.Shadows.MessagePassingBridge.table_R63

/-! ## table.R64 -/
namespace Alignment.Shadows.MessagePassingBridge.table_R64

sa_claim "MessagePassingBridge.table.R64" group "MessagePassingBridge" required
  text "| 64 | Assumption-list lengths: none exceeds mass action |"
  impl hierarchy_monotone_assumptions

@[sa_forward "MessagePassingBridge.table.R64" 1]
theorem fwd1 (h : sa_impl% "MessagePassingBridge.table.R64") : S1 := fun m => h m

@[sa_backward "MessagePassingBridge.table.R64"]
theorem bwd (s1 : S1) : sa_impl% "MessagePassingBridge.table.R64" := fun m => s1 m

end Alignment.Shadows.MessagePassingBridge.table_R64

/-! ## table.R65 -/
namespace Alignment.Shadows.MessagePassingBridge.table_R65

sa_claim "MessagePassingBridge.table.R65" group "MessagePassingBridge" required
  text "| 65 | Dimension lookup table: SIR(2) ≤ Pairwise(4) ≤ ODE(5) ≤ PDE(∞) |"
  impl dim_tower_monotone

sa_fail_forward "MessagePassingBridge.table.R65" 1 "S1 (massAction.effectiveDim = 2) is a clause of the lookup table ModelFamily.effectiveDim and holds by rfl. impl dim_tower_monotone states only the three inequalities, so a checker could only prove S1 without h (vacuous)."

sa_fail_forward "MessagePassingBridge.table.R65" 2 "S2 (pairwise.effectiveDim = 4) is a clause of the lookup table (rfl). impl states only the inequalities, so a checker could only prove S2 without h (vacuous)."

sa_fail_forward "MessagePassingBridge.table.R65" 3 "S3 (ebcmODE.effectiveDim = 5) is a clause of the lookup table (rfl). impl states only the inequalities, so a checker could only prove S3 without h (vacuous)."

@[sa_forward "MessagePassingBridge.table.R65" 4]
theorem fwd4 (h : sa_impl% "MessagePassingBridge.table.R65") : S4 := h.1

@[sa_forward "MessagePassingBridge.table.R65" 5]
theorem fwd5 (h : sa_impl% "MessagePassingBridge.table.R65") : S5 := h.2.1

@[sa_forward "MessagePassingBridge.table.R65" 6]
theorem fwd6 (h : sa_impl% "MessagePassingBridge.table.R65") : S6 := h.2.2

@[sa_backward "MessagePassingBridge.table.R65"]
theorem bwd (_s1 : S1) (_s2 : S2) (_s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) :
    sa_impl% "MessagePassingBridge.table.R65" :=
  ⟨s4, s5, s6⟩

end Alignment.Shadows.MessagePassingBridge.table_R65

namespace Alignment.Shadows.MessagePassingBridge.table_R66

sa_claim "MessagePassingBridge.table.R66" group "MessagePassingBridge" required
  text "| 66 | The bridge: [SI] connects MP/EBCM to pairwise world |"
  impl bridge_requires_edge_formulation

sa_fail_forward "MessagePassingBridge.table.R66" 1 "impl (bridge_requires_edge_formulation) is the list-length inequality messagePassing.requiredAssumptions.length < pairwise.requiredAssumptions.length (1 < 4). It says nothing about [SI], the message H₁, ψ or derivatives. S1 requires that [SI], through Eq. 18, makes S = ψ(H₁) satisfy dS/dt = -β·[SI] (HasDerivAt over ℝ). That is a different notion and not implied."
sa_fail_backward "MessagePassingBridge.table.R66" "impl is a closed count inequality between MP's and pairwise's assumption lists (1 < 4). S1 is an analytic statement about real functions and HasDerivAt and says nothing about requiredAssumptions. impl does not follow from S1, and a proof of the closed Nat.lt would need Nat.le constructors (library) independently of S1."

end Alignment.Shadows.MessagePassingBridge.table_R66

namespace Alignment.Shadows.MessagePassingBridge.table_R67

sa_claim "MessagePassingBridge.table.R67" group "MessagePassingBridge" required
  text "| 67 | Pairwise requires PT; MP/EBCM do not |"
  impl pairwise_needs_more_than_ebcm

sa_fail_forward "MessagePassingBridge.table.R67" 1 "impl (pairwise_needs_more_than_ebcm) is the count inequality ebcmODE.requiredAssumptions.length < pairwise.requiredAssumptions.length (3 < 4). It does not say which assumption is extra. S1 (poissonType ∈ pairwise.requiredAssumptions, 'Pairwise requires PT') is not implied by a count."
sa_fail_forward "MessagePassingBridge.table.R67" 2 "impl compares only the list lengths of ebcmODE and pairwise and never mentions messagePassing. S2 (poissonType ∉ messagePassing.requiredAssumptions, 'MP ... do not') is not stated by impl."
sa_fail_forward "MessagePassingBridge.table.R67" 3 "impl compares only the list lengths of ebcmODE and pairwise and never mentions ebcmPDE. S3 (poissonType ∉ ebcmPDE.requiredAssumptions) is not stated by impl."
sa_fail_forward "MessagePassingBridge.table.R67" 4 "impl is a count inequality (3 < 4). S4 (poissonType ∉ ebcmODE.requiredAssumptions) is a non-membership fact that a count cannot imply: a shorter list may still contain poissonType."
sa_fail_backward "MessagePassingBridge.table.R67" "impl is len ebcmODE < len pairwise (a count). The shadows are membership and non-membership facts about poissonType. poissonType ∈ pairwise ∧ poissonType ∉ ebcmODE does not imply len ebcmODE < len pairwise (e.g. [configModel, markovTransmission] vs [poissonType]). impl is a different notion and not derivable from S1…S4."

end Alignment.Shadows.MessagePassingBridge.table_R67

/-! ## table.R68 -/
namespace Alignment.Shadows.MessagePassingBridge.table_R68

sa_claim "MessagePassingBridge.table.R68" group "MessagePassingBridge" required
  text "| 68 | Equivalence chain for Markov + Poisson (informal; mass action matches S(t) only) |"
  impl full_equivalence_poisson

sa_fail_forward "MessagePassingBridge.table.R68" 1 "impl full_equivalence_poisson is the reflexivity massAction.requiredAssumptions.length = massAction.requiredAssumptions.length (proved by rfl). It says nothing about the mass-action and EBCM trajectories, so it does not give S1 (after β = κβ̃, γ = β̃ + γ̃, the mass-action S(t) matches the network S(t))."

sa_fail_forward "MessagePassingBridge.table.R68" 2 "impl is a reflexivity about list lengths. S2 (the mass-action I(t) is not the network prevalence) is a statement about solutions of two ODE systems, which impl does not mention."

sa_fail_backward "MessagePassingBridge.table.R68" "impl (x = x) is provable by rfl without the shadows, so a backward checker could only be vacuous. impl carries none of the row's content (the row itself says the equivalence chain is informal)."

end Alignment.Shadows.MessagePassingBridge.table_R68

/-! ## R64 -/
namespace Alignment.Shadows.MessagePassingBridge.R64

sa_claim "MessagePassingBridge.R64" group "MessagePassingBridge" required
  text "**Result 64.** Every model family requires at most as many listed assumptions as mass action (a comparison of list lengths only). The lists are not nested: pairwise needs `poissonType`, mass action `poissonDegree` instead."
  impl hierarchy_monotone_assumptions

@[sa_forward "MessagePassingBridge.R64" 1]
theorem fwd1 (h : sa_impl% "MessagePassingBridge.R64") : S1 := fun m => h m

sa_fail_forward "MessagePassingBridge.R64" 2 "impl hierarchy_monotone_assumptions compares list lengths only. S2 (poissonType ∈ pairwise.requiredAssumptions) is a closed fact about the list contents that impl does not state. A checker could prove it only without h, and List.Mem constructors are core-library proofs, not structural."

sa_fail_forward "MessagePassingBridge.R64" 3 "S3 (poissonType ∉ massAction.requiredAssumptions) is a closed fact about list contents. impl, a length comparison, does not state it."

sa_fail_forward "MessagePassingBridge.R64" 4 "S4 (poissonDegree ∈ massAction.requiredAssumptions) is a closed fact about list contents. impl, a length comparison, does not state it."

sa_fail_forward "MessagePassingBridge.R64" 5 "S5 (the pairwise list is not contained in the mass-action list: 'The lists are not nested') is not stated by impl, which compares lengths only; the text itself says so ('a comparison of list lengths only')."

@[sa_backward "MessagePassingBridge.R64"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) (_s5 : S5) :
    sa_impl% "MessagePassingBridge.R64" := fun m => s1 m

end Alignment.Shadows.MessagePassingBridge.R64

namespace Alignment.Shadows.MessagePassingBridge.R60

sa_claim "MessagePassingBridge.R60" group "MessagePassingBridge" required
  text "**Result 60.** The hazard-density identity: f(a) = f̂(a). [...] f(a) = τ(a)·ξ_q(a) = ζ(a)·ξ_τ(a)·ξ_q(a) = f̂(a)"
  impl hazard_density_identity

@[sa_forward "MessagePassingBridge.R60" 1]
theorem fwd1 (h : sa_impl% "MessagePassingBridge.R60") : S1 := fun e => h e
sa_fail_forward "MessagePassingBridge.R60" 2 "impl (hazard_density_identity) states only f_mp = f_ebcm. S2 (f_mp = (ζ·ξ_τ)·ξ_q, the text's first link f(a) = τ(a)·ξ_q(a) = ζ(a)·ξ_τ(a)·ξ_q(a)) is not a consequence of that equation. It holds only by unfolding the definition EpiProcess.f_mp := ζ * ξ_τ * ξ_q, so any proof ignores h (vacuous). The substantive step τ(a) = ζ(a)·ξ_τ(a) has no counterpart in impl (τ is not a field of EpiProcess); it is built into the definition."
/-- `ζ·ξ_τ·ξ_q` is the definition of `f_mp`, so the implementation (associativity) is `S3`. -/
@[sa_forward "MessagePassingBridge.R60" 3]
theorem fwd3 (h : sa_impl% "MessagePassingBridge.R60") : S3 := fun e => h e

@[sa_backward "MessagePassingBridge.R60"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "MessagePassingBridge.R60" := fun e => s1 e

end Alignment.Shadows.MessagePassingBridge.R60

namespace Alignment.Shadows.MessagePassingBridge.R61a

sa_claim "MessagePassingBridge.R61a" group "MessagePassingBridge" required
  text "**Result 61.** The MP ↔ EBCM bridge is an isomorphism."
  impl mp_ebcm_roundtrip ebcm_mp_roundtrip

@[sa_forward "MessagePassingBridge.R61a" 1]
theorem fwd1 (h : sa_impl% "MessagePassingBridge.R61a") : S1 := fun m => h.2 m

@[sa_forward "MessagePassingBridge.R61a" 2]
theorem fwd2 (h : sa_impl% "MessagePassingBridge.R61a") : S2 := fun e => h.1 e

@[sa_backward "MessagePassingBridge.R61a"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "MessagePassingBridge.R61a" :=
  ⟨fun e => s2 e, fun m => s1 m⟩

end Alignment.Shadows.MessagePassingBridge.R61a

namespace Alignment.Shadows.MessagePassingBridge.R61b

sa_claim "MessagePassingBridge.R61b" group "MessagePassingBridge" required
  text "Round-trip EBCM → MP → EBCM is the identity."
  impl mp_ebcm_roundtrip

@[sa_forward "MessagePassingBridge.R61b" 1]
theorem fwd1 (h : sa_impl% "MessagePassingBridge.R61b") : S1 := fun e => h e

@[sa_backward "MessagePassingBridge.R61b"]
theorem bwd (s1 : S1) : sa_impl% "MessagePassingBridge.R61b" := fun e => s1 e

end Alignment.Shadows.MessagePassingBridge.R61b

namespace Alignment.Shadows.MessagePassingBridge.ebcmMpRoundtrip

sa_claim "MessagePassingBridge.ebcmMpRoundtrip" group "MessagePassingBridge" required
  text "Round-trip MP → EBCM → MP is the identity."
  impl ebcm_mp_roundtrip

@[sa_forward "MessagePassingBridge.ebcmMpRoundtrip" 1]
theorem fwd1 (h : sa_impl% "MessagePassingBridge.ebcmMpRoundtrip") : S1 := fun m => h m

@[sa_backward "MessagePassingBridge.ebcmMpRoundtrip"]
theorem bwd (s1 : S1) : sa_impl% "MessagePassingBridge.ebcmMpRoundtrip" := fun m => s1 m

end Alignment.Shadows.MessagePassingBridge.ebcmMpRoundtrip

namespace Alignment.Shadows.MessagePassingBridge.R62d

sa_claim "MessagePassingBridge.R62d" group "MessagePassingBridge" required
  text "For the algebraic content: given S = ψ(Θ) and ψ' = mean degree derivative at Θ, the edge-level [SI] relates to node-level I via the chain rule: dS/dt = ψ'(Θ)·dΘ/dt = -β·[SI]."
  impl chain_rule_bridge

sa_fail_forward "MessagePassingBridge.R62d" 1 "impl (chain_rule_bridge) has the extra hypothesis hbeta : beta ≠ 0. S1 (∀ β dψ dΘ SI : ℚ, dψ ≠ 0 → dΘ = -β·SI/dψ → dψ·dΘ = -β·SI) has none, and the text 'dS/dt = ψ'(Θ)·dΘ/dt = -β·[SI]' needs none. After rewriting dΘ, h closes S1 only when β ≠ 0. The case β = 0 is not covered by impl, and a case split on β = 0 (Classical/Decidable) is not structural."
sa_fail_forward "MessagePassingBridge.R62d" 2 "impl is a ℚ-algebraic identity for three free numbers psi_prime, SI_over_N, beta, with no function ψ or Θ and no derivative. S2 is the analytic chain rule over ℝ (HasDerivAt ψ dψ (Θ t) → HasDerivAt Θ dΘ t → HasDerivAt (ψ ∘ Θ) (dψ·dΘ) t), i.e. Mathlib's HasDerivAt.comp. impl does not contain it: the text's 'via the chain rule' step is absent from the implementation, which assumes dS/dt = ψ'·dΘ/dt by writing it into the expression."

/-- Instantiate `S1` with `dΘ := -β·SI/ψ'`; the rewriting hypothesis is `rfl`. -/
@[sa_backward "MessagePassingBridge.R62d"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "MessagePassingBridge.R62d" := by
  intro psi_prime SI_over_N beta hpsi _hbeta
  exact s1 beta psi_prime (-beta * SI_over_N / psi_prime) SI_over_N hpsi rfl

end Alignment.Shadows.MessagePassingBridge.R62d

namespace Alignment.Shadows.MessagePassingBridge.R63d

sa_claim "MessagePassingBridge.R63d" group "MessagePassingBridge" required
  text "We verify: T = β/(β+γ) is the Markovian transmissibility."
  impl markov_transmissibility

@[sa_forward "MessagePassingBridge.R63d" 1]
theorem fwd1 (h : sa_impl% "MessagePassingBridge.R63d") : S1 := fun p => h p
sa_fail_forward "MessagePassingBridge.R63d" 2 "impl (markov_transmissibility) is the definitional identity p.transmissibility = p.β / (p.β + p.γ) (rfl). 'Markovian' is connected to no distribution or integral. S2 (∫₀^∞ β·e^{-βa}·e^{-γa} da = transmissibility, cast to ℝ) is the substantive content of 'is the Markovian transmissibility'. It needs an improper-integral computation (integral_exp_neg_Ioi etc., library content) that impl does not provide."

@[sa_backward "MessagePassingBridge.R63d"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "MessagePassingBridge.R63d" := fun p => s1 p

end Alignment.Shadows.MessagePassingBridge.R63d

namespace Alignment.Shadows.MessagePassingBridge.markovEbcmDim

sa_claim "MessagePassingBridge.markovEbcmDim" group "MessagePassingBridge" required
  text "The Markovian EBCM dimension: 3 core variables (Θ, p_I, p_S) plus 2 output variables (S, I)."
  impl markov_ebcm_dim

sa_fail_forward "MessagePassingBridge.markovEbcmDim" 1 "impl (markov_ebcm_dim) is the closed numeral tautology (3 : ℕ) + 2 = 5 (rfl). No model or variable occurs in it. S1 (ModelFamily.ebcmODE.effectiveDim = 3 + 2) is about the Markovian EBCM and holds only by the definition of effectiveDim (ebcmODE ↦ 5), which impl does not mention. h.symm would typecheck only by kernel evaluation of effectiveDim, so impl would contribute nothing but the kernel-decidable fact 3 + 2 = 5 (audit limitation 1). This is a tautological impl, so it is not used."

/-- The implementation is a closed numeral identity, true by kernel computation. -/
@[sa_backward "MessagePassingBridge.markovEbcmDim"]
theorem bwd (_s1 : S1) : sa_impl% "MessagePassingBridge.markovEbcmDim" := rfl

end Alignment.Shadows.MessagePassingBridge.markovEbcmDim

namespace Alignment.Shadows.MessagePassingBridge.pdeToOdeReduction

sa_claim "MessagePassingBridge.pdeToOdeReduction" group "MessagePassingBridge" required
  text "The non-Markovian EBCM is infinite-dimensional (PDE). Markovian specialization reduces ∞ → 3 core variables. This is a massive dimensional reduction."
  impl pde_to_ode_reduction

sa_fail_forward "MessagePassingBridge.pdeToOdeReduction" 1 "impl (pde_to_ode_reduction) is the tautology ∀ n : ℕ, 3 ≤ n → n ≤ n (le_refl) and has no content. It mentions neither ModelFamily nor effectiveDim. S1 (ebcmODE.effectiveDim < ebcmPDE.effectiveDim, the Markovian specialisation strictly reduces the dimension) is not implied. Any proof would ignore h (vacuous)."
sa_fail_backward "MessagePassingBridge.pdeToOdeReduction" "impl ∀ n : ℕ, 3 ≤ n → n ≤ n is reflexivity of ≤ on a variable n. Its only proof is Nat.le.refl / le_refl (library constructor/lemma, not in the structural whitelist). It is unrelated to S1 (a strict inequality between two fixed effectiveDim values), which cannot supply n ≤ n for an arbitrary n. impl is a different, contentless statement."

end Alignment.Shadows.MessagePassingBridge.pdeToOdeReduction

namespace Alignment.Shadows.MessagePassingBridge.R65

sa_claim "MessagePassingBridge.R65" group "MessagePassingBridge" required
  text "**Result 65.** The dimension tower is monotonically decreasing as we specialize."
  impl dim_tower_monotone

sa_fail_forward "MessagePassingBridge.R65" 1 "impl (dim_tower_monotone) is massAction ≤ pairwise ∧ pairwise ≤ ebcmODE ∧ ebcmODE ≤ ebcmPDE (effectiveDim) and omits the MP level of the tower. S1 (ebcmPDE.effectiveDim ≤ messagePassing.effectiveDim) is not stated."
@[sa_forward "MessagePassingBridge.R65" 2]
theorem fwd2 (h : sa_impl% "MessagePassingBridge.R65") : S2 := h.2.2
sa_fail_forward "MessagePassingBridge.R65" 3 "impl compares massAction with pairwise and pairwise with ebcmODE. It has no direct comparison of massAction with ebcmODE. S3 (massAction.effectiveDim ≤ ebcmODE.effectiveDim) follows only by transitivity (Nat.le_trans), a library lemma. impl's chain goes through a pairwise level that the text's tower does not contain."
sa_fail_backward "MessagePassingBridge.R65" "impl's first two conjuncts, massAction ≤ pairwise (2 ≤ 4) and pairwise ≤ ebcmODE (4 ≤ 5), involve the pairwise level. The tower of S1…S3 (MP ≥ EBCM(PDE) ≥ ODE ≥ SIR) omits it. Neither conjunct is, up to definitional unfolding, any of S1…S3, so impl states a different chain from the shadows."

end Alignment.Shadows.MessagePassingBridge.R65

namespace Alignment.Shadows.MessagePassingBridge.R66a

sa_claim "MessagePassingBridge.R66a" group "MessagePassingBridge" required
  text "**Result 66.** The [SI] bridge connects MP/EBCM to pairwise."
  impl bridge_requires_edge_formulation

sa_fail_forward "MessagePassingBridge.R66a" 1 "impl (bridge_requires_edge_formulation) is the list-length inequality messagePassing.requiredAssumptions.length < pairwise.requiredAssumptions.length (1 < 4). It says nothing about [SI] or a bridge. S1 requires that [SI], defined from the message H₁ through Eq. 18, makes S = ψ(H₁) satisfy dS/dt = -β·[SI] (HasDerivAt over ℝ). That is a different notion and not implied."
sa_fail_backward "MessagePassingBridge.R66a" "impl is a closed count inequality between MP's and pairwise's assumption lists (1 < 4). S1 is an analytic statement about real functions and derivatives and says nothing about requiredAssumptions. impl does not follow from S1, and a proof of the closed Nat.lt would need Nat.le constructors (library) independently of S1."

end Alignment.Shadows.MessagePassingBridge.R66a

/-! ## R66e -/
namespace Alignment.Shadows.MessagePassingBridge.R66e

sa_claim "MessagePassingBridge.R66e" group "MessagePassingBridge" required
  text "The Lean theorem only compares assumption-list lengths: message passing needs fewer listed assumptions than pairwise."
  impl bridge_requires_edge_formulation

@[sa_forward "MessagePassingBridge.R66e" 1]
theorem fwd1 (h : sa_impl% "MessagePassingBridge.R66e") : S1 := h

@[sa_backward "MessagePassingBridge.R66e"]
theorem bwd (s1 : S1) : sa_impl% "MessagePassingBridge.R66e" := s1

end Alignment.Shadows.MessagePassingBridge.R66e

namespace Alignment.Shadows.MessagePassingBridge.R67

sa_claim "MessagePassingBridge.R67" group "MessagePassingBridge" required
  text "**Result 67.** Pairwise requires PT; MP/EBCM do not. The number of additional assumptions for pairwise beyond EBCM ODE."
  impl pairwise_needs_more_than_ebcm

sa_fail_forward "MessagePassingBridge.R67" 1 "impl (pairwise_needs_more_than_ebcm) is the count inequality len ebcmODE.requiredAssumptions < len pairwise.requiredAssumptions (3 < 4). It does not say which assumption is extra. S1 (poissonType ∈ pairwise.requiredAssumptions, 'Pairwise requires PT') is not implied by a count."
sa_fail_forward "MessagePassingBridge.R67" 2 "impl mentions only ebcmODE and pairwise. S2 (poissonType ∉ messagePassing.requiredAssumptions, 'MP ... do not') is about MP, which impl does not mention."
sa_fail_forward "MessagePassingBridge.R67" 3 "impl mentions only ebcmODE and pairwise. S3 (poissonType ∉ ebcmPDE.requiredAssumptions) is about the EBCM PDE, which impl does not mention."
sa_fail_forward "MessagePassingBridge.R67" 4 "impl is a count inequality (3 < 4). S4 (poissonType ∉ ebcmODE.requiredAssumptions) is a non-membership fact that a count cannot imply: a shorter list may still contain poissonType."
@[sa_forward "MessagePassingBridge.R67" 5]
theorem fwd5 (h : sa_impl% "MessagePassingBridge.R67") : S5 := h

@[sa_backward "MessagePassingBridge.R67"]
theorem bwd (_s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) (s5 : S5) :
    sa_impl% "MessagePassingBridge.R67" := s5

end Alignment.Shadows.MessagePassingBridge.R67

/-! ## R68a -/
namespace Alignment.Shadows.MessagePassingBridge.R68a

sa_claim "MessagePassingBridge.R68a" group "MessagePassingBridge" required
  text "**Result 68.** Under full Markov + Poisson assumptions, MP, EBCM, DSA and pairwise agree. Mass action matches only S(t), and only after reparametrisation: with per-edge rates β̃, γ̃ and mean degree κ, the mass-action rates are β = κβ̃ and γ = β̃ + γ̃, and the mass-action I(t) corresponds to φ_I, not to the network prevalence (Rempała 2023)."
  impl full_equivalence_poisson

sa_fail_forward "MessagePassingBridge.R68a" 1 "impl full_equivalence_poisson is the reflexivity massAction.requiredAssumptions.length = massAction.requiredAssumptions.length. It says nothing about the mass-action or EBCM trajectories, so it does not give S1 (mass action with β = κβ̃, γ = β̃ + γ̃ matches S(t), with I corresponding to φ_I)."

sa_fail_forward "MessagePassingBridge.R68a" 2 "impl is a reflexivity about list lengths. S2 (the mass-action I(t) is not the network prevalence) is about solutions of the two ODE systems, which impl does not mention."

sa_fail_backward "MessagePassingBridge.R68a" "impl (x = x) is provable by rfl without any shadow, so a backward checker could only be vacuous. impl states none of Result 68's content."

end Alignment.Shadows.MessagePassingBridge.R68a

namespace Alignment.Shadows.MessagePassingBridge.poissonMarkovR0Agree

sa_claim "MessagePassingBridge.poissonMarkovR0Agree" group "MessagePassingBridge" required
  text "For Poisson networks with Markov dynamics, the EBCM R₀ equals the mass-action R₀. This follows from Result 4 in EpiCategory."
  impl poisson_markov_R0_agree

@[sa_forward "MessagePassingBridge.poissonMarkovR0Agree" 1]
theorem fwd1 (h : sa_impl% "MessagePassingBridge.poissonMarkovR0Agree") : S1 :=
  fun p κ hκ => h p κ hκ

@[sa_backward "MessagePassingBridge.poissonMarkovR0Agree"]
theorem bwd (s1 : S1) : sa_impl% "MessagePassingBridge.poissonMarkovR0Agree" :=
  fun p κ hκ => s1 p κ hκ

end Alignment.Shadows.MessagePassingBridge.poissonMarkovR0Agree

/-! ## `MessagePassingBridge.R68b` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.MessagePassingBridge.R68b

sa_claim "MessagePassingBridge.R68b" group "MessagePassingBridge"
  text "This is the maximum-equivalence scenario: * MP ≡ EBCM (always, by Sherborne et al.) * EBCM ODE = EBCM PDE (Markov collapses PDE → ODE) * EBCM ≡ DSA (always for finite variance, by Kiss et al.) * DSA ≡ Pairwise (PT closure is exact, by Kiss et al.) * Pairwise → Mass-action SIR (Poisson: κ = 1; S(t) agrees after reparametrisation, the infected curves differ)"
  impl

end Alignment.Shadows.MessagePassingBridge.R68b
