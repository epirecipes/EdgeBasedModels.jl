import Alignment.Registry
import Alignment.Shadows.Docs
import EBCMCategory.SEIREquations
import EBCMCategory.InvariantRegion

/-!
# Checkers: group `Docs`

Checker author (SA-PASS role 3, non-blind). For every claim of the `Docs` group
(`categorical_foundations.md`, `EBCMCategory/MARGINALISATION_SPEC.md`, README "Lean proofs") with
`status: implemented` this file holds the `sa_claim` registration (verbatim registry text,
registry `impl` list in registry order), the forward checkers `sa_impl% → Sᵢ`, the backward checker
`S₁ → … → Sₙ → sa_impl%`, and `sa_fail_*` records where a check cannot be proved structurally
because the implementation says something different from the shadow.

No bridges are declared. Every passing check needs only definitional unfolding of trusted
definitions (`coarseGrain`, `poissonLift`, `nodeModel`, `edgeModel`, `PGFData.excessDegree`,
`standardEbcmValid`, `ebcmExists`, `DynamicEBCM.staticLimit`, `trajectoryGap`, `algebraicGap`,
`C4ℝ`, …), structure eta for `EpiModel`, and constructor disjointness of plain enumerations
(`NetworkType.noConfusion`). None of the failing checks can be repaired by identifying a trusted
definition with the text's notion: they fail because of quantifier gaps (∃ vs ∀), missing
hypotheses or conclusions, or ℚ/ℝ algebra that no definition carries.

Criterion used for forward checks: `Sᵢ` must follow from what the impl *states* (plus unfolding
of the definitions occurring in `Sᵢ` and the impl). Where a shadow, or a part of it, holds only by
unfolding a trusted definition that no impl mentions, the only structural proof would ignore `h`
(or use it for part of the statement only), and the check is recorded as a failure.
-/

/-! ## `categorical_foundations.md` -/

/-! ### `Docs.cf.thm3_2` -/
namespace Alignment.Shadows.Docs.cf_thm3_2

sa_claim "Docs.cf.thm3_2" group "Docs" required
  text "**Theorem 3.2.** F is not injective on EBCM states: distinct EBCM states (θ, φ, R, ψ) can have the same image (S, I, R), because F forgets φ and all of ψ except its value at θ. Whether distinct EBCM *trajectories* can project to identical node-level trajectories is not established here."
  impl coarseGrain_not_injective

sa_fail_forward "Docs.cf.thm3_2" 1 "impl coarseGrain_not_injective is about the EpiModel records (dimension, R₀): some e₁ ≠ e₂ have coarseGrain e₁ = coarseGrain e₂. S1 is about the map F on EBCM states (θ, φ, R, ψ) ↦ (ψ(θ), 1 − ψ(θ) − R, R), a different map on a different type, which impl does not mention."

@[sa_forward "Docs.cf.thm3_2" 2]
theorem fwd2 (h : sa_impl% "Docs.cf.thm3_2") : S2 := by
  intro hinj
  obtain ⟨e₁, e₂, hne, heq⟩ := h
  exact hne (hinj heq)

sa_fail_backward "Docs.cf.thm3_2" "impl is the constructive existential ∃ e₁ e₂, e₁ ≠ e₂ ∧ coarseGrain e₁ = coarseGrain e₂. S2 is ¬ Function.Injective coarseGrain, and ¬∀ ⇒ ∃¬ needs classical logic (not_forall), which structural proofs forbid. S1 is about a different map. Audit limitation (classical logic) for S2."

end Alignment.Shadows.Docs.cf_thm3_2

/-! ### `Docs.cf.cor4_2-FG` -/

namespace Alignment.Shadows.Docs.cf_cor4_2_FG

sa_claim "Docs.cf.cor4_2-FG" group "Docs" required
  text "F ∘ G = id_Node (coarse-graining the Poisson lift recovers the original)"
  impl counit_dim FG_preserves_R0

/-- `counit_dim` gives the `dim` field (3, which is `(nodeModel p κ).dim` by definition) and
`FG_preserves_R0` the `R0` field of `coarseGrain (poissonLift n)`; `congr` assembles the two
field equalities into an equality of `EpiModel.mk … …` terms, which is the goal by structure eta. -/
@[sa_forward "Docs.cf.cor4_2-FG" 1]
theorem fwd1 (h : sa_impl% "Docs.cf.cor4_2-FG") : S1 :=
  fun p κ => congr (congrArg EpiModel.mk (h.1 (nodeModel p κ))) (h.2 (nodeModel p κ))

/-- As `fwd1`, with the hypothesis `N.dim = 3` supplying the `dim` field. -/
@[sa_forward "Docs.cf.cor4_2-FG" 2]
theorem fwd2 (h : sa_impl% "Docs.cf.cor4_2-FG") : S2 :=
  fun N hN => congr (congrArg EpiModel.mk ((h.1 N).trans hN.symm)) (h.2 N)

/-- Instantiate `S2` at the 3-dimensional model `⟨3, n.R0⟩` and project onto the two fields. -/
@[sa_backward "Docs.cf.cor4_2-FG"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "Docs.cf.cor4_2-FG" := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · have e := congrArg EpiModel.dim (s2 ⟨3, n.R0⟩ rfl)
    exact e
  · have e := congrArg EpiModel.R0 (s2 ⟨3, n.R0⟩ rfl)
    exact e

end Alignment.Shadows.Docs.cf_cor4_2_FG

/-! ### `Docs.cf.cor4_2-GF` -/
namespace Alignment.Shadows.Docs.cf_cor4_2_GF

sa_claim "Docs.cf.cor4_2-GF" group "Docs" required
  text "G ∘ F ≠ id_Edge (projecting then lifting forgets the original PGF)"
  impl GF_ne_id

@[sa_forward "Docs.cf.cor4_2-GF" 1]
theorem fwd1 (h : sa_impl% "Docs.cf.cor4_2-GF") : S1 := by
  obtain ⟨e, he⟩ := h
  exact fun heq => he (congrFun heq e)

sa_fail_forward "Docs.cf.cor4_2-GF" 2 "S2 (G ∘ F keeps only the R₀: records with equal R₀ have equal images) holds by unfolding poissonLift and coarseGrain (both images are ⟨4, R₀⟩; congrArg on R₀). impl GF_ne_id (∃ e, G(F e) ≠ e) does not state it, so a checker could only prove S2 without h (vacuous)."

sa_fail_backward "Docs.cf.cor4_2-GF" "impl is the constructive existential ∃ e, G(F e) ≠ e. S1 (G ∘ F ≠ id) gives a witness only by classical logic (not_forall). S2 does not identify a record that G ∘ F moves, so with S2 the witness's disequality is a closed computation that ignores the shadows (vacuous). Audit limitation (classical logic)."

end Alignment.Shadows.Docs.cf_cor4_2_GF

/-! ### `Docs.cf.cor4_2-GFG` -/

namespace Alignment.Shadows.Docs.cf_cor4_2_GFG

sa_claim "Docs.cf.cor4_2-GFG" group "Docs" required
  text "G ∘ F ∘ G = G (the connection is idempotent)"
  impl G_F_G_eq_G

@[sa_forward "Docs.cf.cor4_2-GFG" 1]
theorem fwd1 (h : sa_impl% "Docs.cf.cor4_2-GFG") : S1 := h

@[sa_forward "Docs.cf.cor4_2-GFG" 2]
theorem fwd2 (h : sa_impl% "Docs.cf.cor4_2-GFG") : S2 := fun p κ => h (nodeModel p κ)

@[sa_forward "Docs.cf.cor4_2-GFG" 3]
theorem fwd3 (h : sa_impl% "Docs.cf.cor4_2-GFG") : S3 := fun N _ => h N

@[sa_backward "Docs.cf.cor4_2-GFG"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "Docs.cf.cor4_2-GFG" := s1

end Alignment.Shadows.Docs.cf_cor4_2_GFG

/-! ### `Docs.cf.cor4_2-FGF` -/

namespace Alignment.Shadows.Docs.cf_cor4_2_FGF

sa_claim "Docs.cf.cor4_2-FGF" group "Docs" required
  text "F ∘ G ∘ F = F (the connection is idempotent)"
  impl F_G_F_eq_F

@[sa_forward "Docs.cf.cor4_2-FGF" 1]
theorem fwd1 (h : sa_impl% "Docs.cf.cor4_2-FGF") : S1 := h

@[sa_forward "Docs.cf.cor4_2-FGF" 2]
theorem fwd2 (h : sa_impl% "Docs.cf.cor4_2-FGF") : S2 := fun p ψ => h (edgeModel p ψ)

@[sa_forward "Docs.cf.cor4_2-FGF" 3]
theorem fwd3 (h : sa_impl% "Docs.cf.cor4_2-FGF") : S3 := fun E _ => h E

@[sa_backward "Docs.cf.cor4_2-FGF"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "Docs.cf.cor4_2-FGF" := s1

end Alignment.Shadows.Docs.cf_cor4_2_FGF

/-! ### `Docs.cf.thm4_3`

`sa_impl%` = `poisson_excess_eq_mean ∧ poisson_variance_eq_mean ∧ poisson_unique_exact_lift ∧
excess_degree_decomposition`. -/
namespace Alignment.Shadows.Docs.cf_thm4_3

sa_claim "Docs.cf.thm4_3" group "Docs" required
  text "**Theorem 4.3.** (a) ψ''(1)/ψ'(1) = ψ'(1) (excess degree equals mean degree) iff the degree distribution has variance equal to its mean. (b) A Poisson degree distribution satisfies (a). (c) The EBCM has mass-action form for S iff ψ' = κψ on [0, 1], i.e. iff the degree distribution is Poisson. (a) does not imply Poisson: ψ(u) = (1 + u²)/2 satisfies (a) and is not Poisson."
  impl PGFData.poisson_excess_eq_mean PGFData.poisson_variance_eq_mean poisson_unique_exact_lift excess_degree_decomposition

sa_fail_forward "Docs.cf.thm4_3" 1 "S1 ((a) →: excess = mean ⇒ variance = mean, for every record) would come from poisson_unique_exact_lift at κ := ψ'(1), but that conjunct takes the hypothesis 0 < κ, i.e. 0 < ψ.mean, which only the data invariant PGFData.mean_pos provides (not structural). The route through excess_degree_decomposition needs field arithmetic (σ²/κ = 1 ⇒ σ² = κ)."

sa_fail_forward "Docs.cf.thm4_3" 2 "S2 ((a) ←: variance = mean ⇒ excess = mean) follows from excess_degree_decomposition (excess = κ − 1 + σ²/κ) only after σ²/κ = κ/κ = 1, which needs div_self with κ ≠ 0 (the data invariant mean_pos) and ring arithmetic. That is not structural."

@[sa_forward "Docs.cf.thm4_3" 3]
theorem fwd3 (h : sa_impl% "Docs.cf.thm4_3") : S3 := fun κ hκ => h.1 κ hκ

sa_fail_forward "Docs.cf.thm4_3" 4 "S4 ((c) mass-action form for S iff ψ′ = κψ on [0,1]) is about real PGFs and the EBCM S-equation. impl consists of rational identities about two-moment records and does not state it; the doc says (c) is not formalised."

sa_fail_forward "Docs.cf.thm4_3" 5 "S5 (ψ′ = κψ on [0,1] with ψ(1) = 1 forces the Poisson PGF) is an ODE uniqueness statement about real functions, which impl does not make."

sa_fail_forward "Docs.cf.thm4_3" 6 "S6 (the Poisson PGF e^{κ(x−1)} satisfies ψ′ = κψ) is a real derivative computation that impl does not state."

sa_fail_forward "Docs.cf.thm4_3" 7 "S7 ((1 + u²)/2 satisfies (a), via real derivatives) is about the real PGF psiMix, which impl does not mention."

sa_fail_forward "Docs.cf.thm4_3" 8 "S8 ((1 + u²)/2 is not a Poisson PGF) is about real functions, which impl does not mention."

sa_fail_backward "Docs.cf.thm4_3" "The shadows give impl's first three conjuncts (S3; S1 at the Poisson record; S1 for poisson_unique_exact_lift). The fourth conjunct, excess_degree_decomposition (ψ''(1)/ψ'(1) = κ − 1 + σ²/κ for every record), is a field identity that no shadow states and that is not structural, so impl is stronger than the shadow set."

end Alignment.Shadows.Docs.cf_thm4_3

/-! ### `Docs.cf.nonMarkovObstruction` (`.pde = .ode` is refuted by `SystemType.noConfusion`) -/
namespace Alignment.Shadows.Docs.cf_nonMarkovObstruction

sa_claim "Docs.cf.nonMarkovObstruction" group "Docs" required
  text "The ODE system must be replaced by integro-differential equations or delay-differential equations. [...] These dynamics are outside the ODE-based **Edge** models, but they are not an obstruction to edge-based modelling: the non-Markovian EBCM is exact for general independent transmission and recovery processes (Sherborne, Miller, Blyuss & Kiss 2018)."
  impl nonmarkov_requires_pde

@[sa_forward "Docs.cf.nonMarkovObstruction" 1]
theorem fwd1 (h : sa_impl% "Docs.cf.nonMarkovObstruction") : S1 :=
  fun hode => SystemType.noConfusion (h.symm.trans hode)

@[sa_forward "Docs.cf.nonMarkovObstruction" 2]
theorem fwd2 (h : sa_impl% "Docs.cf.nonMarkovObstruction") : S2 := h

sa_fail_forward "Docs.cf.nonMarkovObstruction" 3 "S3 (a non-Markovian EBCM exists on configuration models) holds by the definition of ebcmExists (.uniform = .uniform, rfl). impl nonmarkov_requires_pde states only systemRequired = .pde, so a checker could only prove S3 without h (vacuous)."

@[sa_backward "Docs.cf.nonMarkovObstruction"]
theorem bwd (_s1 : S1) (s2 : S2) (_s3 : S3) : sa_impl% "Docs.cf.nonMarkovObstruction" := s2

end Alignment.Shadows.Docs.cf_nonMarkovObstruction

/-! ### `Docs.cf.localisedObstruction` -/

namespace Alignment.Shadows.Docs.cf_localisedObstruction

sa_claim "Docs.cf.localisedObstruction" group "Docs" required
  text "If the initial condition is spatially correlated (e.g., a localised outbreak), the factorisation θ(0) = 1 - ε breaks down for edges near the seed."
  impl localised_genuine_obstruction

/-- The third conjunct of `standardEbcmValid n tr .localised` is `.localised = .uniform`, which is
`ebcmExists n tr .localised` by definition; the impl refutes it. -/
@[sa_forward "Docs.cf.localisedObstruction" 1]
theorem fwd1 (h : sa_impl% "Docs.cf.localisedObstruction") : S1 :=
  fun n tr hv => h n tr hv.2.2

@[sa_forward "Docs.cf.localisedObstruction" 2]
theorem fwd2 (h : sa_impl% "Docs.cf.localisedObstruction") : S2 := h

@[sa_backward "Docs.cf.localisedObstruction"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "Docs.cf.localisedObstruction" := s2

end Alignment.Shadows.Docs.cf_localisedObstruction

/-! ### `Docs.cf.validityDomain`

The backward checker uses S1 for `standard_ebcm_valid`. The two `…_breaks_standard` conjuncts
(the standard predicate fails on clustered and degree-correlated networks), which the text does not
state, hold by `NetworkType.noConfusion` on the network equation, so the backward pass is weak
evidence for them. -/
namespace Alignment.Shadows.Docs.cf_validityDomain

sa_claim "Docs.cf.validityDomain" group "Docs" required
  text "The ODE EBCM is exact for Markovian processes on configuration-model networks with uniform (independent) seeding; the non-Markovian (PDE) EBCM extends this to general independent transmission and recovery processes."
  impl standard_ebcm_valid clustering_breaks_standard degreeCorr_breaks_standard

@[sa_forward "Docs.cf.validityDomain" 1]
theorem fwd1 (h : sa_impl% "Docs.cf.validityDomain") : S1 := h.1

sa_fail_forward "Docs.cf.validityDomain" 2 "S2 (Markovian + uniform needs an ODE system) is a clause of systemRequired (rfl; the trusted theorem markov_is_ode is not in this claim's impl list). impl (standard_ebcm_valid ∧ clustering_breaks_standard ∧ degreeCorr_breaks_standard) does not mention systemRequired, so a checker could only prove S2 without h (vacuous)."

sa_fail_forward "Docs.cf.validityDomain" 3 "S3 (general non-Markovian + uniform needs the PDE system) is a clause of systemRequired (rfl; nonmarkov_requires_pde is not in impl). impl does not mention systemRequired, so a checker could only prove S3 without h (vacuous)."

sa_fail_forward "Docs.cf.validityDomain" 4 "S4 (the non-Markovian EBCM exists on configuration models) holds by the definition of ebcmExists (rfl). impl does not mention ebcmExists, so a checker could only prove S4 without h (vacuous)."

@[sa_backward "Docs.cf.validityDomain"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) : sa_impl% "Docs.cf.validityDomain" :=
  ⟨s1, fun hv => NetworkType.noConfusion hv.1, fun hv => NetworkType.noConfusion hv.1⟩

end Alignment.Shadows.Docs.cf_validityDomain

/-! ### `Docs.cf.thetaNonincreasing` -/

namespace Alignment.Shadows.Docs.cf_thetaNonincreasing

sa_claim "Docs.cf.thetaNonincreasing" group "Docs" required
  text "In the EBCM, θ(t) is non-increasing (edges can only transmit, not \"un-transmit\")."
  impl InvariantRegion.theta_dot_nonpos theta_nonincreasing

sa_fail_forward "Docs.cf.thetaNonincreasing" 1 "impl states two sign conditions on rate expressions over ℚ at a single state: -(p.β * φ_I) ≤ 0 for φ_I ≥ 0 (InvariantRegion.theta_dot_nonpos, EBCMParams) and VMState.dθ s p ≤ 0 for P₁, θ ≥ 0 (theta_nonincreasing, Volz–Meyers). S1 is monotonicity of a real function θ on [0, ∞) given HasDerivAt θ (-(β·φI t)) t with φI ∈ [0,1]; getting AntitoneOn from a derivative sign needs the mean value theorem (e.g. antitoneOn_of_deriv_nonpos) and a ℚ → ℝ transfer, which the impl does not state and which is not structural. The impl says nothing about solutions θ(t)."

sa_fail_backward "Docs.cf.thetaNonincreasing" "S1 is about real functions and their derivatives; the impl conjuncts are ℚ-valued inequalities about EBCMParams (-(β·φ_I) ≤ 0) and VMState (dθ ≤ 0). Obtaining them from S1 would need instantiating S1 at a linear θ, HasDerivAt lemmas and casts ℚ ↔ ℝ (Rat.cast_le): library lemmas, not structural."

end Alignment.Shadows.Docs.cf_thetaNonincreasing

/-! ### `Docs.cf.thm8_1` -/

namespace Alignment.Shadows.Docs.cf_thm8_1

sa_claim "Docs.cf.thm8_1" group "Docs" required
  text "**Theorem 8.1 (Degree-variance inequality).** Let ψ be any valid PGF with mean degree κ. Then: [...] ψ''(1)/ψ'(1) = κ + (σ² - κ)/κ = κ + (σ²/κ - 1) [...] where σ² = Var(degree)."
  impl excess_degree_decomposition

sa_fail_forward "Docs.cf.thm8_1" 1 "impl (excess_degree_decomposition) is ψ.excessDegree = ψ.mean − 1 + ψ.dispersionIndex, i.e. ψ''(1)/κ = κ − 1 + σ²/κ after unfolding excessDegree and dispersionIndex. S1's right-hand side κ + (σ² − κ)/κ equals this only after (σ² − κ)/κ = σ²/κ − 1, which needs κ ≠ 0 (the data invariant ψ.mean_pos) and sub_div/div_self, plus additive re-association over ℚ: library lemmas and a data invariant, not structural. No trusted definition carries this step, so no bridge applies."

sa_fail_forward "Docs.cf.thm8_1" 2 "S2's right-hand side κ + (σ²/κ − 1) differs from the impl's κ − 1 + σ²/κ by additive re-association/commutation over ℚ (add_sub_assoc, add_comm, sub_add_eq_add_sub). This is not definitional (ℚ addition does not reduce on open terms), so it needs library lemmas; no trusted definition can serve as a bridge for it."

sa_fail_backward "Docs.cf.thm8_1" "Deriving the impl's form κ − 1 + σ²/κ from S1 (κ + (σ² − κ)/κ) or S2 (κ + (σ²/κ − 1)) needs the same ℚ re-association (and, for S1, division by κ ≠ 0): library lemmas, not structural."

end Alignment.Shadows.Docs.cf_thm8_1

/-! ### `Docs.cf.thm8_1-poisson` -/
namespace Alignment.Shadows.Docs.cf_thm8_1_poisson

sa_claim "Docs.cf.thm8_1-poisson" group "Docs" required
  text "σ² = κ (e.g. Poisson): excess degree = mean degree; exact equivalence of S(t) with mass action holds for Poisson degrees (Theorem 4.3(c)), not for every law with σ² = κ"
  impl excess_degree_decomposition

sa_fail_forward "Docs.cf.thm8_1-poisson" 1 "impl excess_degree_decomposition gives excess = κ − 1 + σ²/κ. S1 (σ² = κ ⇒ excess = κ) needs, after rewriting σ² = κ, κ − 1 + κ/κ = κ, i.e. div_self with κ ≠ 0 (data invariant mean_pos) and ring arithmetic, which are not structural."

sa_fail_forward "Docs.cf.thm8_1-poisson" 2 "S2 (the Poisson record has σ² = κ) is PGFData.poisson_variance_eq_mean, which is not in this claim's impl list. The decomposition identity does not give it."

sa_fail_forward "Docs.cf.thm8_1-poisson" 3 "S3 (exact equivalence of S(t) with mass action for Poisson degrees) is a statement about ODE solutions, which impl (a rational identity about records) does not make; the text defers it to Theorem 4.3(c), which is not formalised."

sa_fail_forward "Docs.cf.thm8_1-poisson" 4 "S4 ((1 + u²)/2 has σ² = κ, via real derivatives) is about the real PGF psiMix, which impl does not mention."

sa_fail_forward "Docs.cf.thm8_1-poisson" 5 "S5 ((1 + u²)/2 violates ψ′ = κψ somewhere on [0,1]) is about real functions, which impl does not mention."

sa_fail_backward "Docs.cf.thm8_1-poisson" "impl (excess = κ − 1 + σ²/κ for every record) is a field identity. The shadows state it only in the case σ² = κ (S1), and extending to all records needs field arithmetic, so impl does not follow structurally from the shadow set."

end Alignment.Shadows.Docs.cf_thm8_1_poisson

/-! ## `EBCMCategory/MARGINALISATION_SPEC.md` -/

/-! ### `Docs.ms.T1` -/
namespace Alignment.Shadows.Docs.ms_T1

universe u_1 u_2

open EBCMCategory.Marginalisation

sa_claim "Docs.ms.T1" group "Docs" required
  text "theorem dynamic_marginalisation_iff_equivariance (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃} (h₄ : IsFlow F₄ φ₄) (h₃ : IsFlow F₃ φ₃) (uniq₃ : UniqueFlow F₃) : (∀ u, M (F₄ u) = F₃ (M u)) ↔ (∀ u t, M (φ₄ u t) = φ₃ (M u) t) [...] Plain math: for global flows, and unique solutions of `F₃`, along trajectories `M ∘ φ₄(·, t) = φ₃(M ·, t) ↔ RHS commute`."
  impl EBCMCategory.Marginalisation.dynamic_marginalisation_iff_equivariance

@[sa_forward "Docs.ms.T1" 1]
theorem fwd1 (h : sa_impl% "Docs.ms.T1") : S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hu
  exact (h M F₄ F₃ h₄ h₃ hu).mp

@[sa_forward "Docs.ms.T1" 2]
theorem fwd2 (h : sa_impl% "Docs.ms.T1") : S2.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hu
  exact (h M F₄ F₃ h₄ h₃ hu).mpr

@[sa_backward "Docs.ms.T1"]
theorem bwd (s1 : S1.{u_1, u_2}) (s2 : S2.{u_1, u_2}) : sa_impl% "Docs.ms.T1" := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ hu
  exact ⟨s1 M F₄ F₃ φ₄ φ₃ h₄ h₃ hu, s2 M F₄ F₃ φ₄ φ₃ h₄ h₃ hu⟩

/-- Satisfiability witness for the shared hypotheses `IsFlow F₄ φ₄`, `IsFlow F₃ φ₃` and
`UniqueFlow F₃`: the zero fields on `ULift ℝ` and on `PUnit` with constant flows; uniqueness on
`PUnit` holds because all curves into a subsingleton are equal. -/
@[sa_witness "Docs.ms.T1" 1]
theorem witness :
    ∃ (V₄ : Type u_1) (V₃ : Type u_2) (_ : NormedAddCommGroup V₄) (_ : NormedSpace ℝ V₄)
      (_ : NormedAddCommGroup V₃) (_ : NormedSpace ℝ V₃) (_ : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄)
      (F₃ : V₃ → V₃) (φ₄ : V₄ → ℝ → V₄) (φ₃ : V₃ → ℝ → V₃) (_ : IsFlow F₄ φ₄)
      (_ : IsFlow F₃ φ₃) (_ : UniqueFlow F₃), True :=
  ⟨ULift ℝ, PUnit, inferInstance, inferInstance, inferInstance, inferInstance, 0,
    fun _ => 0, fun _ => 0, fun v _ => v, fun v _ => v,
    ⟨fun _ => rfl, fun v t => hasDerivAt_const t v⟩,
    ⟨fun _ => rfl, fun v t => hasDerivAt_const t v⟩,
    fun _ _ _ _ _ => funext fun _ => Subsingleton.elim _ _, trivial⟩

end Alignment.Shadows.Docs.ms_T1

/-! ### `Docs.ms.T2` -/
namespace Alignment.Shadows.Docs.ms_T2

sa_claim "Docs.ms.T2" group "Docs" required
  text "theorem kirkwood_marginalisation_obstruction : ∃ (u4 : Order4Var → ℚ), M_Q (F4_Kirkwood u4) ≠ F3_Kirkwood (M_Q u4) [...] We use a **concrete ℚ-valued surrogate** with mnemonic labels: two order-4 entries (`a = C_4 SISI`, `b = C_4 SSSS` placeholder) and one order-3 entry (`c = P_3 SIS`); `M_Q(a,b) = a + b`; `F4_Kirkwood (a,b) = (a*b, b)`; `F3_Kirkwood c = c^2 / 4`. In Lean the index types are `Idx4 = {a, b}` and `Idx3 = {c}`, not `Order4Var`/`Order3Var`."
  impl MarginalisationObstruction.kirkwood_marginalisation_obstruction

@[sa_forward "Docs.ms.T2" 1]
theorem fwd1 (h : sa_impl% "Docs.ms.T2") : S1 := h

sa_fail_forward "Docs.ms.T2" 2 "S2 (M_Q(a, b) = a + b) is the definition of MarginalisationObstruction.M_witness (rfl). impl kirkwood_marginalisation_obstruction states only the existence of a non-commuting state, so a checker could only prove S2 without h (vacuous)."

sa_fail_forward "Docs.ms.T2" 3 "S3 (the a-component of F4_Kirkwood is a·b) is the definition of F4_Kirkwood (rfl). impl does not state it, so a checker could only prove S3 without h (vacuous)."

sa_fail_forward "Docs.ms.T2" 4 "S4 (the b-component of F4_Kirkwood is b) is the definition of F4_Kirkwood (rfl). impl does not state it, so a checker could only prove S4 without h (vacuous)."

sa_fail_forward "Docs.ms.T2" 5 "S5 (F3_Kirkwood c = c²/4) is the definition of F3_Kirkwood (rfl). impl does not state it, so a checker could only prove S5 without h (vacuous)."

@[sa_backward "Docs.ms.T2"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) (_s5 : S5) : sa_impl% "Docs.ms.T2" := s1

end Alignment.Shadows.Docs.ms_T2

/-! ### `Docs.ms.T3` (S2 unfolds `IsKirkwoodForm` and `Equivariant`; the checker maps under the
eight existential binders with `Exists.imp`) -/
namespace Alignment.Shadows.Docs.ms_T3

sa_claim "Docs.ms.T3" group "Docs" required
  text "theorem kirkwood_form_not_equivariant : ∃ (V₄ V₃ : Type) (_ : AddCommGroup V₄) (_ : AddCommGroup V₃) (_ : Module ℝ V₄) (_ : Module ℝ V₃) (M : V₄ →ₗ[ℝ] V₃) (C₄ : ClosureFamily V₄), C₄.IsKirkwoodForm ∧ ∀ (C₃ : ClosureFamily V₃), ¬ Equivariant M C₄.C C₃.C [...] Plain math: T3 is the existential statement T3b. There is a linear `M` and a non-additive order-4 field `C₄` such that no order-3 field `C₃` satisfies `M ∘ C₄ = C₃ ∘ M` (the witness of T2, over ℝ)."
  impl EBCMCategory.MarginalisationCharacterization.kirkwood_form_not_equivariant

@[sa_forward "Docs.ms.T3" 1]
theorem fwd1 (h : sa_impl% "Docs.ms.T3") : S1 := h

@[sa_forward "Docs.ms.T3" 2]
theorem fwd2 (h : sa_impl% "Docs.ms.T3") : S2 :=
  h.imp fun _ => Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ =>
    Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ hc =>
      ⟨fun hall => hc.1.elim fun u hu => hu.elim fun v huv => huv (hall u v), hc.2⟩

sa_fail_forward "Docs.ms.T3" 3 "impl kirkwood_form_not_equivariant is existential; the T2 surrogate over ℝ (MℝLin, C4ℝ) appears only in its proof. S3 (C4ℝ is Kirkwood-form and no C₃ makes MℝLin intertwine it) is about the named witness and does not follow from the existential."

@[sa_backward "Docs.ms.T3"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "Docs.ms.T3" := s1

end Alignment.Shadows.Docs.ms_T3

/-! ### `Docs.ms.T3-linearEquivariant` -/
namespace Alignment.Shadows.Docs.ms_T3_linearEquivariant

sa_claim "Docs.ms.T3-linearEquivariant" group "Docs" required
  text "For a linear `L₄` this reads `L₄(ker M) ⊆ ker M` (`linear_admits_equivariant_iff`), so linear closures are not equivariant for every `M`."
  impl EBCMCategory.MarginalisationCharacterization.linear_closure_equivariant EBCMCategory.MarginalisationCharacterization.isLinear_admits_equivariant

sa_fail_forward "Docs.ms.T3-linearEquivariant" 1 "impl = linear_closure_equivariant ∧ isLinear_admits_equivariant. The first is tautological (its hypothesis is its conclusion unfolded), the second vacuous (∃ F₃, … ∨ True). Neither mentions ker M, so S1 (an equivariant F₃ forces L₄(ker M) ⊆ ker M) does not follow. The text cites linear_admits_equivariant_iff, which is not in impl."

sa_fail_forward "Docs.ms.T3-linearEquivariant" 2 "S2 (L₄(ker M) ⊆ ker M gives an equivariant F₃) is the reverse direction of linear_admits_equivariant_iff, which is not in impl; the tautological and vacuous impl conjuncts do not give it."

sa_fail_forward "Docs.ms.T3-linearEquivariant" 3 "S3 (some linear L₄ admits no equivariant F₃ for some M) needs a concrete counterexample, which impl does not provide. isLinear_admits_equivariant even asserts '∃ F₃, … ∨ True' for every linear closure."

sa_fail_backward "Docs.ms.T3-linearEquivariant" "Both impl conjuncts are provable outright (fun _ _ _ h => h, and ⟨0, Or.inr trivial⟩) without any shadow, so a backward checker could only be vacuous."

end Alignment.Shadows.Docs.ms_T3_linearEquivariant

/-! ### `Docs.ms.T3-kkr` -/
namespace Alignment.Shadows.Docs.ms_T3_kkr

sa_claim "Docs.ms.T3-kkr" group "Docs" required
  text "the Kiss–Kenah–Rempala conditions ensure `F_3` is exact at the *unclosed limit* (κ constant) but place no constraint on the order-4 closure used to define `F_4`. T3c records only that a degree record with `closureKappa = 1` can be paired with the non-equivariant surrogate of T3b; the two are unrelated data."
  impl EBCMCategory.MarginalisationCharacterization.kkr_necessary_not_sufficient

@[sa_forward "Docs.ms.T3-kkr" 1]
theorem fwd1 (h : sa_impl% "Docs.ms.T3-kkr") : S1 :=
  h.imp fun _ hψ =>
    hψ.elim fun _ h => h.elim fun _ h => h.elim fun _ h => h.elim fun _ h =>
      h.elim fun _ h => h.elim fun _ h => h.elim fun _ h => h.elim fun _ hc => hc.1

sa_fail_forward "Docs.ms.T3-kkr" 2 "impl kkr_necessary_not_sufficient is existential over V₄, V₃, M, C₄; the T3b surrogate (MℝLin, C4ℝ) appears only in its proof. S2 (no C₃ makes MℝLin intertwine C4ℝ) is about the named surrogate and does not follow from the existential."

sa_fail_backward "Docs.ms.T3-kkr" "With the witnesses from S1 and S2 (U4ℝ, U3ℝ, MℝLin, C4ℝ), impl still needs C4ℝ.IsKirkwoodForm, which no shadow states. It is the trusted lemma C4ℝ_isKirkwoodForm, which a checker may not cite, and a direct proof needs real arithmetic. impl is stronger by that conjunct."

end Alignment.Shadows.Docs.ms_T3_kkr

/-! ### `Docs.ms.T4` -/

namespace Alignment.Shadows.Docs.ms_T4

universe u_1 u_2

sa_claim "Docs.ms.T4" group "Docs" required
  text "theorem fibre_collapse_obstruction (M : V₄ →ₗ[ℝ] V₃) (F : V₄ → V₄) (u₁ u₂ : V₄) (h_fibre : M u₁ = M u₂) (h_split : M (F u₁) ≠ M (F u₂)) : ∀ (C₃ : ClosureFamily V₃), ¬ Equivariant M F C₃.C [...] Lifts the argument inlined in T3b to a reusable structural lemma."
  impl EBCMCategory.MarginalisationDynamicalGap.fibre_collapse_obstruction

@[sa_forward "Docs.ms.T4" 1]
theorem fwd1 (h : sa_impl% "Docs.ms.T4") : S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F u₁ u₂ hf hs
  exact h M F u₁ u₂ hf hs

@[sa_backward "Docs.ms.T4"]
theorem bwd (s1 : S1.{u_1, u_2}) : sa_impl% "Docs.ms.T4" := by
  intro V₄ V₃ _ _ _ _ M F u₁ u₂ hf hs
  exact s1 M F u₁ u₂ hf hs

end Alignment.Shadows.Docs.ms_T4

/-! ### `Docs.ms.T4-companion` -/

namespace Alignment.Shadows.Docs.ms_T4_companion

sa_claim "Docs.ms.T4-companion" group "Docs" required
  text "A companion theorem `kirkwood_not_equivariant_via_T4` re-derives T3b using T4."
  impl EBCMCategory.MarginalisationDynamicalGap.kirkwood_not_equivariant_via_T4

@[sa_forward "Docs.ms.T4-companion" 1]
theorem fwd1 (h : sa_impl% "Docs.ms.T4-companion") : S1 := h

/-- `C4ℝ.C` is `F4Kℝ` by definition of `C4ℝ`. -/
@[sa_forward "Docs.ms.T4-companion" 2]
theorem fwd2 (h : sa_impl% "Docs.ms.T4-companion") : S2 := h

@[sa_backward "Docs.ms.T4-companion"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "Docs.ms.T4-companion" := s1

end Alignment.Shadows.Docs.ms_T4_companion

/-! ### `Docs.ms.T5` -/

namespace Alignment.Shadows.Docs.ms_T5

universe u_1 u_2

sa_claim "Docs.ms.T5" group "Docs" required
  text "theorem trajectoryGap_hasDerivAt_zero (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃} (h₄ : IsFlow F₄ φ₄) (h₃ : IsFlow F₃ φ₃) (u : V₄) : HasDerivAt (trajectoryGap M φ₄ φ₃ u) (algebraicGap M F₄ F₃ u) 0"
  impl EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_hasDerivAt_zero

@[sa_forward "Docs.ms.T5" 1]
theorem fwd1 (h : sa_impl% "Docs.ms.T5") : S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ u
  exact h M F₄ F₃ h₄ h₃ u

/-- `trajectoryGap M φ₄ φ₃ u` and `algebraicGap M F₄ F₃ u` unfold to the primitive forms. -/
@[sa_forward "Docs.ms.T5" 2]
theorem fwd2 (h : sa_impl% "Docs.ms.T5") : S2.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ u
  exact h M F₄ F₃ h₄ h₃ u

@[sa_backward "Docs.ms.T5"]
theorem bwd (s1 : S1.{u_1, u_2}) (_s2 : S2.{u_1, u_2}) : sa_impl% "Docs.ms.T5" := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ u
  exact s1 M F₄ F₃ h₄ h₃ u

end Alignment.Shadows.Docs.ms_T5

/-! ### `Docs.ms.T5-witnessGap` -/
namespace Alignment.Shadows.Docs.ms_T5_witnessGap

sa_claim "Docs.ms.T5-witnessGap" group "Docs" required
  text "**Specialisation to the (2,1) witness** (`algebraicGap_at_witness`): `algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = fun _ => 2`."
  impl EBCMCategory.MarginalisationDynamicalGap.algebraicGap_at_witness

@[sa_forward "Docs.ms.T5-witnessGap" 1]
theorem fwd1 (h : sa_impl% "Docs.ms.T5-witnessGap") : S1 := h

@[sa_backward "Docs.ms.T5-witnessGap"]
theorem bwd (s1 : S1) : sa_impl% "Docs.ms.T5-witnessGap" := s1

end Alignment.Shadows.Docs.ms_T5_witnessGap

/-! ### `Docs.ms.T5-rateTwo` -/
namespace Alignment.Shadows.Docs.ms_T5_rateTwo

sa_claim "Docs.ms.T5-rateTwo" group "Docs" required
  text "For *any* local solutions ψ₄ of F4Kℝ from u₁ and ψ₃ of F3Kℝ from M u₁, the gap `t ↦ M(ψ₄ t) − ψ₃ t` has first-order rate exactly 2 (`witness_localGap_hasDerivAt`), and such local solutions exist (`witness_local_solutions_exist`)."
  impl EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_rate_two_at_witness

sa_fail_forward "Docs.ms.T5-rateTwo" 1 "impl trajectoryGap_rate_two_at_witness assumes global flows φ₄ of F4Kℝ and φ₃ of F3Kℝ. The latter cannot exist (no_flow_F3Kℝ), so impl is vacuous. S1 (for local solutions the gap has rate exactly 2) is witness_localGap_hasDerivAt, which the text cites and which is not in this claim's impl list."

sa_fail_forward "Docs.ms.T5-rateTwo" 2 "S2 (local solutions from u₁ and M u₁ exist) is witness_local_solutions_exist, which is not in impl. impl assumes global flows and asserts no existence."

sa_fail_backward "Docs.ms.T5-rateTwo" "Deriving impl from S1 needs the global flows turned into LocalSol curves, which requires a positive real radius (0 < 1 in ℝ via zero_lt_one), not structural. impl's hypothesis IsFlow F3Kℝ φ₃ is in any case refuted by no_flow_F3Kℝ (hypothesis_refuted)."

end Alignment.Shadows.Docs.ms_T5_rateTwo

/-! ### `Docs.ms.T6` -/

namespace Alignment.Shadows.Docs.ms_T6

sa_claim "Docs.ms.T6" group "Docs" required
  text "theorem refinement_failure_exists : ∃ (F4_kirk : U4ℝ → U4ℝ) (F3_kirk : U3ℝ → U3ℝ) (F3_exact : U3ℝ → U3ℝ) (u₀ : U4ℝ), (ClosureFamily.mk F4_kirk).IsKirkwoodForm ∧ (ClosureFamily.mk F3_kirk).IsKirkwoodForm ∧ MℝLin (F4_kirk u₀) = F3_exact (MℝLin u₀) ∧ F3_kirk (MℝLin u₀) ≠ F3_exact (MℝLin u₀) [...] Witness: `F4_kirk = F4Kℝ`, `F3_kirk = F3Kℝ`, `F3_exact = const 6`, `u₀ = u₁`."
  impl EBCMCategory.MarginalisationDynamicalGap.refinement_failure_exists

@[sa_forward "Docs.ms.T6" 1]
theorem fwd1 (h : sa_impl% "Docs.ms.T6") : S1 := h

sa_fail_forward "Docs.ms.T6" 2 "The impl (refinement_failure_exists) is existential; its witnesses (F4Kℝ, F3Kℝ, const 6, u₁) are chosen only inside the proof. S2 ((ClosureFamily.mk F4Kℝ).IsKirkwoodForm) is about the specific map F4Kℝ and cannot be extracted from the existential; the lemma that states it (C4ℝ_isKirkwoodForm) is not in the impl list."

sa_fail_forward "Docs.ms.T6" 3 "S3 ((ClosureFamily.mk F3Kℝ).IsKirkwoodForm) is about the specific map F3Kℝ; the impl only asserts Kirkwood form for existentially hidden F3_kirk. The lemma stating it (F3Kℝ_isKirkwoodForm) is not in the impl list."

sa_fail_forward "Docs.ms.T6" 4 "S4 (MℝLin (F4Kℝ u₁) = const 6) is about the named witness; the impl's equation MℝLin (F4_kirk u₀) = F3_exact (MℝLin u₀) is about existentially hidden F4_kirk, F3_exact, u₀ and does not identify them with F4Kℝ, const 6, u₁. Computing 1·3 + 3 = 6 over ℝ would also need norm_num."

sa_fail_forward "Docs.ms.T6" 5 "S5 (F3Kℝ (MℝLin u₁) ≠ const 6) is about the named witness; the impl's inequality F3_kirk (MℝLin u₀) ≠ F3_exact (MℝLin u₀) is about existentially hidden witnesses, so S5 cannot be extracted. Computing 4²/4 = 4 ≠ 6 over ℝ would also need norm_num."

@[sa_backward "Docs.ms.T6"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) (_s5 : S5) : sa_impl% "Docs.ms.T6" := s1

end Alignment.Shadows.Docs.ms_T6

/-! ### `Docs.ms.T6-values` -/

namespace Alignment.Shadows.Docs.ms_T6_values

sa_claim "Docs.ms.T6-values" group "Docs" required
  text "`M(F4Kℝ u₁)(c) = 1·3 + 3 = 6` — m=4 chain is **exact** at first order. * `F3Kℝ(M u₁)(c) = 4²/4 = 4 ≠ 6` — m=3 Kirkwood deviates by 2."
  impl EBCMCategory.MarginalisationDynamicalGap.algebraicGap_at_witness EBCMCategory.MarginalisationDynamicalGap.refinement_failure_exists

sa_fail_forward "Docs.ms.T6-values" 1 "The impl gives algebraicGap MℝLinCLM F4Kℝ F3Kℝ u₁ = const 2 (only the difference M(F4Kℝ u₁) − F3Kℝ(M u₁)) and the existential refinement_failure_exists (hidden witnesses). The value MℝLin (F4Kℝ u₁) c = 6 is not stated: the difference alone does not determine it, and computing 1·3 + 3 = 6 over ℝ needs norm_num."

sa_fail_forward "Docs.ms.T6-values" 2 "F3Kℝ (MℝLin u₁) c = 4 is not stated by the impl: only the difference 2 (algebraicGap_at_witness) and an existential with hidden witnesses (refinement_failure_exists); computing 4²/4 = 4 over ℝ needs norm_num."

sa_fail_forward "Docs.ms.T6-values" 3 "F3Kℝ (MℝLin u₁) c ≠ 6 is not stated by the impl: refinement_failure_exists's inequality concerns existentially hidden F3_kirk, F3_exact, u₀, and from the difference = 2 alone one cannot conclude it without the value M(F4Kℝ u₁)(c) = 6 and real arithmetic."

/-- Evaluate the impl's function equality `algebraicGap … u₁ = fun _ => 2` at `c`;
`algebraicGap` and the pointwise subtraction on `U3ℝ` unfold to the shadow's difference, and
`MℝLinCLM` applies as `MℝLin`. -/
@[sa_forward "Docs.ms.T6-values" 4]
theorem fwd4 (h : sa_impl% "Docs.ms.T6-values") : S4 :=
  congrFun h.1 MarginalisationObstruction.Idx3.c

sa_fail_backward "Docs.ms.T6-values" "The impl conjunct refinement_failure_exists needs Kirkwood-form proofs for two closures ((ClosureFamily.mk F4_kirk).IsKirkwoodForm and (ClosureFamily.mk F3_kirk).IsKirkwoodForm); no shadow states a Kirkwood-form fact (S1–S4 are values at u₁ only), so the conjunct is not derivable. (The conjunct algebraicGap_at_witness would follow from S4 by funext and case analysis on Idx3.)"

end Alignment.Shadows.Docs.ms_T6_values

/-! ### `Docs.ms.T7` -/

namespace Alignment.Shadows.Docs.ms_T7

universe u_1 u_2

sa_claim "Docs.ms.T7" group "Docs" required
  text "theorem trajectoryGap_norm_ge_half_eps_t (M : V₄ →L[ℝ] V₃) (F₄ : V₄ → V₄) (F₃ : V₃ → V₃) {φ₄ : V₄ → ℝ → V₄} {φ₃ : V₃ → ℝ → V₃} (h₄ : IsFlow F₄ φ₄) (h₃ : IsFlow F₃ φ₃) (u : V₄) {ε : ℝ} (hε : 0 < ε) (h_gap : ε ≤ ‖algebraicGap M F₄ F₃ u‖) : ∃ T > 0, ∀ t, 0 < t → t ≤ T → ε * t / 2 ≤ ‖trajectoryGap M φ₄ φ₃ u t‖ [...] Quantitative time-domain refinement of T5: if the algebraic gap has norm at least `ε`, then the trajectory gap grows at least linearly (at rate `ε/2`) for sufficiently small positive `t`."
  impl EBCMCategory.MarginalisationDynamicalGap.trajectoryGap_norm_ge_half_eps_t

@[sa_forward "Docs.ms.T7" 1]
theorem fwd1 (h : sa_impl% "Docs.ms.T7") : S1.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ u ε hε hg
  exact h M F₄ F₃ h₄ h₃ u hε hg

/-- `algebraicGap` / `trajectoryGap` unfold to the primitive forms of `S2`. -/
@[sa_forward "Docs.ms.T7" 2]
theorem fwd2 (h : sa_impl% "Docs.ms.T7") : S2.{u_1, u_2} := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ u ε hε hg
  exact h M F₄ F₃ h₄ h₃ u hε hg

@[sa_backward "Docs.ms.T7"]
theorem bwd (s1 : S1.{u_1, u_2}) (_s2 : S2.{u_1, u_2}) : sa_impl% "Docs.ms.T7" := by
  intro V₄ V₃ _ _ _ _ M F₄ F₃ φ₄ φ₃ h₄ h₃ u ε hε hg
  exact s1 M F₄ F₃ h₄ h₃ u hε hg

end Alignment.Shadows.Docs.ms_T7

/-! ## README "Lean proofs" section

The claims `Docs.readme.conservationLaws`, `Docs.readme.r0RewiringIndependence`,
`Docs.readme.pgfIdentities` and `Docs.readme.vmInvariants` were retired (WP4): their source
sentence was replaced by the TRIAGE P2.1 wording, whose claims (`Docs.readme.leanScope`,
`Docs.readme.notSolutions`, `Docs.readme.legacy`) are informal. Their registrations, checkers and
failure records were removed with them. -/

/-! ## `Docs.cf.coarseGrainDef` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.cf_coarseGrainDef

sa_claim "Docs.cf.coarseGrainDef" group "Docs"
  text "Given an EBCM object (θ, φ, R, ψ), define F on objects by: [...] F(θ, φ, R, ψ) = (S, I, R) where S_l = ψ_l(θ_{1l}, …, θ_{Kl}) (evaluate PGF at θ-vector) R_l = R_l (identity) I_l = 1 - S_l - R_l (derived) [...] On morphisms, F is not yet defined: the formula ψ ∘ h ∘ ψ^{-1} does not type-check in general (h acts on (θ, φ, R), ψ only on θ), so F is a map on objects only."
  impl

end Alignment.Shadows.Docs.cf_coarseGrainDef

/-! ## `Docs.cf.dispersionSingleScalar` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.cf_dispersionSingleScalar

sa_claim "Docs.cf.dispersionSingleScalar" group "Docs"
  text "The correction involves the **index of dispersion** σ²/κ and the mean κ: ψ''(1)/ψ'(1) = κ − 1 + σ²/κ. No single scalar measures how much information the EBCM adds over the node model."
  impl

end Alignment.Shadows.Docs.cf_dispersionSingleScalar

/-! ## `Docs.cf.liftDef` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.cf_liftDef

sa_claim "Docs.cf.liftDef" group "Docs"
  text "Given a node-based SIR model with mass-action rates β and γ (R₀ = β/γ), define G by: [...] G(S, I, R; β, γ) = EBCM(ψ_Poisson(κ), β̃, γ̃) where β̃ = β/κ, γ̃ = γ − β/κ, for any mean degree κ > R₀"
  impl

end Alignment.Shadows.Docs.cf_liftDef

/-! ## `Docs.cf.liftNotUnique` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.cf_liftNotUnique

sa_claim "Docs.cf.liftNotUnique" group "Docs"
  text "**Caveat:** Even the Poisson lift is not unique: any mean degree κ > R₀ works, with β̃ = β/κ and γ̃ = γ − β/κ. [...] The Poisson lift is singled out by giving mass-action dynamics for S, not by any minimality property."
  impl

end Alignment.Shadows.Docs.cf_liftNotUnique

/-! ## `Docs.cf.pgfClosureTreeLike` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.cf_pgfClosureTreeLike

sa_claim "Docs.cf.pgfClosureTreeLike" group "Docs"
  text "S(t) = ψ(θ(t)) (exact on configuration-model networks as N → ∞, which are locally tree-like)"
  impl

end Alignment.Shadows.Docs.cf_pgfClosureTreeLike

/-! ## `Docs.cf.poissonEquivMassAction` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.cf_poissonEquivMassAction

sa_claim "Docs.cf.poissonEquivMassAction" group "Docs"
  text "Markovian on Poisson network ← same S(t) as mass-action SIR (after reparametrisation)"
  impl

end Alignment.Shadows.Docs.cf_poissonEquivMassAction

/-! ## `Docs.cf.poissonUniqueSection` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.cf_poissonUniqueSection

sa_claim "Docs.cf.poissonUniqueSection" group "Docs"
  text "This embeds the node-based model into an EBCM with the **Poisson PGF**, whose susceptible curve matches the node model's after this reparametrisation; the EBCM infected curve differs. Among PGFs, only the Poisson PGF gives mass-action dynamics for S (Theorem 4.3(c))."
  impl

end Alignment.Shadows.Docs.cf_poissonUniqueSection

/-! ## `Docs.cf.subcategoryInclusions` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.cf_subcategoryInclusions

sa_claim "Docs.cf.subcategoryInclusions" group "Docs"
  text "Each restriction narrows the class of models (informally a subcategory inclusion; no category is defined)."
  impl

end Alignment.Shadows.Docs.cf_subcategoryInclusions

/-! ## `Docs.cf.thm3_3-lostInformation` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.cf_thm3_3_lostInformation

sa_claim "Docs.cf.thm3_3-lostInformation" group "Docs"
  text "The node-level trajectory does not determine ψ, but it retains more than the first moment: for instance its early growth rate depends on ψ''(1)/ψ'(1). So the lost information is not simply the degree distribution beyond its mean."
  impl

end Alignment.Shadows.Docs.cf_thm3_3_lostInformation

/-! ## `Docs.cf.thm4_1` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.cf_thm4_1

sa_claim "Docs.cf.thm4_1" group "Docs"
  text "**Theorem 4.1 (corrected).** F and G are not a Galois connection for the dimension preorder (M₁ ≤ M₂ iff dim M₁ ≤ dim M₂) used in the Lean library: the condition [...] F(E) ≤ N ⟺ E ≤ G(N) [...] fails for E = ⟨10, r⟩ and N = ⟨3, r⟩, where F(E) ≤ N holds but E ≤ G(N) does not (`not_galoisConnection_coarseGrain_poissonLift`)."
  impl

end Alignment.Shadows.Docs.cf_thm4_1

/-! ## `Docs.cf.thm4_3-massAction` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.cf_thm4_3_massAction

sa_claim "Docs.cf.thm4_3-massAction" group "Docs"
  text "(c) With S = ψ(θ), dS/dt = ψ'(θ)·dθ/dt = −β̃ψ'(θ)φ_I, which equals −(κβ̃)·S·φ_I iff ψ'(θ) = κψ(θ); then S(t) solves the mass-action equation with I := φ_I and rates β = κβ̃, γ = β̃ + γ̃ (Rempała 2023)."
  impl

end Alignment.Shadows.Docs.cf_thm4_3_massAction

/-! ## `Docs.cf.thm7_1` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.cf_thm7_1

sa_claim "Docs.cf.thm7_1" group "Docs"
  text "**Theorem 7.1 (withdrawn).** It is not true that every SIR trajectory is reproduced exactly by EBCMs with arbitrary PGFs ψ with ψ'(1) = κ: an EBCM with given ψ has only two rates (β̃, γ̃), which cannot in general match an arbitrary curve S(t). The earlier proof defined θ(t) = ψ⁻¹(S(t)) but did not check that θ(t) solves the EBCM θ-equation. What does hold is the Poisson lift of §4.1: for Poisson ψ and κ > R₀ the EBCM reproduces the mass-action S(t) (Rempała 2023)."
  impl

end Alignment.Shadows.Docs.cf_thm7_1

/-! ## `Docs.cf.thm8_1-factor` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.cf_thm8_1_factor

sa_claim "Docs.cf.thm8_1-factor" group "Docs"
  text "The ratio of the EBCM excess degree to the mean degree is (ψ''(1)/ψ'(1))/κ = 1 + (σ²/κ - 1)/κ = (κ² − κ + σ²)/κ²."
  impl

end Alignment.Shadows.Docs.cf_thm8_1_factor

/-! ## `Docs.ms.T2-smallestWitness` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.ms_T2_smallestWitness

sa_claim "Docs.ms.T2-smallestWitness" group "Docs"
  text "It is one arithmetic witness for one pair of fields, not a general law: with `M = id` a quadratic field commutes with itself, and at `u4 = (1, 3)` the quadratic field `c ↦ 3c²/8` agrees with `M ∘ F4_Kirkwood`."
  impl

end Alignment.Shadows.Docs.ms_T2_smallestWitness

/-! ## `Docs.ms.T6-phaseReversal` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.ms_T6_phaseReversal

sa_claim "Docs.ms.T6-phaseReversal" group "Docs"
  text "Here \"exact\" means only agreement with the fitted constant `F3_exact = 6`. T6 is one surrogate witness and says nothing about the empirical phase reversal. T3b (via T4) shows that no order-3 field commutes with F4Kℝ under MℝLin at every state; at the single state u₁ the non-additive field `c ↦ 3c²/8` does match (`kirkwoodForm_matches_at_witness`)."
  impl

end Alignment.Shadows.Docs.ms_T6_phaseReversal

/-! ## `Docs.ms.T7-witness` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.ms_T7_witness

sa_claim "Docs.ms.T7-witness" group "Docs"
  text "At the (2,1) witness the global-flow form is vacuous (F3Kℝ has no global flow). The local form `localGap_norm_ge_half_eps_t` assumes only local solutions, and at the witness (`witness_localGap_ge`, ε = 2) it gives `‖M(ψ₄ t) − ψ₃ t‖ ≥ t` for all small `t > 0`, for any local solutions ψ₄ of F4Kℝ from u₁ and ψ₃ of F3Kℝ from M u₁."
  impl

end Alignment.Shadows.Docs.ms_T7_witness

/-! ## `Docs.ms.flowDef` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.ms_flowDef

sa_claim "Docs.ms.flowDef" group "Docs"
  text "**Flow:** `IsFlow F φ` ↔ `(∀ v, φ v 0 = v) ∧ ∀ v t, HasDerivAt (φ v) (F (φ v t)) t`. Existence and uniqueness are *hypotheses* on the systems, not derived. `IsFlow` asks for solutions on all of `ℝ`, so a field whose solutions blow up in finite time has no flow: `F3Kℝ` (`c ↦ c²/4`) has none (`no_flow_F3Kℝ`)."
  impl

end Alignment.Shadows.Docs.ms_flowDef

/-! ## `Docs.ms.flowHypothesised` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.Docs.ms_flowHypothesised

sa_claim "Docs.ms.flowHypothesised" group "Docs"
  text "**ODE flow existence/uniqueness** is *hypothesised*, not derived. Picard–Lindelöf gives only local existence for `C¹` `F`; global flows (`IsFlow`) need not exist, and for `F3Kℝ` they do not (`no_flow_F3Kℝ`)."
  impl

end Alignment.Shadows.Docs.ms_flowHypothesised
