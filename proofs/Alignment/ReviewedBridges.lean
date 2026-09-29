import Alignment.Registry
import Alignment.Example.ExampleChecks
import Alignment.Example.SelfTest
import Alignment.Checks.SurvivalBridge
-- shadows reviewed with `sa_shadow_reviewed` below
import Alignment.Shadows.CategoricalComposition
import Alignment.Shadows.ConvergenceTheorems
import Alignment.Shadows.InvariantRegion
import Alignment.Shadows.MarginalisationCharacterization
import Alignment.Shadows.PairwiseClosureConditions

/-!
# Reviewed bridges

This is the ONLY module whose `sa_bridge_reviewed` / `sa_bridge_rejected` records count.
Changes here need trusted-library-level review: a record asserts that the bridge's right-hand
side is exactly the source text's notion and smuggles no theorem content.

Procedure (independent reviewer, never the checker author):

1. Run `bash scripts/sa_pass.sh`; the report lists every `unreviewed` / `stale` bridge with its
   statement and stable hash.
2. Compare the statement with the cited source text: infinities and degenerate inputs, strict
   versus non-strict inequalities, which variable is which, hidden side conditions.
3. Accept with `sa_bridge_reviewed <decl> "<hash>" "<source: why RHS is the text's notion>"`
   or reject with `sa_bridge_rejected <decl> "<reason>"`.
4. A record whose hash no longer matches the bridge's statement is reported as `stale` and does
   not count: re-review before updating a hash.

Import every `Checks/<Group>` module that declares bridges above this comment.

## Rejected bridges (reasons)

* (none yet)

## Shadow reviews (`sa_shadow_reviewed`)

A shadow flagged `shadow_trusted_free` mentions no trusted constant. A record accepts it only if
(i) the claim's own registered text is itself a statement of arithmetic or logic, meaning the
text states the identity, inequality or equivalence, so that nothing has to be taken from
another passage; and (ii) the shadow states exactly that, with the same variables, hypotheses,
strictness and number system. A shadow may be *more* general than the text, for example
quantifying over every real where the text speaks of susceptible fractions, because then the
text still follows from it. It may not be weaker. Domain words that have no Lean object
('trivial layer', 'susceptible product') are accepted as glosses only where the text itself
reduces them to numbers.

Review of 2026-09-26 (independent reviewer; not an author of any shadow, checker or trusted
theorem). The candidates were the 13 claims whose checks all pass and whose score is zeroed only
by `shadow_trusted_free` (report of 2026-09-26 18:11). 11 claims (16 shadows) are accepted
below. 2 claims are rejected.

## Rejected shadow reviews (reasons; no record, so the flag stays)

* `CategoricalComposition.R100f.1` (S1, S2). The text (CategoricalComposition.lean:434-436) says
  'the real-number identities that the pentagon and triangle identities would reduce to hold',
  but it never says which identities. At least three readings exist:
  1. the equality of all the vertices of each diagram (for the pentagon also
     `(ab)(cd)`, `(a(bc))d` and `a((bc)d)`; for the triangle also `a·(1·b) = a·b`);
  2. only the two ends, `((ab)c)d = a(b(cd))`;
  3. the strictness conditions, i.e. associativity and the unit laws.

  The shadows take reading 2. For the triangle they take the associator leg
  `(a·1)·b = a·(1·b)` and leave out the unitor legs. The shadow author's own AMBIGUITY note
  covers the pentagon only. A text with no fixed arithmetic content cannot be certified as an
  arithmetic statement. Fix: state the identities in the docstring, re-register the text, and
  re-shadow blind.
* `ClusteringExtension.R73` (S1). The text (ClusteringExtension.lean:122), 'Triangle edges
  contribute less per edge than single edges to R₀', is a statement about R₀, and the trusted
  library has an R₀ for this setting (`clustered_R0`, Result 72). It is not arithmetic. The
  inequality `T(1+T)/2 ≤ T` does not occur in the text: the shadow imports it from the passages
  of two other claims, R73-sec-a and R73-sec-b (lines 112-120). Those passages say that the
  claim 'is a statement about that formula, not a derivation of R₀' and that the per-stub value
  'is not sourced'. The text also says 'less' (strict), while the shadow has `≤`, with
  equality at T = 1. A faithful shadow must mention `clustered_R0`.
-/

/-! ## Worked example -/

sa_bridge_reviewed Alignment.Example.PoissonVariance.bridge_variance "16481377043707351972"
  "EpiCategory.lean (PGFData.variance docstring): Var(k) = ψ''(1) + ψ'(1) − (ψ'(1))²; the RHS
  ψ''(1) + ψ'(1)(1 − ψ'(1)) is the same polynomial in the PGF data, with no side condition"

/-! ## Group SurvivalBridge -/

sa_bridge_reviewed Alignment.Shadows.SurvivalBridge.R46c.bridge_edgeModel "12900344808292493412"
  "The R46c text (EBCMCategory/SurvivalBridge.lean:170-172) says 'the EBCM uses T·ψ''(1)/ψ'(1)'. EpiCategory.lean defines edgeModel p ψ = ⟨4, transmissibility p * excessDegree ψ⟩ with T = β/(β+γ) (line 79), excessDegree = secondFactorial/mean, and PGFData's docstring gives mean = ψ'(1) and secondFactorial = ψ''(1). So the RHS ⟨4, ((β/(β+γ))·ψ''(1))/ψ'(1)⟩ is exactly the text's per-edge-transmissibility-times-mean-excess-degree R₀. The only step is mul_div_assoc, which holds in ℚ with no hypotheses (and mean > 0, β+γ > 0 by the structure invariants in any case), and dim := 4 is the definition's own value. No Poisson content (κ²/κ = κ) and no impl theorem are used."

sa_bridge_reviewed Alignment.Shadows.SurvivalBridge.R46c.bridge_nodeModel "1686206359287332404"
  "The R46c text says 'DSA uses β·μ/(β+γ) where μ = mean degree'. EpiCategory.lean defines nodeModel p κ = ⟨3, transmissibility p * κ⟩ = ⟨3, (β/(β+γ))·κ⟩, where κ is the mean degree (edge_refines_node instantiates it with ψ.mean, and the checker uses the Poisson mean, which is definitionally κ). So the RHS ⟨3, β·κ/(β+γ)⟩ is exactly the text's DSA formula with μ = κ. The only step is div_mul_eq_mul_div, which is unconditional in ℚ and needs no sign or nonzero side condition on κ, and dim := 3 is the definition's own value. The bridge carries no theorem content and uses no impl theorem."

/-! ## Self-test records (deliberately broken; `--self-test` checks that they do not count) -/

-- stale: the hash does not match the bridge's statement
sa_bridge_reviewed Alignment.Example.SelfTest.StaleBridge.bridge "0"
  "SELFTEST: stale review record"
-- valid hash, but the bridge's proof depends on an implementation theorem (laundering)
sa_bridge_reviewed Alignment.Example.SelfTest.LaunderingBridge.bridge "16481377043707351972"
  "SELFTEST: laundering bridge with a matching hash"
-- rejected by the reviewer
sa_bridge_rejected Alignment.Example.SelfTest.RejectedBridge.bridge
  "SELFTEST: rejected bridge"
-- reviewed with a matching hash, but the checker using it belongs to another claim
-- (`SELFTEST.outOfScopeBridge` uses the worked example's bridge above)

/-! ## Self-test shadow reviews (`sa_shadow_reviewed`) -/

-- valid: the mock's text is arithmetic, so a trusted-free shadow is appropriate
sa_shadow_reviewed Alignment.Example.SelfTest.TrustedFreeReviewed.S1 "12124625975434494302"
  "SELFTEST: the mock text is a statement of real arithmetic (1 * S = S)"
-- stale: the hash does not match the shadow's content
sa_shadow_reviewed Alignment.Example.SelfTest.TrustedFreeStale.S1 "0"
  "SELFTEST: stale shadow review record"

/-! ## Shadow reviews: group CategoricalComposition -/

sa_shadow_reviewed Alignment.Shadows.CategoricalComposition.R96a.S1 "18118268704599918753"
  "Text (CategoricalComposition.lean:98-100): 'Product susceptible fraction: S = S₁ · S₂. For layer susceptible fractions S₁ ∈ (0,1] and S₂ ∈ (0,1], the product S₁·S₂ ∈ (0,1].' The first sentence is a heading that defines S as the product. The operative claim is closed real arithmetic. The trusted library has no layer susceptible fraction: EBCMLayer carries only mean, secondFactorial, T and dim. S1 is the lower half of the conclusion, 0 < S₁·S₂, under exactly the text's hypotheses 0 < Sᵢ ≤ 1 (open at 0, closed at 1), for all reals."

sa_shadow_reviewed Alignment.Shadows.CategoricalComposition.R96a.S2 "16452762903075868917"
  "Text as for S1 (CategoricalComposition.lean:98-100). S2 is the upper half of the conclusion S₁·S₂ ∈ (0,1], that is S₁·S₂ ≤ 1 (closed at 1, as in the text), under the text's hypotheses 0 < Sᵢ ≤ 1, for all reals. S1 and S2 together are exactly membership in (0,1]."

sa_shadow_reviewed Alignment.Shadows.CategoricalComposition.R100a.S1 "8006581057523220641"
  "Text (CategoricalComposition.lean:411-412): 'Left unitality: the trivial layer is a left unit for the susceptible product. S_unit · S = 1 · S = S.' The text itself reduces the trivial layer to the number S_unit = 1. The docstring models the unit this way (lines 407-409), and the section header says that no category is defined and that the identities are verified for real multiplication (lines 398-405). EBCMLayer cannot represent the trivial layer (mean_pos). The content is the real identity 1·S = S. S1 states it for every real S, which is at least as strong as for every susceptible fraction."

sa_shadow_reviewed Alignment.Shadows.CategoricalComposition.R100b.S1 "12227782950718836910"
  "Text (CategoricalComposition.lean:415): 'Right unitality: S · S_unit = S · 1 = S.' The text displays the real identity S·1 = S, with S_unit = 1 as in R100a. S1 is ∀ S : ℝ, S * 1 = S, exactly that and at least as general as the text."

sa_shadow_reviewed Alignment.Shadows.CategoricalComposition.R100c.S1 "8966180171648085440"
  "Text (CategoricalComposition.lean:418-419): 'Associativity of the multiplex product: (S₁ · S₂) · S₃ = S₁ · (S₂ · S₃).' The multiplex product of susceptible fractions is real multiplication (Result 96a). The text displays associativity of that product. S1 is ∀ S₁ S₂ S₃ : ℝ, (S₁ * S₂) * S₃ = S₁ * (S₂ * S₃), the displayed identity verbatim for all reals."

sa_shadow_reviewed Alignment.Shadows.CategoricalComposition.R100d.S1 "3921892068967338273"
  "Text (CategoricalComposition.lean:423-424): 'The product ODE dimension is associative: (d₁ + d₂) + d₃ = d₁ + (d₂ + d₃).' The product dimension is defined as the sum of the layer dimensions (Result 96b, MultiplexProduct.dim = layer1.dim + layer2.dim). MultiplexProduct has exactly two layers, so a triple product cannot be formed. The text's content is the displayed identity on natural-number dimensions. S1 is that identity for all d₁ d₂ d₃ : ℕ. It is not a claim about compactMultiplexDim, and the text does not say it is."

sa_shadow_reviewed Alignment.Shadows.CategoricalComposition.R100e.S1 "10859786292137398121"
  "Text (CategoricalComposition.lean:428-429): 'The unit dimension is 0 (trivial ODE system): 0 + d = d and d + 0 = d.' That the unit dimension is 0 is the text's stipulation: the trivial ODE system has no Lean object. The claim is the two displayed unit laws on natural-number dimensions. S1 is the first, ∀ d : ℕ, 0 + d = d, verbatim."

sa_shadow_reviewed Alignment.Shadows.CategoricalComposition.R100e.S2 "4420622397373677444"
  "Text as for S1 (CategoricalComposition.lean:428-429). S2 is the second displayed unit law, ∀ d : ℕ, d + 0 = d, verbatim. It is definitional in ℕ, but the text asserts it explicitly as half of the conjunction, so it belongs in the shadow set."

/-! ## Shadow reviews: group ConvergenceTheorems -/

sa_shadow_reviewed Alignment.Shadows.ConvergenceTheorems.dfeDerivativeAbsLeOneIff.S1 "18405518961620889407"
  "Text (ConvergenceTheorems.lean:326-327): 'For T ≥ 0 and excessDeg ≥ 0, |f'(1)| ≤ 1 ↔ R₀ ≤ 1, where f'(1) = R₀ = T · excessDeg.' The where-clause replaces both f'(1) and R₀ by T·excessDeg. excessDeg is a free real with its own hypothesis, not PGFMoments.excessDegree. The derivative fact is a separate claim (finalSizeMapHasDerivAt, whose shadow mentions finalSizeMap). So the text is the real equivalence |T·e| ≤ 1 ↔ T·e ≤ 1 for T, e ≥ 0, and the module works over ℝ. S1 is its (→) direction with the same non-strict inequalities and hypotheses."

sa_shadow_reviewed Alignment.Shadows.ConvergenceTheorems.dfeDerivativeAbsLeOneIff.S2 "12647593375326244056"
  "Text as for S1 (ConvergenceTheorems.lean:326-327). S2 is the (←) direction, T·e ≤ 1 → |T·e| ≤ 1, for all reals T, e ≥ 0. S1 and S2 together are exactly the text's equivalence."

/-! ## Shadow reviews: group InvariantRegion -/

sa_shadow_reviewed Alignment.Shadows.InvariantRegion.phiILeTheta.S1 "9010931585015679052"
  "Text (InvariantRegion.lean:368): 'Edge conservation: θ = φ_S + φ_I + φ_R with φ_S, φ_R ≥ 0 gives φ_I ≤ θ.' This is a closed statement of ordered-field arithmetic about four numbers, and no trusted object is named. S1 is ∀ θ φS φI φR : ℚ, θ = φS + φI + φR → 0 ≤ φS → 0 ≤ φR → φI ≤ θ: the text's single hypothesis equation, its two non-negativity hypotheses (none on φ_I), and its non-strict conclusion. ℚ is the module's number system (DataTypes/InvariantRegion.md: all state variables are rationals)."

/-! ## Shadow reviews: group MarginalisationCharacterization -/

sa_shadow_reviewed Alignment.Shadows.MarginalisationCharacterization.existsEquivariantIffFibrewise.S1 "3630059095103699796"
  "Text (MarginalisationCharacterization.lean:280-282): 'For any field F on V₄, some order-3 field F₃ satisfies M ∘ F = F₃ ∘ M iff F maps each fibre of M into a single fibre: M u = M u' → M (F u) = M (F u').' This is a factorisation lemma of pure algebra and logic about arbitrary self-maps. The module's marginalisation is an arbitrary linear map M : V₄ →ₗ[ℝ] V₃ (DataTypes). The trusted predicate Equivariant M F G is by definition the pointwise equation ∀ u, M (F u) = G (M u), which is the text's M ∘ F = F₃ ∘ M and which the shadow writes out. S1 is the (→) direction for all ℝ-modules V₄, V₃, all linear M and all F : V₄ → V₄, with ∃ F₃ : V₃ → V₃ exactly as in the text."

sa_shadow_reviewed Alignment.Shadows.MarginalisationCharacterization.existsEquivariantIffFibrewise.S2 "9673709430542453181"
  "Text as for S1 (MarginalisationCharacterization.lean:280-282). S2 is the (←) direction: if M w = M w' → M (F w) = M (F w') for all w, w', then some F₃ : V₃ → V₃ satisfies M (F w) = F₃ (M w) for all w. The quantifiers are the same as in S1 (every ℝ-module pair, every linear M, every field F, and F₃ an arbitrary function, as 'order-3 field' requires). S1 and S2 together are exactly the text's iff."

/-! ## Shadow reviews: group PairwiseClosureConditions -/

sa_shadow_reviewed Alignment.Shadows.PairwiseClosureConditions.header_safeRegime.S3 "15140977414827178178"
  "Text (PairwiseClosureConditions.lean:9-21): a closed triple written as [ASI]_A = B * p_A, with B ≥ 0, ∑_A p_A = 1 and p_A ≥ 0, has total mass ∑_A [ASI]_A = B, and each triple is nonnegative. The header calls it 'a small algebraic fact': the text defines [ASI]_A as the product B * p_A over a finite set of states. S3 is conclusion 1 for that literal form: ∑ a, base * p a = base over every finite state type, under all three of the text's hypotheses (0 ≤ base, normalisation, pointwise nonnegativity). The base is any nonnegative rational, which is more general than B = (n-1)[SI]. The tripleTerm reading is covered by the trusted-mentioning S1 and S2."

sa_shadow_reviewed Alignment.Shadows.PairwiseClosureConditions.header_safeRegime.S4 "1806753512647260405"
  "Text as for S3 (PairwiseClosureConditions.lean:9-21). S4 is conclusion 2 for the literal form: ∀ a, 0 ≤ base * p a ('each triple count is nonnegative', read as non-strict as written), under the same three hypotheses, over every finite state type and every nonnegative rational base."

sa_shadow_reviewed Alignment.Shadows.PairwiseClosureConditions.weightInUnitInterval.S1 "12901778656111795673"
  "Text (PairwiseClosureConditions.lean:81-82): 'Under nonnegative normalized weights, each individual closure weight lies in [0,1].' The closure weights are a family p : α → ℚ over a finite state type. There is no trusted weight object (DataTypes: normalized means ∑ a, p a = 1 and nonnegative means ∀ a, 0 ≤ p a). The text is a closed arithmetic statement. The lower bound 0 ≤ p a is literally a hypothesis. S1 is the one non-trivial requirement, the upper bound p a ≤ 1 (closed, as in [0,1]), for every a, under both hypotheses. The reference adds the lower bound from the hypothesis, so S1 is equivalent to the text."
