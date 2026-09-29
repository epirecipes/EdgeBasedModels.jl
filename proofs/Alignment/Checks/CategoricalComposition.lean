import Alignment.Registry
import Alignment.Shadows.CategoricalComposition

/-!
# Checkers: group `CategoricalComposition`

Claim registrations, checkers and failure records for the claims of
`EBCMCategory/CategoricalComposition.lean`, against the blind shadow sets in
`Alignment/Shadows/CategoricalComposition.lean`.

No bridges are declared. Every definition the shadows use (`EBCMLayer.R0`, `excessDegree`,
`MultiplexProduct.R0_sum`, `StratifiedData.S_total`, `compactMultiplexDim`,
`MixingPullbackData.meanDeg`, `q1`, `q2`, and the alignment helpers `R0atT`, `clusteringCoeff`,
`C11`…`C22`) unfolds definitionally to what the implementation states wherever the two agree.
Where they do not agree, the gap is a library lemma (`Nat.cast_one`, `div_nonneg`, field
cancellation), a data invariant (`T_pos`, `sf_nonneg`, `mean_pos`) or a different notion, and no
bridge whose right-hand side is exactly the text's notion could close it. Those checks are
recorded with `sa_fail_*`.

Checker proofs are structural only: application, anonymous constructors, projections, `show`,
`rw [hyp]`, `rfl`.
-/

/-! ## R95a.2 -/
namespace Alignment.Shadows.CategoricalComposition.R95a_2

sa_claim "CategoricalComposition.R95a.2" group "CategoricalComposition" required
  text "We verify that R₀ = T · ψ''(1)/ψ'(1) for the resulting system."
  impl ebcm_functor_R0

@[sa_forward "CategoricalComposition.R95a.2" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R95a.2") : S1 := fun l => h l

@[sa_backward "CategoricalComposition.R95a.2"]
theorem bwd (s1 : S1) : sa_impl% "CategoricalComposition.R95a.2" := fun l => s1 l

end Alignment.Shadows.CategoricalComposition.R95a_2

/-! ## R96a (the implementation orders the hypotheses `0 < S₁, 0 < S₂, S₁ ≤ 1, S₂ ≤ 1`) -/
namespace Alignment.Shadows.CategoricalComposition.R96a

sa_claim "CategoricalComposition.R96a" group "CategoricalComposition" required
  text "**Result 96a.** Product susceptible fraction: S = S₁ · S₂. For layer susceptible fractions S₁ ∈ (0,1] and S₂ ∈ (0,1], the product S₁·S₂ ∈ (0,1]."
  impl product_susceptible_pos

@[sa_forward "CategoricalComposition.R96a" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R96a") : S1 :=
  fun a b ha0 ha1 hb0 hb1 => (h a b ha0 hb0 ha1 hb1).1

@[sa_forward "CategoricalComposition.R96a" 2]
theorem fwd2 (h : sa_impl% "CategoricalComposition.R96a") : S2 :=
  fun a b ha0 ha1 hb0 hb1 => (h a b ha0 hb0 ha1 hb1).2

@[sa_backward "CategoricalComposition.R96a"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "CategoricalComposition.R96a" :=
  fun a b ha0 hb0 ha1 hb1 => ⟨s1 a b ha0 ha1 hb0 hb1, s2 a b ha0 ha1 hb0 hb1⟩

end Alignment.Shadows.CategoricalComposition.R96a

/-! ## R96d -/
namespace Alignment.Shadows.CategoricalComposition.R96d

sa_claim "CategoricalComposition.R96d" group "CategoricalComposition" required
  text "**Result 96d.** A two-layer compact multiplex system has 3 ODEs."
  impl compact_multiplex_dim_two

@[sa_forward "CategoricalComposition.R96d" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R96d") : S1 := h

@[sa_backward "CategoricalComposition.R96d"]
theorem bwd (s1 : S1) : sa_impl% "CategoricalComposition.R96d" := s1

end Alignment.Shadows.CategoricalComposition.R96d

/-! ## R96e -/
namespace Alignment.Shadows.CategoricalComposition.R96e

sa_claim "CategoricalComposition.R96e" group "CategoricalComposition" required
  text "**Result 96e.** A three-layer compact multiplex system has 4 ODEs."
  impl compact_multiplex_dim_three

@[sa_forward "CategoricalComposition.R96e" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R96e") : S1 := h

@[sa_backward "CategoricalComposition.R96e"]
theorem bwd (s1 : S1) : sa_impl% "CategoricalComposition.R96e" := s1

end Alignment.Shadows.CategoricalComposition.R96e

/-! ## R96f

`MultiplexProduct.R0_sum p` unfolds to `p.layer1.T * (sf₁/mean₁) + p.layer2.T * (sf₂/mean₂)`,
which is the shadow's `T₁e₁ + T₂e₂`; the implementation is the identity implication, as the text
says ("Tautological Lean statement"). The counterexample sentences (S2–S4) are not stated by the
implementation. -/
namespace Alignment.Shadows.CategoricalComposition.R96f

sa_claim "CategoricalComposition.R96f" group "CategoricalComposition" required
  text "**Result 96f.** If the summed multiplex contribution is at most one, the sum is at most one. **Tautological Lean statement:** its hypothesis is its conclusion. The multiplex product itself need not be subcritical: for two 3-regular layers with T = 6/25 the sum is 24/25 but R₀ = ρ(K) = 6/5 (`multiplex_R0_sum_ne_spectral`)."
  impl product_subcritical

@[sa_forward "CategoricalComposition.R96f" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R96f") : S1 := fun p hp => h p hp

sa_fail_forward "CategoricalComposition.R96f" 2 "impl product_subcritical is the identity implication R0_sum ≤ 1 → R0_sum ≤ 1. It says nothing about the next-generation matrix K or its spectral radius, so it does not give S2 (some product with R0_sum ≤ 1 has ρ(K) > 1). The text attributes that example to multiplex_R0_sum_ne_spectral, which is not in this claim's impl list."

sa_fail_forward "CategoricalComposition.R96f" 3 "impl product_subcritical is the identity implication R0_sum ≤ 1 → R0_sum ≤ 1 and states no value of R0_sum; S3 (two 3-regular layers with T = 6/25 give R0_sum = 24/25) does not follow from it."

sa_fail_forward "CategoricalComposition.R96f" 4 "impl product_subcritical is the identity implication R0_sum ≤ 1 → R0_sum ≤ 1 and mentions no matrix or eigenvalue; S4 (ρ(K) = 6/5 for the 3-regular example) does not follow from it."

@[sa_backward "CategoricalComposition.R96f"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) : sa_impl% "CategoricalComposition.R96f" :=
  fun p hp => s1 p hp

end Alignment.Shadows.CategoricalComposition.R96f

/-! ## R96g -/
namespace Alignment.Shadows.CategoricalComposition.R96g

sa_claim "CategoricalComposition.R96g" group "CategoricalComposition" required
  text "**Result 96g.** If the first layer is supercritical, then the additive multiplex threshold is also supercritical."
  impl product_supercritical_left

@[sa_forward "CategoricalComposition.R96g" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R96g") : S1 := fun p hp => h p hp

@[sa_backward "CategoricalComposition.R96g"]
theorem bwd (s1 : S1) : sa_impl% "CategoricalComposition.R96g" := fun p hp => s1 p hp

end Alignment.Shadows.CategoricalComposition.R96g

/-! ## R97b -/
namespace Alignment.Shadows.CategoricalComposition.R97b

sa_claim "CategoricalComposition.R97b" group "CategoricalComposition" required
  text "**Result 97b.** The coproduct susceptible fraction at t=0 is 1 (everyone starts susceptible)."
  impl stratified_S_initial

@[sa_forward "CategoricalComposition.R97b" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R97b") : S1 := fun d => h d

@[sa_backward "CategoricalComposition.R97b"]
theorem bwd (s1 : S1) : sa_impl% "CategoricalComposition.R97b" := fun d => s1 d

end Alignment.Shadows.CategoricalComposition.R97b

/-! ## R97c (the implementation orders the hypotheses `0 ≤ S₁, 0 ≤ S₂, S₁ ≤ 1, S₂ ≤ 1`) -/
namespace Alignment.Shadows.CategoricalComposition.R97c

sa_claim "CategoricalComposition.R97c" group "CategoricalComposition" required
  text "**Result 97c.** The coproduct susceptible fraction is in [0,1] when each Si ∈ [0,1]."
  impl stratified_S_in_unit

@[sa_forward "CategoricalComposition.R97c" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R97c") : S1 :=
  fun d a b ha0 ha1 hb0 hb1 => (h d a b ha0 hb0 ha1 hb1).1

@[sa_forward "CategoricalComposition.R97c" 2]
theorem fwd2 (h : sa_impl% "CategoricalComposition.R97c") : S2 :=
  fun d a b ha0 ha1 hb0 hb1 => (h d a b ha0 hb0 ha1 hb1).2

@[sa_backward "CategoricalComposition.R97c"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "CategoricalComposition.R97c" :=
  fun d a b ha0 hb0 ha1 hb1 => ⟨s1 d a b ha0 ha1 hb0 hb1, s2 d a b ha0 ha1 hb0 hb1⟩

end Alignment.Shadows.CategoricalComposition.R97c

/-! ## R97d.1

The implementation is the reflexivity `d.layer1.dim + d.layer2.dim = d.layer1.dim + d.layer2.dim`.
Because it is a tautology it follows from anything (backward check proved by `rfl`), and it
cannot give the shadow's coproduct-dimension statement (forward check fails). -/
namespace Alignment.Shadows.CategoricalComposition.R97d_1

sa_claim "CategoricalComposition.R97d.1" group "CategoricalComposition" required
  text "**Result 97d.** The coproduct dimension is the sum of individual dimensions."
  impl stratified_dim

sa_fail_forward "CategoricalComposition.R97d.1" 1 "impl stratified_dim is the reflexivity d.layer1.dim + d.layer2.dim = d.layer1.dim + d.layer2.dim (proved by rfl) and defines no coproduct dimension, so it carries no information. S1 requires that the coproduct state space Fin dim₁ ⊕ Fin dim₂ has Fintype.card equal to dim₁ + dim₂. That is library content (Fintype.card_sum, Fintype.card_fin) which impl does not state, and no trusted coproduct-dimension definition exists that a bridge could identify. A proof could not use h (vacuous)."

@[sa_backward "CategoricalComposition.R97d.1"]
theorem bwd (_s1 : S1) : sa_impl% "CategoricalComposition.R97d.1" := fun _ => rfl

end Alignment.Shadows.CategoricalComposition.R97d_1

/-! ## R98a

The implementation inlines `T_erlang` with `n = 1` by hand, writing the literal `(1 : ℝ)` where
`T_erlang` has the cast `((d.n : ℕ) : ℝ)`. `((1 : ℕ) : ℝ) = 1` is `Nat.cast_one`, which is not
definitional in `ℝ` (checked: `rfl` and `with_unfolding_all rfl` fail), so neither direction is
structural. -/
namespace Alignment.Shadows.CategoricalComposition.R98a

sa_claim "CategoricalComposition.R98a" group "CategoricalComposition" required
  text "**Result 98a.** For n=1, the Erlang transmissibility equals the exponential transmissibility: T₁ = β/(β+γ)."
  impl stages_n1_recovers_exp

sa_fail_forward "CategoricalComposition.R98a" 1 "impl stages_n1_recovers_exp is a free-scalar identity, 1 - ((1:ℝ)·γ/(β + (1:ℝ)·γ))^1 = β/(β+γ) for β, γ > 0. It never mentions StagesNatTransData.T_erlang or T_exp. S1 requires d.n = 1 → d.T_erlang = d.T_exp. After rewriting d.n = 1, the unfolding of T_erlang contains the cast ((1:ℕ):ℝ) where impl has the literal (1:ℝ). ((1:ℕ):ℝ) = 1 is Nat.cast_one, a library lemma that is not definitional in ℝ (Real.one is irreducible; rfl fails). So S1 does not follow structurally from h. A faithful impl would state ∀ d, d.n = 1 → d.T_erlang = d.T_exp."

sa_fail_forward "CategoricalComposition.R98a" 2 "impl stages_n1_recovers_exp is stated over free reals β, γ with the literal (1:ℝ). S2 requires d.n = 1 → d.T_erlang = d.beta/(d.beta + d.gamma), and after rewriting d.n = 1 the unfolding of T_erlang has the cast ((1:ℕ):ℝ). Bridging the cast needs Nat.cast_one (a library lemma, not definitional in ℝ), so S2 does not follow structurally from h."

sa_fail_backward "CategoricalComposition.R98a" "impl is the n = 1 identity over free reals β, γ > 0 with the literal (1:ℝ). S1/S2 give the n = 1 statement only for d.T_erlang, whose unfolding (instantiated at ⟨β, γ, 1, …⟩) has the cast ((1:ℕ):ℝ) in place of (1:ℝ). Converting it needs Nat.cast_one (a library lemma, not definitional in ℝ), so impl does not follow structurally from the shadows."

end Alignment.Shadows.CategoricalComposition.R98a

/-! ## R98b.1 -/
namespace Alignment.Shadows.CategoricalComposition.R98b_1

sa_claim "CategoricalComposition.R98b.1" group "CategoricalComposition" required
  text "**Result 98b.** Excess-degree preservation: the excess degree ratio is independent of the number of stages (it depends only on the PGF)."
  impl stages_preserve_excess_degree

sa_fail_forward "CategoricalComposition.R98b.1" 1 "impl stages_preserve_excess_degree is the field-cancellation disjunction (T₁·e/e = T₁ ∧ T₂·e/e = T₂) ∨ e = 0 over free reals. It mentions no layer, PGF, excess-degree operation or stage count, so it does not state that the excess degree depends only on the PGF. S1 (layers with equal mean and ψ''(1) have equal excessDegree) holds by congruence on the definition of EBCMLayer.excessDegree, so a checker could only prove it without h (vacuous)."

sa_fail_backward "CategoricalComposition.R98b.1" "impl is a cancellation identity over arbitrary reals; proving it needs a case split on e = 0 and field lemmas (mul_div_cancel_right₀). S1 is a congruence about EBCMLayer.excessDegree and says nothing about cancelling a division, so impl does not follow structurally from S1: the two statements are about different notions."

end Alignment.Shadows.CategoricalComposition.R98b_1

/-! ## R98c.1 -/
namespace Alignment.Shadows.CategoricalComposition.R98c_1

sa_claim "CategoricalComposition.R98c.1" group "CategoricalComposition" required
  text "**Result 98c.** Mean infectious period is preserved: E[Erlang(n,nγ)] = 1/γ."
  impl stages_mean_preserved

sa_fail_forward "CategoricalComposition.R98c.1" 1 "impl stages_mean_preserved is the closed-form identity (n:ℝ)/((n:ℝ)·γ) = 1/γ for n > 0, γ > 0. S1 requires the expectation of Erlang(n, nγ) itself, ∫ x d(gammaMeasure n (n·γ)) = 1/γ. Linking the closed form n/(nγ) to that integral is the gamma-mean formula (library measure theory), which impl does not state. The Erlang distribution and its expectation are not formalised in the trusted library, so no bridge applies either."

sa_fail_backward "CategoricalComposition.R98c.1" "impl is the closed-form arithmetic identity n/(n·γ) = 1/γ. S1 speaks only about the integral ∫ x d(gammaMeasure n (n·γ)). Deriving the closed form from S1 needs ∫ x dΓ(n, nγ) = n/(nγ) (library content, not in the shadow), so impl does not follow structurally. The two statements are about different notions (a ratio of scalars vs an expectation)."

end Alignment.Shadows.CategoricalComposition.R98c_1

/-! ## R98d.1 (no shadow set: the blind author skipped this claim) -/
namespace Alignment.Shadows.CategoricalComposition.R98d_1

sa_claim "CategoricalComposition.R98d.1" group "CategoricalComposition" required
  text "**Result 98d.** Final-size equation: the final size equation θ∞ = 1 - T + T·g(θ∞) depends on T and the PGF g, not on the sojourn time distribution within the infectious period."
  impl stages_final_size_map

sa_fail_backward "CategoricalComposition.R98d.1" "No shadow set exists: the blind shadow author skipped the claim ('the only formal rendering of \"the equation depends on T and g only\" is a congruence, a tautology that no implementation can falsify'; the vocabulary has no sojourn-time distribution and no final size). impl stages_final_size_map is the ring identity 1 - T + T·g = 1 - T·(1 - g) over free reals and is silent about sojourn-time distributions, so the claim cannot pass as registered. Registrar question: reclassify as informal, or state a theorem over a staged model."

end Alignment.Shadows.CategoricalComposition.R98d_1

/-! ## R99a.3 -/
namespace Alignment.Shadows.CategoricalComposition.R99a_3

sa_claim "CategoricalComposition.R99a.3" group "CategoricalComposition" required
  text "The triangle stub fraction 2⟨t⟩/(2⟨t⟩+⟨s⟩) (called the clustering coefficient in ClusteringExtension; the clustering coefficient is 2⟨t⟩/⟨k(k−1)⟩) vanishes when ⟨t⟩ = 0."
  impl clustering_zero_is_identity

sa_fail_forward "CategoricalComposition.R99a.3" 1 "S1 is the defining equation of clustering_coefficient (it holds by rfl). impl clustering_zero_is_identity (2·0/(2·0 + ⟨s⟩) = 0 for a free rational ⟨s⟩ > 0) does not mention clustering_coefficient, so a checker could only prove S1 without h (vacuous). Remediation: add the defining equation to impl, or accept it as definitional."

sa_fail_forward "CategoricalComposition.R99a.3" 2 "impl is stated for a free rational ⟨s⟩ with the hypothesis 0 < ⟨s⟩. For d : ClusteredPGFData, S2 needs 0 < d.mean_single, which is the data invariant ClusteredPGFData.single_pos; a structural checker may not project it. impl does not state the vanishing for ClusteredPGFData itself (mathematically S2 follows from impl plus single_pos)."

@[sa_backward "CategoricalComposition.R99a.3"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "CategoricalComposition.R99a.3" :=
  fun ms hs => s2 ⟨ms, 0, 0, hs, le_refl 0⟩ rfl

end Alignment.Shadows.CategoricalComposition.R99a_3

/-! ## R99b.1 -/
namespace Alignment.Shadows.CategoricalComposition.R99b_1

sa_claim "CategoricalComposition.R99b.1" group "CategoricalComposition" required
  text "**Result 99b.** The clustered R₀ reduces to the standard R₀ when there are no triangle edges (⟨t⟩ = 0). [...] When ⟨t⟩ = 0: R₀_clustered = T·excess_single = R₀_standard."
  impl clustering_zero_R0

sa_fail_forward "CategoricalComposition.R99b.1" 1 "impl clustering_zero_R0 is a ℚ ring identity over free scalars, T·e + T·(2·0/(e + 2·0))·(1+T) = T·e. The formula's ⟨s⟩ is replaced by excess_s and ⟨t⟩ is the literal 0. S1 is ∀ l : EBCMLayer, l.R0 = l.T · l.excessDegree over ℝ, which holds by definition (rfl) and cannot be obtained from h (different number type, no EBCMLayer, no R0). Any proof of S1 would ignore h (vacuous). Neither statement connects a clustered R₀ to EBCMLayer.R0."

sa_fail_backward "CategoricalComposition.R99b.1" "impl is a ℚ identity for arbitrary T and excess_s. Proving it needs ring normalisation (2·0 = 0, 0/x = 0, T·0·(1+T) = 0, a + 0 = a). S1 is the definitional unfolding of EBCMLayer.R0 over ℝ and gives no ℚ arithmetic, so impl does not follow structurally from S1."

end Alignment.Shadows.CategoricalComposition.R99b_1

/-! ## R100a -/
namespace Alignment.Shadows.CategoricalComposition.R100a

sa_claim "CategoricalComposition.R100a" group "CategoricalComposition" required
  text "**Result 100a.** Left unitality: the trivial layer is a left unit for the susceptible product. S_unit · S = 1 · S = S."
  impl monoidal_left_unit

@[sa_forward "CategoricalComposition.R100a" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R100a") : S1 := fun S => h S

@[sa_backward "CategoricalComposition.R100a"]
theorem bwd (s1 : S1) : sa_impl% "CategoricalComposition.R100a" := fun S => s1 S

end Alignment.Shadows.CategoricalComposition.R100a

/-! ## R100b -/
namespace Alignment.Shadows.CategoricalComposition.R100b

sa_claim "CategoricalComposition.R100b" group "CategoricalComposition" required
  text "**Result 100b.** Right unitality: S · S_unit = S · 1 = S."
  impl monoidal_right_unit

@[sa_forward "CategoricalComposition.R100b" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R100b") : S1 := fun S => h S

@[sa_backward "CategoricalComposition.R100b"]
theorem bwd (s1 : S1) : sa_impl% "CategoricalComposition.R100b" := fun S => s1 S

end Alignment.Shadows.CategoricalComposition.R100b

/-! ## R100c -/
namespace Alignment.Shadows.CategoricalComposition.R100c

sa_claim "CategoricalComposition.R100c" group "CategoricalComposition" required
  text "**Result 100c.** Associativity of the multiplex product: (S₁ · S₂) · S₃ = S₁ · (S₂ · S₃)."
  impl monoidal_assoc

@[sa_forward "CategoricalComposition.R100c" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R100c") : S1 :=
  fun a b c => h a b c

@[sa_backward "CategoricalComposition.R100c"]
theorem bwd (s1 : S1) : sa_impl% "CategoricalComposition.R100c" :=
  fun a b c => s1 a b c

end Alignment.Shadows.CategoricalComposition.R100c

/-! ## R100d -/
namespace Alignment.Shadows.CategoricalComposition.R100d

sa_claim "CategoricalComposition.R100d" group "CategoricalComposition" required
  text "**Result 100d.** The product ODE dimension is associative: (d₁ + d₂) + d₃ = d₁ + (d₂ + d₃)."
  impl monoidal_dim_assoc

@[sa_forward "CategoricalComposition.R100d" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R100d") : S1 :=
  fun a b c => h a b c

@[sa_backward "CategoricalComposition.R100d"]
theorem bwd (s1 : S1) : sa_impl% "CategoricalComposition.R100d" :=
  fun a b c => s1 a b c

end Alignment.Shadows.CategoricalComposition.R100d

/-! ## R100e -/
namespace Alignment.Shadows.CategoricalComposition.R100e

sa_claim "CategoricalComposition.R100e" group "CategoricalComposition" required
  text "**Result 100e.** The unit dimension is 0 (trivial ODE system): 0 + d = d and d + 0 = d."
  impl monoidal_dim_unit_left monoidal_dim_unit_right

@[sa_forward "CategoricalComposition.R100e" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R100e") : S1 := h.1

@[sa_forward "CategoricalComposition.R100e" 2]
theorem fwd2 (h : sa_impl% "CategoricalComposition.R100e") : S2 := h.2

@[sa_backward "CategoricalComposition.R100e"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "CategoricalComposition.R100e" := ⟨s1, s2⟩

end Alignment.Shadows.CategoricalComposition.R100e

/-! ## R100f.1 -/
namespace Alignment.Shadows.CategoricalComposition.R100f_1

sa_claim "CategoricalComposition.R100f.1" group "CategoricalComposition" required
  text "**Result 100f.** The real-number identities that the pentagon and triangle identities would reduce to hold (no associator or unitor is defined)."
  impl monoidal_pentagon monoidal_triangle

@[sa_forward "CategoricalComposition.R100f.1" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R100f.1") : S1 :=
  fun a b c d => h.1 a b c d

@[sa_forward "CategoricalComposition.R100f.1" 2]
theorem fwd2 (h : sa_impl% "CategoricalComposition.R100f.1") : S2 :=
  fun a b => h.2 a b

@[sa_backward "CategoricalComposition.R100f.1"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "CategoricalComposition.R100f.1" :=
  ⟨fun a b c d => s1 a b c d, fun a b => s2 a b⟩

end Alignment.Shadows.CategoricalComposition.R100f_1

/-! ## R101a -/
namespace Alignment.Shadows.CategoricalComposition.R101a

sa_claim "CategoricalComposition.R101a" group "CategoricalComposition" required
  text "**Result 101a.** R₀ is monotone in transmissibility: if T₁ ≤ T₂ and the excess degree is the same, then R₀(T₁) ≤ R₀(T₂)."
  impl R0_monotone_in_T

sa_fail_forward "CategoricalComposition.R101a" 1 "impl R0_monotone_in_T requires 0 ≤ excessDeg (hypothesis he), which neither the text nor S1 assumes. impl is a free-scalar inequality T₁·e ≤ T₂·e and is not stated for layers. For EBCMLayers, 0 ≤ l.excessDegree = sf/mean holds only through the data invariants sf_nonneg and mean_pos plus div_nonneg (a library lemma), none of which a structural checker may use, so S1 does not follow structurally from h. A faithful impl would be stated over EBCMLayer."

sa_fail_backward "CategoricalComposition.R101a" "impl holds for arbitrary reals T₁ ≤ T₂ (including T ≤ 0 or T > 1) and every e ≥ 0. S1 covers only EBCMLayers (0 < T ≤ 1, e = sf/mean), and no layer has T or excessDegree definitionally equal to an arbitrary real. The free-scalar impl is strictly more general than S1, so it does not follow from the shadow."

end Alignment.Shadows.CategoricalComposition.R101a

/-! ## R101b -/
namespace Alignment.Shadows.CategoricalComposition.R101b

sa_claim "CategoricalComposition.R101b" group "CategoricalComposition" required
  text "**Result 101b.** Strict monotonicity when excessDeg > 0."
  impl R0_strict_monotone_in_T

/-- `l.R0` unfolds to `l.T * l.excessDegree`; rewrite the second layer's excess degree to the
first's and apply the implementation at `e = l₁.excessDegree`. -/
@[sa_forward "CategoricalComposition.R101b" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R101b") : S1 := by
  intro l₁ l₂ hT he hpos
  show l₁.T * l₁.excessDegree < l₂.T * l₂.excessDegree
  rw [← he]
  exact h l₁.T l₂.T l₁.excessDegree hT hpos

sa_fail_backward "CategoricalComposition.R101b" "impl holds for arbitrary reals T₁ < T₂ (including values outside (0,1]) and every e > 0. S1 covers only EBCMLayers (0 < T ≤ 1, e = sf/mean), and arbitrary reals are not definitionally the T or excessDegree of some layer. The free-scalar impl is strictly more general than S1, so it does not follow from the shadow."

end Alignment.Shadows.CategoricalComposition.R101b

/-! ## R101c -/
namespace Alignment.Shadows.CategoricalComposition.R101c

sa_claim "CategoricalComposition.R101c" group "CategoricalComposition" required
  text "**Result 101c.** R₀ = 0 when T = 0 (no transmission)."
  impl R0_zero_at_T_zero

/-- `R0atT 0 l` unfolds to `0 * l.excessDegree`. -/
@[sa_forward "CategoricalComposition.R101c" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R101c") : S1 := fun l => h l.excessDegree

sa_fail_backward "CategoricalComposition.R101c" "impl is 0·e = 0 for every real e. S1 (R0atT 0 l = 0) gives it only for e = l.excessDegree = sf/mean ≥ 0 of some layer, and no layer's excessDegree is definitionally an arbitrary real (e.g. a negative e). The free-scalar impl is strictly more general than S1."

end Alignment.Shadows.CategoricalComposition.R101c

/-! ## R101d -/
namespace Alignment.Shadows.CategoricalComposition.R101d

sa_claim "CategoricalComposition.R101d" group "CategoricalComposition" required
  text "**Result 101d.** R₀ = excessDeg when T = 1 (complete transmission)."
  impl R0_at_T_one

/-- `l.R0` unfolds to `l.T * l.excessDegree`; rewrite `l.T = 1`. -/
@[sa_forward "CategoricalComposition.R101d" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R101d") : S1 := by
  intro l hT
  show l.T * l.excessDegree = l.excessDegree
  rw [hT]
  exact h l.excessDegree

sa_fail_backward "CategoricalComposition.R101d" "impl is 1·e = e for every real e. S1 (l.T = 1 → l.R0 = l.excessDegree) gives it only for e = sf/mean ≥ 0 of a layer with T = 1, and an arbitrary (e.g. negative) real is not definitionally such an excess degree. The free-scalar impl is strictly more general than S1."

end Alignment.Shadows.CategoricalComposition.R101d

/-! ## R101e -/
namespace Alignment.Shadows.CategoricalComposition.R101e

sa_claim "CategoricalComposition.R101e" group "CategoricalComposition" required
  text "**Result 101e.** Monotonicity of R₀ in the excess degree: if e₁ ≤ e₂ and T ≥ 0, then T·e₁ ≤ T·e₂."
  impl R0_monotone_in_excess

@[sa_forward "CategoricalComposition.R101e" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R101e") : S1 :=
  fun τ e₁ e₂ he hτ => h τ e₁ e₂ hτ he

sa_fail_forward "CategoricalComposition.R101e" 2 "impl R0_monotone_in_excess is stated for free reals with the hypothesis 0 ≤ T. For layers, S2 needs 0 ≤ l₂.T, which follows only from the data invariant EBCMLayer.T_pos via le_of_lt; a structural checker may use neither. impl does not state the layer-level monotonicity of EBCMLayer.R0 (mathematically S2 follows from impl plus T_pos)."

@[sa_backward "CategoricalComposition.R101e"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "CategoricalComposition.R101e" :=
  fun τ e₁ e₂ hτ he => s1 τ e₁ e₂ he hτ

end Alignment.Shadows.CategoricalComposition.R101e

/-! ## meanDegPos -/
namespace Alignment.Shadows.CategoricalComposition.meanDegPos

sa_claim "CategoricalComposition.meanDegPos" group "CategoricalComposition" required
  text "Mean degree is positive."
  impl MixingPullbackData.meanDeg_pos

@[sa_forward "CategoricalComposition.meanDegPos" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.meanDegPos") : S1 := fun d => h d

@[sa_backward "CategoricalComposition.meanDegPos"]
theorem bwd (s1 : S1) : sa_impl% "CategoricalComposition.meanDegPos" := fun d => s1 d

end Alignment.Shadows.CategoricalComposition.meanDegPos

/-! ## R102a.3 -/
namespace Alignment.Shadows.CategoricalComposition.R102a_3

sa_claim "CategoricalComposition.R102a.3" group "CategoricalComposition" required
  text "We verify that for any r, the r=0 specialization gives q₁."
  impl neutral_is_terminal_q1

sa_fail_forward "CategoricalComposition.R102a.3" 1 "impl neutral_is_terminal_q1 is k₁·(0 + (1-0)·q₁) = k₁·q₁ over free reals: the r = 0 value of the entry k₁·P(1|1), multiplied by k₁. S1 requires that the r-dependent quantity itself, P(1|1) = r + (1-r)·q₁, equals q₁ at r = 0 (text: 'the r=0 specialization gives q₁'). Removing the factor k₁ needs cancellation (k₁ ≠ 0, mul_left_cancel₀) or one_mul at k₁ = 1, library content that impl does not state. impl says the specialisation gives k₁·q₁, not q₁."

sa_fail_backward "CategoricalComposition.R102a.3" "impl holds for arbitrary reals k₁, q₁. S1 gives 0 + (1-0)·q₁ = q₁ only for q₁ = d.q1 = k₁p₁/⟨k⟩ of a mixing datum, never for an arbitrary real q₁, so the free-scalar impl is strictly more general than S1 and does not follow from it (multiplying by k₁ would be congrArg, but the q₁ gap remains)."

end Alignment.Shadows.CategoricalComposition.R102a_3

/-! ## R102b -/
namespace Alignment.Shadows.CategoricalComposition.R102b

sa_claim "CategoricalComposition.R102b" group "CategoricalComposition" required
  text "**Result 102b.** At r=0, the off-diagonal mixing entry k₁·(1-r)·q₂ reduces to k₁·q₂, the neutral mixing value."
  impl pullback_neutral_offdiag

@[sa_forward "CategoricalComposition.R102b" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R102b") : S1 := by
  intro d hr
  rw [hr]
  exact h d

/-- The implementation's statement does not involve `d.r`, and `d.k1`, `d.q2` do not depend on
`r`; apply the shadow to `d` with its assortativity set to `0` (the proof fields of the new datum
are data arguments). -/
@[sa_backward "CategoricalComposition.R102b"]
theorem bwd (s1 : S1) : sa_impl% "CategoricalComposition.R102b" := fun d =>
  s1 ⟨d.k1, d.k2, d.p1, d.p2, 0, d.k1_pos, d.k2_pos, d.p1_pos, d.p2_pos, d.p_sum,
    le_refl 0, zero_le_one⟩ rfl

end Alignment.Shadows.CategoricalComposition.R102b

/-! ## R102c.2 -/
namespace Alignment.Shadows.CategoricalComposition.R102c_2

sa_claim "CategoricalComposition.R102c.2" group "CategoricalComposition" required
  text "We verify that the r=0 specialization of every mixing entry recovers the neutral form."
  impl pullback_C11_neutral pullback_C12_neutral pullback_C21_neutral pullback_C22_neutral

@[sa_forward "CategoricalComposition.R102c.2" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.R102c.2") : S1 := by
  intro d hr
  show d.k1 * (d.r + (1 - d.r) * d.q1) = d.k1 * d.q1
  rw [hr]
  exact h.1 d.k1 d.q1

@[sa_forward "CategoricalComposition.R102c.2" 2]
theorem fwd2 (h : sa_impl% "CategoricalComposition.R102c.2") : S2 := by
  intro d hr
  show d.k1 * (1 - d.r) * d.q2 = d.k1 * d.q2
  rw [hr]
  exact h.2.1 d.k1 d.q2

@[sa_forward "CategoricalComposition.R102c.2" 3]
theorem fwd3 (h : sa_impl% "CategoricalComposition.R102c.2") : S3 := by
  intro d hr
  show d.k2 * (1 - d.r) * d.q1 = d.k2 * d.q1
  rw [hr]
  exact h.2.2.1 d.k2 d.q1

@[sa_forward "CategoricalComposition.R102c.2" 4]
theorem fwd4 (h : sa_impl% "CategoricalComposition.R102c.2") : S4 := by
  intro d hr
  show d.k2 * (d.r + (1 - d.r) * d.q2) = d.k2 * d.q2
  rw [hr]
  exact h.2.2.2 d.k2 d.q2

sa_fail_backward "CategoricalComposition.R102c.2" "impl is four identities over arbitrary reals (k and q free, r the literal 0). S1–S4 give them only for k = d.kᵢ and q = d.qⱼ = kⱼpⱼ/⟨k⟩ of mixing data, and an arbitrary real q is not definitionally some d.qⱼ. The free-scalar impl is strictly more general than the shadows, so it does not follow from them."

end Alignment.Shadows.CategoricalComposition.R102c_2

/-! ## R102d.2 -/
namespace Alignment.Shadows.CategoricalComposition.R102d_2

sa_claim "CategoricalComposition.R102d.2" group "CategoricalComposition" required
  text "We verify that det(C_neutral) = 0 for 2×2."
  impl neutral_mixing_det_zero

sa_fail_forward "CategoricalComposition.R102d.2" 1 "impl neutral_mixing_det_zero requires q₁ + q₂ = 1 (hypothesis _hq, unused in its proof), which S1 does not assume. For MixingPullbackData, d.q1 + d.q2 = k₁p₁/⟨k⟩ + k₂p₂/⟨k⟩ = 1 needs field lemmas (div_add_div_same, div_self with meanDeg ≠ 0 from meanDeg_pos), not structural reasoning, so S1 does not follow structurally from h."

sa_fail_backward "CategoricalComposition.R102d.2" "impl holds for arbitrary reals k₁, k₂, q₁, q₂ with q₁ + q₂ = 1. S1 gives the determinant identity only for k = d.kᵢ and q = d.qⱼ of mixing data, and arbitrary reals are not definitionally of that form. The free-scalar impl is strictly more general than S1."

end Alignment.Shadows.CategoricalComposition.R102d_2

/-! ## R102e.1 -/
namespace Alignment.Shadows.CategoricalComposition.R102e_1

sa_claim "CategoricalComposition.R102e.1" group "CategoricalComposition" required
  text "**Result 102e.** Pullback compatibility: the degree-correlated model recovers the uncorrelated R₀ when r=0."
  impl pullback_R0_at_neutral

sa_fail_forward "CategoricalComposition.R102e.1" 1 "impl pullback_R0_at_neutral is the re-association T·A/B = T·(A/B) over free reals, with A = k₁²p₁ + k₂²p₂ and B = k₁p₁ + k₂p₂ > 0. It mentions no degree-correlated model, next-generation matrix, eigenvalue or assortativity r. S1 requires that R0uncorr d τ = τ·⟨k(k−1)⟩/⟨k⟩ is an eigenvalue of ngm d τ at r = 0, which h does not state. impl's quantity also uses ⟨k²⟩/⟨k⟩ rather than ⟨k(k−1)⟩/⟨k⟩, so it is not even the uncorrelated R₀."

sa_fail_forward "CategoricalComposition.R102e.1" 2 "impl pullback_R0_at_neutral says nothing about eigenvalues: it is only the re-association T·A/B = T·(A/B). S2 requires every eigenvalue of the degree-correlated next-generation matrix ngm d τ at r = 0 to be at most R0uncorr d τ, and that does not follow from h."

sa_fail_backward "CategoricalComposition.R102e.1" "impl is a field identity T·A/B = T·(A/B) over arbitrary reals (proved by field_simp). S1/S2 are eigenvalue statements about ngm for mixing data and give no information about this re-association, so impl does not follow structurally from the shadows. The two are about different notions."

end Alignment.Shadows.CategoricalComposition.R102e_1

/-! ## r0SumEqTrace -/
namespace Alignment.Shadows.CategoricalComposition.r0SumEqTrace

sa_claim "CategoricalComposition.r0SumEqTrace" group "CategoricalComposition" required
  text "The additive rule `R0_sum` is the trace of the multiplex next-generation matrix K."
  impl MultiplexProduct.R0_sum_eq_trace

sa_fail_forward "CategoricalComposition.r0SumEqTrace" 1 "impl MultiplexProduct.R0_sum_eq_trace states R0_sum = K11 + K22. S1 states R0_sum = Matrix.trace (Kmp p), a Finset sum over Fin 2 that unfolds to K11 + (K22 + 0); x + 0 = x is not definitional in ℝ, and the two agree only by the library lemma Matrix.trace_fin_two (or add_zero). A structural checker may not use it, and no bridge applies because Matrix.trace is not a trusted definition. The mathematical content is the same."

sa_fail_backward "CategoricalComposition.r0SumEqTrace" "S1 gives R0_sum = Matrix.trace (Kmp p); impl needs R0_sum = K11 + K22. The trace is a Finset sum over Fin 2 that reduces to K11 + (K22 + 0), and removing + 0 in ℝ needs add_zero / Matrix.trace_fin_two, which a structural checker may not use (no trusted definition to bridge). Same mathematical content, not structurally derivable."

end Alignment.Shadows.CategoricalComposition.r0SumEqTrace

/-! ## multiplexR0SumNeSpectral

The implementation is existential (one witness `⟨threeRegularLayer, threeRegularLayer⟩`) and
states row sums and differences of `K`; the shadows are universal over all products of two
3-regular layers with `T = 6/25` and state `K` entrywise, its eigen-equations and ρ(K). -/
namespace Alignment.Shadows.CategoricalComposition.multiplexR0SumNeSpectral

sa_claim "CategoricalComposition.multiplexR0SumNeSpectral" group "CategoricalComposition" required
  text "**The additive multiplex R₀ is not the spectral radius.** For two 3-regular layers with T = 6/25, K = [[12/25, 18/25], [18/25, 12/25]] has the eigenvectors (1, 1) with eigenvalue 6/5 and (1, −1) with eigenvalue −6/25, so ρ(K) = 6/5 > 1, while `R0_sum` = 24/25 < 1."
  impl multiplex_R0_sum_ne_spectral

sa_fail_forward "CategoricalComposition.multiplexR0SumNeSpectral" 1 "impl multiplex_R0_sum_ne_spectral is existential: ∃ p with K11 + K12 = 6/5, K21 + K22 = 6/5, K11 - K12 = -6/25, K21 - K22 = 6/25 and R0_sum = 24/25. S1 is universal (every product of two 3-regular layers with T = 6/25 has K = [[12/25, 18/25], [18/25, 12/25]]); an existential does not give a universal statement, and the witness's layers are not named in impl's statement."

sa_fail_forward "CategoricalComposition.multiplexR0SumNeSpectral" 2 "impl is existential over p; S2 (K(1,1) = (6/5)(1,1)) is universal over all products of two 3-regular layers with T = 6/25, so it does not follow. Even for the witness, turning the row sum K11 + K12 = 6/5 into Matrix.mulVec needs Finset-sum and mul_one lemmas, which are not structural."

sa_fail_forward "CategoricalComposition.multiplexR0SumNeSpectral" 3 "impl is existential over p; S3 (K(1,-1) = (-6/25)(1,-1)) is universal over all products of two 3-regular layers with T = 6/25, so it does not follow; converting K11 - K12 = -6/25 into a Matrix.mulVec equation would also need library lemmas."

sa_fail_forward "CategoricalComposition.multiplexR0SumNeSpectral" 4 "impl states no eigenvalue or spectral-radius property: it gives row sums and differences of K for one witness p. S4 (6/5 is an eigenvalue of K and bounds every real eigenvalue, for every product of two 3-regular layers with T = 6/25) needs eigenvalue theory and the universal quantifier; impl is weaker."

sa_fail_forward "CategoricalComposition.multiplexR0SumNeSpectral" 5 "impl gives R0_sum = 24/25 only for its existential witness p. S5 is universal over every product of two 3-regular layers with T = 6/25; an existential does not give it."

sa_fail_backward "CategoricalComposition.multiplexR0SumNeSpectral" "Mathematically S1 and S5 give impl with the witness ⟨threeRegularLayer, threeRegularLayer⟩ (its threeReg hypotheses hold by rfl). But from K = [[12/25, 18/25], [18/25, 12/25]] the conjunct K11 + K12 = 6/5 needs the closed real arithmetic 12/25 + 18/25 = 6/5 (norm_num), and similarly for the other row sums and differences. That is not structural, and no bridge applies because the gap is arithmetic on numerals, not a trusted definition."

end Alignment.Shadows.CategoricalComposition.multiplexR0SumNeSpectral

/-! ## stagesChangeTransmissibility -/
namespace Alignment.Shadows.CategoricalComposition.stagesChangeTransmissibility

sa_claim "CategoricalComposition.stagesChangeTransmissibility" group "CategoricalComposition" required
  text "Staging changes the transmissibility: with n = 2 stages, T_exp = β/(β+γ) < T_2 = 1 − (2γ/(β+2γ))², since the difference is β²γ/((β+γ)(β+2γ)²) > 0."
  impl stages_change_transmissibility

@[sa_forward "CategoricalComposition.stagesChangeTransmissibility" 1]
theorem fwd1 (h : sa_impl% "CategoricalComposition.stagesChangeTransmissibility") : S1 :=
  fun d hn => h d hn

sa_fail_forward "CategoricalComposition.stagesChangeTransmissibility" 2 "S2 is the defining equation of StagesNatTransData.T_exp (it holds by rfl). impl stages_change_transmissibility (n = 2 → T_exp < T_erlang) does not state it, so a checker could only prove S2 without h (vacuous). Remediation: add the defining equation to impl, or accept it as definitional."

sa_fail_forward "CategoricalComposition.stagesChangeTransmissibility" 3 "S3 (for n = 2, T_erlang = 1 - (2γ/(β+2γ))²) is the definition of StagesNatTransData.T_erlang after rewriting n = 2 (it holds by rw and rfl). impl states only the strict inequality T_exp < T_erlang, so a checker could only prove S3 without h (vacuous)."

sa_fail_forward "CategoricalComposition.stagesChangeTransmissibility" 4 "impl states only the strict inequality T_exp < T_erlang for n = 2. S4 is the closed form of the difference, T_erlang - T_exp = β²γ/((β+γ)(β+2γ)²); it appears only inside impl's proof (the local fact `key`), not in its statement, so impl is weaker than S4."

@[sa_backward "CategoricalComposition.stagesChangeTransmissibility"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) :
    sa_impl% "CategoricalComposition.stagesChangeTransmissibility" :=
  fun d hn => s1 d hn

end Alignment.Shadows.CategoricalComposition.stagesChangeTransmissibility

/-! ## `CategoricalComposition.R100.monoidal` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.CategoricalComposition.R100_monoidal

sa_claim "CategoricalComposition.R100.monoidal" group "CategoricalComposition"
  text "The multiplex product of layers (Result 96) behaves like a monoidal product on susceptible fractions and dimensions (informal: no category is defined). Its unit is the trivial network: degree 0, no edges."
  impl

end Alignment.Shadows.CategoricalComposition.R100_monoidal

/-! ## `CategoricalComposition.R102.terminal` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.CategoricalComposition.R102_terminal

sa_claim "CategoricalComposition.R102.terminal" group "CategoricalComposition"
  text "Neutral mixing (Q(l|k) = l·pₗ/⟨k⟩) is the special case r = 0 of the assortative family below; no category of mixing matrices, and so no terminal object, is defined."
  impl

end Alignment.Shadows.CategoricalComposition.R102_terminal

/-! ## `CategoricalComposition.R102a.1` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.CategoricalComposition.R102a_1

sa_claim "CategoricalComposition.R102a.1" group "CategoricalComposition"
  text "**Result 102a.** Neutral mixing: when r=0, the mixing matrix Q(l|k) = q_l is independent of k."
  impl

end Alignment.Shadows.CategoricalComposition.R102a_1

/-! ## `CategoricalComposition.R102c.1` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.CategoricalComposition.R102c_1

sa_claim "CategoricalComposition.R102c.1" group "CategoricalComposition"
  text "**Result 102c.** The r = 0 specialisation of the assortative mixing matrix."
  impl

end Alignment.Shadows.CategoricalComposition.R102c_1

/-! ## `CategoricalComposition.R102d.1` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.CategoricalComposition.R102d_1

sa_claim "CategoricalComposition.R102d.1" group "CategoricalComposition"
  text "**Result 102d.** The neutral mixing matrix is rank-1 (det = 0): it factors through the degree distribution."
  impl

end Alignment.Shadows.CategoricalComposition.R102d_1

/-! ## `CategoricalComposition.R102e.2` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.CategoricalComposition.R102e_2

sa_claim "CategoricalComposition.R102e.2" group "CategoricalComposition"
  text "For r=0, the largest eigenvalue of C = k·Q equals ⟨k²⟩/⟨k⟩, which is one more than the largest eigenvalue ⟨k²-k⟩/⟨k⟩ of the next-generation matrix K = (k-1)·Q; R₀ = T·⟨k²-k⟩/⟨k⟩ is the standard uncorrelated formula (DegreeCorrelation `neutral_traceK`). The Lean statement below is the field identity T·a/b = T·(a/b), with a/b = ⟨k²⟩/⟨k⟩."
  impl

end Alignment.Shadows.CategoricalComposition.R102e_2

/-! ## `CategoricalComposition.R96b` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.CategoricalComposition.R96b

sa_claim "CategoricalComposition.R96b" group "CategoricalComposition"
  text "**Result 96b.** The product dimension is defined as the sum of the layer dimensions; the compact multiplex system needs fewer ODEs (one θ-equation per layer plus one recovery equation, `compactMultiplexDim`)."
  impl

end Alignment.Shadows.CategoricalComposition.R96b

/-! ## `CategoricalComposition.R96c` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.CategoricalComposition.R96c

sa_claim "CategoricalComposition.R96c" group "CategoricalComposition"
  text "**Result 96c.** The sum T₁e₁ + T₂e₂ of the per-layer R₀ values; it matches the former compact implementation in `src/multiplex.jl`. It is not the R₀ of independent multiplex layers, which is ρ(K) with K = [[T₁e₁, T₁⟨k₁⟩], [T₂⟨k₂⟩, T₂e₂]] and eᵢ = ψᵢ''(1)/ψᵢ'(1) (`MultiplexProduct.K11` …). The sum T₁e₁ + T₂e₂ equals ρ(K) iff det K = 0, i.e. e₁e₂ = ⟨k₁⟩⟨k₂⟩, for example for two Poisson layers; it underestimates ρ(K) when e₁e₂ < ⟨k₁⟩⟨k₂⟩. Two 3-regular layers with T = 6/25 give sum 24/25 but ρ(K) = 6/5 (`multiplex_R0_sum_ne_spectral`)."
  impl

end Alignment.Shadows.CategoricalComposition.R96c

/-! ## `CategoricalComposition.R97a.2` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.CategoricalComposition.R97a_2

sa_claim "CategoricalComposition.R97a.2" group "CategoricalComposition"
  text "It is a convex combination of the type susceptible fractions, not a coproduct injection."
  impl

end Alignment.Shadows.CategoricalComposition.R97a_2

/-! ## `CategoricalComposition.R98.keyProperty` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.CategoricalComposition.R98_keyProperty

sa_claim "CategoricalComposition.R98.keyProperty" group "CategoricalComposition"
  text "Key property: η_n preserves the PGF and the mean infectious period. T_n = 1 − (nγ/(β+nγ))^n increases with n towards 1 − exp(−β/γ), so R₀ and the final size change (`stages_change_transmissibility`)."
  impl

end Alignment.Shadows.CategoricalComposition.R98_keyProperty

/-! ## `CategoricalComposition.R98b.3` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.CategoricalComposition.R98b_3

sa_claim "CategoricalComposition.R98b.3" group "CategoricalComposition"
  text "The map η_n sends T_exp to T_n and keeps the PGF."
  impl

end Alignment.Shadows.CategoricalComposition.R98b_3

/-! ## `CategoricalComposition.R98c.2` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.CategoricalComposition.R98c_2

sa_claim "CategoricalComposition.R98c.2" group "CategoricalComposition"
  text "It is the identity that fixes the sub-stage rate nγ."
  impl

end Alignment.Shadows.CategoricalComposition.R98c_2

/-! ## `CategoricalComposition.R99a.2` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.CategoricalComposition.R99a_2

sa_claim "CategoricalComposition.R99a.2" group "CategoricalComposition"
  text "So the clustered model with no triangles is the standard model."
  impl

end Alignment.Shadows.CategoricalComposition.R99a_2

/-! ## `CategoricalComposition.R99b.2` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.CategoricalComposition.R99b_2

sa_claim "CategoricalComposition.R99b.2" group "CategoricalComposition"
  text "The scalar `clustered_R0` = T·excess_single + T·(2⟨t⟩/(⟨s⟩+2⟨t⟩))·(1+T) is not the R₀ of a clustered network (ClusteringExtension, Result 72)."
  impl

end Alignment.Shadows.CategoricalComposition.R99b_2
