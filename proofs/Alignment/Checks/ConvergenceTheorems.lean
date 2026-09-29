import Alignment.Registry
import Alignment.Shadows.ConvergenceTheorems

/-!
# Checkers: group `ConvergenceTheorems`

Registrations, checkers and failure records for the implemented claims of
`EBCMCategory/ConvergenceTheorems.lean` (shadows: `Alignment/Shadows/ConvergenceTheorems.lean`,
written blind).

**No bridges.** Every identification of a trusted definition with the text's notion that the
checkers use is definitional:
`PGFMoments.excessDegree m ≡ m.secondFactorial / m.mean`,
`R0_heterogeneous T m ≡ T * m.excessDegree`, `R0_homogeneous T k ≡ T * (k - 1)`,
`criticalTransmissibility m h ≡ m.mean / m.secondFactorial`,
`(poissonMoments κ hκ).mean ≡ κ`, `(poissonMoments κ hκ).secondFactorial ≡ κ ^ 2`,
`Function.IsFixedPt f x ≡ f x = x`, and proof irrelevance for the positivity argument of
`criticalTransmissibility`. The only candidate bridge, `excessDegree m = (secondMoment m - mean)/mean`
for Result 107b, would restate Result 107a (theorem content, not a definition) and is not written.

Policy for the recorded failures (the same as the other groups):
* A shadow that holds by a *definition* alone (e.g. `R₀(homogeneous) = T·(⟨k⟩-1)`,
  `R₀ = T·excessDeg`, `T_c = ⟨k⟩/⟨k(k-1)⟩`, Poisson `ψ''(1)/ψ'(1) = κ²/κ`) is recorded as
  `sa_fail_forward` ("impl does not assert …") when the claim's implementation does not itself
  state it: a checker could only be vacuous or thread `h` through spuriously.
* Discharging an impl hypothesis from a structure field (`d.beta_tilde_pos`, `m.mean_pos`, …) is a
  data invariant, and real arithmetic/order facts need library lemmas; neither is structural.
* Tautological implementations (`κ·S = κ·S`, `T·e = T·e`, `P ↔ P`) cannot yield any shadow that
  mentions `exp`, a derivative or `|·|`; their backward checks hold by `rfl`/`Iff.rfl`.
-/

/-! ## `ConvergenceTheorems.effectiveBetaPos` -/
namespace Alignment.Shadows.ConvergenceTheorems.effectiveBetaPos

sa_claim "ConvergenceTheorems.effectiveBetaPos" group "ConvergenceTheorems" required
  text "Effective β is positive."
  impl effective_beta_pos

@[sa_forward "ConvergenceTheorems.effectiveBetaPos" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.effectiveBetaPos") : S1 :=
  fun d => h d

@[sa_backward "ConvergenceTheorems.effectiveBetaPos"]
theorem bwd (s1 : S1) : sa_impl% "ConvergenceTheorems.effectiveBetaPos" :=
  fun d => s1 d

end Alignment.Shadows.ConvergenceTheorems.effectiveBetaPos

/-! ## `ConvergenceTheorems.effectiveGammaPos` -/
namespace Alignment.Shadows.ConvergenceTheorems.effectiveGammaPos

sa_claim "ConvergenceTheorems.effectiveGammaPos" group "ConvergenceTheorems" required
  text "Effective γ is positive."
  impl effective_gamma_pos

@[sa_forward "ConvergenceTheorems.effectiveGammaPos" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.effectiveGammaPos") : S1 :=
  fun d => h d

@[sa_backward "ConvergenceTheorems.effectiveGammaPos"]
theorem bwd (s1 : S1) : sa_impl% "ConvergenceTheorems.effectiveGammaPos" :=
  fun d => s1 d

end Alignment.Shadows.ConvergenceTheorems.effectiveGammaPos

/-! ## `ConvergenceTheorems.R105c.4` -/
namespace Alignment.Shadows.ConvergenceTheorems.R105c_4

sa_claim "ConvergenceTheorems.R105c.4" group "ConvergenceTheorems" required
  text "Here we verify the simpler identity: κ · β̃/(β̃ + γ̃) = κβ̃/(β̃ + γ̃)."
  impl poisson_R0_edge_formula

sa_fail_forward "ConvergenceTheorems.R105c.4" 1 "free-scalar abstraction: impl poisson_R0_edge_formula is ∀ κ β̃ γ̃ : ℝ, 0 < β̃ → 0 < γ̃ → κ·(β̃/(β̃+γ̃)) = κ·β̃/(β̃+γ̃), with two positivity hypotheses (unused in its ring proof). S1 is stated over PoissonEBCMData records d; instantiating the impl at d.kappa d.beta_tilde d.gamma_tilde needs proofs of 0 < d.beta_tilde and 0 < d.gamma_tilde, available only as the structure fields d.beta_tilde_pos / d.gamma_tilde_pos (data invariants, not structural). A faithful impl would drop the unused hypotheses or be stated over PoissonEBCMData."

sa_fail_backward "ConvergenceTheorems.R105c.4" "impl is stronger in its quantifier: it holds for every real κ (and any β̃, γ̃ > 0), while S1 covers only κ, β̃, γ̃ that are the fields of a PoissonEBCMData record, so κ > 0. To apply S1 at an arbitrary real κ one must build a record ⟨κ, β̃, γ̃, hκ, hβ, hγ⟩ and needs a proof of 0 < κ, which the impl does not provide (the identity for κ ≤ 0 follows only by real algebra, mul_div_assoc)."

end Alignment.Shadows.ConvergenceTheorems.R105c_4

/-! ## `ConvergenceTheorems.R105d.2` -/
namespace Alignment.Shadows.ConvergenceTheorems.R105d_2

sa_claim "ConvergenceTheorems.R105d.2" group "ConvergenceTheorems" required
  text "Thus the excess degree ratio ψ''(1)/ψ'(1) = κ²/κ = κ."
  impl poisson_excess_degree_real

sa_fail_forward "ConvergenceTheorems.R105d.2" 1 "impl poisson_excess_degree_real asserts only the arithmetic link κ^2/κ = κ (for κ > 0) and never mentions ψ''(1)/ψ'(1) or excessDegree. S1 ((poissonMoments κ hκ).excessDegree = κ²/κ, the link ψ''(1)/ψ'(1) = κ²/κ) holds only by the definitions excessDegree := secondFactorial/mean and poissonMoments (secondFactorial := κ², mean := κ), i.e. by rfl independent of h (the registry impl_note says the identification is carried by the text only)."

/-- `(poissonMoments κ hκ).excessDegree` unfolds to `κ ^ 2 / κ`, so the impl is `S2` up to
unfolding. -/
@[sa_forward "ConvergenceTheorems.R105d.2" 2]
theorem fwd2 (h : sa_impl% "ConvergenceTheorems.R105d.2") : S2 :=
  fun κ hκ => h κ hκ

@[sa_backward "ConvergenceTheorems.R105d.2"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "ConvergenceTheorems.R105d.2" :=
  fun κ hκ => s2 κ hκ

end Alignment.Shadows.ConvergenceTheorems.R105d_2

/-! ## R105e.2 (no shadow set: the blind author judged the text not a proposition) -/
namespace Alignment.Shadows.ConvergenceTheorems.R105e_2

sa_claim "ConvergenceTheorems.R105e.2" group "ConvergenceTheorems" required
  text "The Lean statement `kappa * S = kappa * S` is tautological: it holds by reflexivity. The chain rule itself is `S_theta_chain_rule`."
  impl S_theta_chain_rule_coeff

sa_fail_backward "ConvergenceTheorems.R105e.2" "No shadow set exists. The blind shadow author skipped the claim: 'The text describes a Lean statement (and points to another theorem); it asserts no proposition about the model, and the only formula it quotes is a reflexivity instance.' impl S_theta_chain_rule_coeff (κ·S = κ·S) is exactly that reflexivity, so there is nothing for a checker to align. Registrar question: reclassify this sentence as informal (a remark about the Lean statement); its mathematical content is covered by ConvergenceTheorems.sThetaChainRule."

end Alignment.Shadows.ConvergenceTheorems.R105e_2

/-! ## `ConvergenceTheorems.R107a` -/
namespace Alignment.Shadows.ConvergenceTheorems.R107a

sa_claim "ConvergenceTheorems.R107a" group "ConvergenceTheorems" required
  text "**Result 107a.** ψ''(1)/ψ'(1) = (⟨k²⟩ - ⟨k⟩)/⟨k⟩."
  impl excess_degree_second_moment

@[sa_forward "ConvergenceTheorems.R107a" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.R107a") : S1 :=
  fun m => h m

/-- `m.excessDegree` unfolds to `m.secondFactorial / m.mean`. -/
@[sa_forward "ConvergenceTheorems.R107a" 2]
theorem fwd2 (h : sa_impl% "ConvergenceTheorems.R107a") : S2 :=
  fun m => h m

@[sa_backward "ConvergenceTheorems.R107a"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "ConvergenceTheorems.R107a" :=
  fun m => s1 m

end Alignment.Shadows.ConvergenceTheorems.R107a

/-! ## `ConvergenceTheorems.R107b` -/
namespace Alignment.Shadows.ConvergenceTheorems.R107b

sa_claim "ConvergenceTheorems.R107b" group "ConvergenceTheorems" required
  text "**Result 107b.** (⟨k²⟩ - ⟨k⟩)/⟨k⟩ = ⟨k⟩ + Var(k)/⟨k⟩ - 1."
  impl excess_degree_variance_form

sa_fail_forward "ConvergenceTheorems.R107b" 1 "different left-hand side: impl excess_degree_variance_form states m.excessDegree = mean + variance/mean - 1, whose LHS is ψ''(1)/ψ'(1) = secondFactorial/mean; S1 (the text) has LHS (⟨k²⟩ - ⟨k⟩)/⟨k⟩ = (secondMoment - mean)/mean = ((secondFactorial + mean) - mean)/mean. The two LHSs agree only by real arithmetic (add_sub_cancel), i.e. by Result 107a, which is not in this claim's impl list; no admissible bridge exists (excessDegree m = (secondMoment m - mean)/mean would smuggle Result 107a). The registry impl_note records the same mismatch."

sa_fail_backward "ConvergenceTheorems.R107b" "S1 gives (secondMoment - mean)/mean = mean + variance/mean - 1; the impl needs excessDegree = secondFactorial/mean on the left. Rewriting (secondFactorial + mean) - mean to secondFactorial needs real arithmetic (add_sub_cancel = Result 107a), not structural reasoning; no admissible bridge (it would restate Result 107a)."

end Alignment.Shadows.ConvergenceTheorems.R107b

/-! ## `ConvergenceTheorems.R107c` -/
namespace Alignment.Shadows.ConvergenceTheorems.R107c

sa_claim "ConvergenceTheorems.R107c" group "ConvergenceTheorems" required
  text "**Result 107c.** The two forms are equal: (⟨k²⟩-⟨k⟩)/⟨k⟩ = ⟨k⟩+Var/⟨k⟩-1."
  impl excess_degree_forms_agree

@[sa_forward "ConvergenceTheorems.R107c" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.R107c") : S1 :=
  fun m => h m

@[sa_backward "ConvergenceTheorems.R107c"]
theorem bwd (s1 : S1) : sa_impl% "ConvergenceTheorems.R107c" :=
  fun m => s1 m

end Alignment.Shadows.ConvergenceTheorems.R107c

/-! ## `ConvergenceTheorems.R108a` -/
namespace Alignment.Shadows.ConvergenceTheorems.R108a

sa_claim "ConvergenceTheorems.R108a" group "ConvergenceTheorems" required
  text "**Result 108a.** R₀ = T · (⟨k⟩ + Var(k)/⟨k⟩ - 1)."
  impl R0_variance_formula

@[sa_forward "ConvergenceTheorems.R108a" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.R108a") : S1 :=
  fun τ m => h τ m

@[sa_backward "ConvergenceTheorems.R108a"]
theorem bwd (s1 : S1) : sa_impl% "ConvergenceTheorems.R108a" :=
  fun τ m => s1 τ m

end Alignment.Shadows.ConvergenceTheorems.R108a

/-! ## `ConvergenceTheorems.R108b` -/
namespace Alignment.Shadows.ConvergenceTheorems.R108b

sa_claim "ConvergenceTheorems.R108b" group "ConvergenceTheorems" required
  text "**Result 108b.** Heterogeneity amplifies R₀: for any degree distribution with mean ⟨k⟩ and Var ≥ 0, R₀ ≥ T·(⟨k⟩ - 1) = R₀(homogeneous)."
  impl R0_heterogeneity_amplifies

/-- `R0_homogeneous τ m.mean` unfolds to `τ * (m.mean - 1)`. -/
@[sa_forward "ConvergenceTheorems.R108b" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.R108b") : S1 :=
  fun τ hτ m => h τ m hτ

sa_fail_forward "ConvergenceTheorems.R108b" 2 "impl R0_heterogeneity_amplifies asserts only the inequality R0_homogeneous T m.mean ≤ R0_heterogeneous T m; the equality T·(⟨k⟩ - 1) = R₀(homogeneous) (S2: τ·(m.mean - 1) = R0_homogeneous τ m.mean) is not asserted and holds only by the definition R0_homogeneous T k := T·(k - 1) (rfl, independent of h); an equation cannot be derived structurally from a ≤."

@[sa_backward "ConvergenceTheorems.R108b"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "ConvergenceTheorems.R108b" :=
  fun τ m hτ => s1 τ hτ m

end Alignment.Shadows.ConvergenceTheorems.R108b

/-! ## `ConvergenceTheorems.R108c` -/
namespace Alignment.Shadows.ConvergenceTheorems.R108c

sa_claim "ConvergenceTheorems.R108c" group "ConvergenceTheorems" required
  text "**Result 108c.** Equality iff Var(k) = 0 (regular network)."
  impl R0_heterogeneity_eq_iff_regular

/-- `R0_homogeneous τ m.mean ≡ τ * (m.mean - 1)`; the impl's equation is oriented the other way. -/
@[sa_forward "ConvergenceTheorems.R108c" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.R108c") : S1 :=
  fun τ hτ m hv => ((h τ m hτ).mpr hv).symm

@[sa_forward "ConvergenceTheorems.R108c" 2]
theorem fwd2 (h : sa_impl% "ConvergenceTheorems.R108c") : S2 :=
  fun τ hτ m heq => (h τ m hτ).mp heq.symm

@[sa_forward "ConvergenceTheorems.R108c" 3]
theorem fwd3 (h : sa_impl% "ConvergenceTheorems.R108c") : S3 :=
  fun τ hτ m hv => ((h τ m hτ).mpr hv).symm

@[sa_forward "ConvergenceTheorems.R108c" 4]
theorem fwd4 (h : sa_impl% "ConvergenceTheorems.R108c") : S4 :=
  fun τ hτ m heq => (h τ m hτ).mp heq.symm

@[sa_backward "ConvergenceTheorems.R108c"]
theorem bwd (_s1 : S1) (_s2 : S2) (s3 : S3) (s4 : S4) :
    sa_impl% "ConvergenceTheorems.R108c" :=
  fun τ m hτ => ⟨fun heq => s4 τ hτ m heq.symm, fun hv => (s3 τ hτ m hv).symm⟩

end Alignment.Shadows.ConvergenceTheorems.R108c

/-! ## `ConvergenceTheorems.R109a` -/
namespace Alignment.Shadows.ConvergenceTheorems.R109a

sa_claim "ConvergenceTheorems.R109a" group "ConvergenceTheorems" required
  text "**Result 109a.** Poisson excess degree equals the mean κ."
  impl poisson_excess_eq_mean

@[sa_forward "ConvergenceTheorems.R109a" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.R109a") : S1 :=
  fun κ hκ => h κ hκ

/-- `(poissonMoments κ hκ).mean` reduces to `κ`. -/
@[sa_forward "ConvergenceTheorems.R109a" 2]
theorem fwd2 (h : sa_impl% "ConvergenceTheorems.R109a") : S2 :=
  fun κ hκ => h κ hκ

@[sa_backward "ConvergenceTheorems.R109a"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "ConvergenceTheorems.R109a" :=
  fun κ hκ => s1 κ hκ

end Alignment.Shadows.ConvergenceTheorems.R109a

/-! ## `ConvergenceTheorems.R109b` -/
namespace Alignment.Shadows.ConvergenceTheorems.R109b

sa_claim "ConvergenceTheorems.R109b" group "ConvergenceTheorems" required
  text "**Result 109b.** R₀ = T·κ for Poisson networks."
  impl poisson_R0

@[sa_forward "ConvergenceTheorems.R109b" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.R109b") : S1 :=
  fun τ κ hκ => h τ κ hκ

@[sa_backward "ConvergenceTheorems.R109b"]
theorem bwd (s1 : S1) : sa_impl% "ConvergenceTheorems.R109b" :=
  fun τ κ hκ => s1 τ κ hκ

end Alignment.Shadows.ConvergenceTheorems.R109b

/-! ## R110.stability -/
namespace Alignment.Shadows.ConvergenceTheorems.R110_stability

sa_claim "ConvergenceTheorems.R110.stability" group "ConvergenceTheorems" required
  text "For strictly convex f (some degree ≥ 3 has positive probability) it is the only fixed point in [0, 1] iff R₀ ≤ 1, where R₀ = f'(1) (not formalised here)."
  impl dfe_stable_iff_R0_le_one

sa_fail_forward "ConvergenceTheorems.R110.stability" 1 "impl dfe_stable_iff_R0_le_one is the tautology T·e ≤ 1 ↔ T·e ≤ 1 over free reals (the text itself says 'not formalised here'). It mentions no fixed point of the final-size map, so it does not give S1 (for strictly convex f, if θ = 1 is the only fixed point in [0,1] then f'(1) ≤ 1)."

sa_fail_forward "ConvergenceTheorems.R110.stability" 2 "impl is the tautology T·e ≤ 1 ↔ T·e ≤ 1. It does not give S2 (for strictly convex f with f'(1) ≤ 1, θ = 1 is the only fixed point in [0,1]), which needs a convexity argument about finalSizeMap."

sa_fail_backward "ConvergenceTheorems.R110.stability" "impl (A ↔ A) is provable by Iff.rfl without either shadow, so a backward checker could only be vacuous. The implementation does not state the fixed-point characterisation that the shadows describe."

end Alignment.Shadows.ConvergenceTheorems.R110_stability

/-! ## `ConvergenceTheorems.R110a` -/
namespace Alignment.Shadows.ConvergenceTheorems.R110a

sa_claim "ConvergenceTheorems.R110a" group "ConvergenceTheorems" required
  text "**Result 110a.** θ = 1 is always a fixed point: f(1) = 1 when g(1) = 1."
  impl disease_free_fixed_point

@[sa_forward "ConvergenceTheorems.R110a" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.R110a") : S1 :=
  fun τ => h τ

/-- `IsFixedPt (fun θ => finalSizeMap τ (g θ)) 1` unfolds to `finalSizeMap τ (g 1) = 1`; rewrite
`g 1 = 1` and apply the impl. -/
@[sa_forward "ConvergenceTheorems.R110a" 2]
theorem fwd2 (h : sa_impl% "ConvergenceTheorems.R110a") : S2 := by
  intro τ g hg
  show finalSizeMap τ (g 1) = 1
  exact (congrArg (finalSizeMap τ) hg).trans (h τ)

@[sa_backward "ConvergenceTheorems.R110a"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "ConvergenceTheorems.R110a" :=
  fun τ => s1 τ

end Alignment.Shadows.ConvergenceTheorems.R110a

/-! ## R110b.3 (no shadow set: the blind author judged the text not a proposition) -/
namespace Alignment.Shadows.ConvergenceTheorems.R110b_3

sa_claim "ConvergenceTheorems.R110b.3" group "ConvergenceTheorems" required
  text "**Tautological Lean statement:** `T * excessDeg = T * excessDeg`; the derivative is computed in `finalSizeMap_hasDerivAt`."
  impl fixed_point_derivative

sa_fail_backward "ConvergenceTheorems.R110b.3" "No shadow set exists. The blind shadow author skipped the claim: 'A remark about a Lean statement (a reflexivity instance) and a pointer to another theorem; no proposition to shadow.' impl fixed_point_derivative (T·e = T·e) is that reflexivity. Registrar question: reclassify as informal; the derivative content is ConvergenceTheorems.finalSizeMapHasDerivAt."

end Alignment.Shadows.ConvergenceTheorems.R110b_3

/-! ## `ConvergenceTheorems.R110c.2` -/
namespace Alignment.Shadows.ConvergenceTheorems.R110c_2

sa_claim "ConvergenceTheorems.R110c.2" group "ConvergenceTheorems" required
  text "|f'(1)| ≤ 1 iff T · excessDeg ≤ 1 (since both T and excessDeg are nonneg)."
  impl dfe_stable_iff_R0_le_one

sa_fail_forward "ConvergenceTheorems.R110c.2" 1 "vacuous impl: dfe_stable_iff_R0_le_one is (T·e ≤ 1 ↔ T·e ≤ 1) by Iff.rfl for free reals T, e ≥ 0; the text's left side |f'(1)| ≤ 1 has been replaced by the right side. S1 (|deriv (θ ↦ finalSizeMap τ (g θ)) 1| ≤ 1 → τ·excessDegree ≤ 1) needs the derivative f'(1) = τ·secondFactorial/mean (HasDerivAt/deriv lemmas) and le_abs_self; the impl states neither."

sa_fail_forward "ConvergenceTheorems.R110c.2" 2 "vacuous impl (P ↔ P by Iff.rfl). S2 (τ·excessDegree ≤ 1 → |deriv (θ ↦ finalSizeMap τ (g θ)) 1| ≤ 1) needs the derivative computation, abs_of_nonneg and 0 ≤ excessDegree (data invariants with div_nonneg); the impl states none of it."

sa_fail_forward "ConvergenceTheorems.R110c.2" 3 "vacuous impl: (T·e ≤ 1 ↔ T·e ≤ 1) contains no absolute value. S3 (|τ·excessDegree| ≤ 1 → τ·excessDegree ≤ 1) is le_abs_self plus le_trans, library lemmas that the impl does not state."

sa_fail_forward "ConvergenceTheorems.R110c.2" 4 "vacuous impl: (T·e ≤ 1 ↔ T·e ≤ 1) contains no absolute value. S4 (τ·excessDegree ≤ 1 → |τ·excessDegree| ≤ 1) needs abs_of_nonneg with 0 ≤ τ·excessDegree, i.e. mul_nonneg and 0 ≤ excessDegree from the data invariants mean_pos and secondFactorial_nonneg (div_nonneg). The impl's hypothesis 0 ≤ e is an input, never a conclusion, so it supplies none of this."

/-- The impl is the tautology `P ↔ P`. -/
@[sa_backward "ConvergenceTheorems.R110c.2"]
theorem bwd (_s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) :
    sa_impl% "ConvergenceTheorems.R110c.2" :=
  fun _ _ _ _ => Iff.rfl

end Alignment.Shadows.ConvergenceTheorems.R110c_2

/-! ## `ConvergenceTheorems.R110d` -/
namespace Alignment.Shadows.ConvergenceTheorems.R110d

sa_claim "ConvergenceTheorems.R110d" group "ConvergenceTheorems" required
  text "**Result 110d.** When T = 0 (no transmission), the fixed point is trivially θ = 1."
  impl no_transmission_fixed_point

/-- `IsFixedPt (fun θ => finalSizeMap 0 (g θ)) 1` unfolds to `finalSizeMap 0 (g 1) = 1`, which is
the impl at the value `g 1`. -/
@[sa_forward "ConvergenceTheorems.R110d" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.R110d") : S1 := by
  intro g _
  show finalSizeMap 0 (g 1) = 1
  exact h (g 1)

/-- A fixed point θ satisfies `finalSizeMap 0 (g θ) = θ`, and the impl gives
`finalSizeMap 0 (g θ) = 1`. -/
@[sa_forward "ConvergenceTheorems.R110d" 2]
theorem fwd2 (h : sa_impl% "ConvergenceTheorems.R110d") : S2 := by
  intro g _ θ hfix
  have hθ : finalSizeMap 0 (g θ) = θ := hfix
  exact hθ.symm.trans (h (g θ))

sa_fail_backward "ConvergenceTheorems.R110d" "impl is stronger in form: no_transmission_fixed_point asserts finalSizeMap 0 v = 1 for every real value v, whereas S1/S2 speak only of normalised functions g (g 1 = 1) and of fixed points of θ ↦ finalSizeMap 0 (g θ). S1 yields only finalSizeMap 0 1 = 1. Recovering an arbitrary v from S2 needs a g with g 1 = 1 and g (finalSizeMap 0 v) = v, which requires a classical case split on finalSizeMap 0 v = 1 (by_cases / Decidable, if_pos/if_neg), or the arithmetic 1 - 0 + 0·v = 1; neither is structural. Semantically S1 ∧ S2 imply the impl classically, so this is not an overclaim of the text."

end Alignment.Shadows.ConvergenceTheorems.R110d

/-! ## `ConvergenceTheorems.R112a` -/
namespace Alignment.Shadows.ConvergenceTheorems.R112a

sa_claim "ConvergenceTheorems.R112a" group "ConvergenceTheorems" required
  text "**Result 112a.** T_c = 1 / excessDegree."
  impl critical_T_eq_inv_excess

@[sa_forward "ConvergenceTheorems.R112a" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.R112a") : S1 :=
  fun m hsf => h m hsf

@[sa_backward "ConvergenceTheorems.R112a"]
theorem bwd (s1 : S1) : sa_impl% "ConvergenceTheorems.R112a" :=
  fun m hsf => s1 m hsf

end Alignment.Shadows.ConvergenceTheorems.R112a

/-! ## `ConvergenceTheorems.R112b` -/
namespace Alignment.Shadows.ConvergenceTheorems.R112b

sa_claim "ConvergenceTheorems.R112b" group "ConvergenceTheorems" required
  text "**Result 112b.** R₀ > 1 iff T > T_c: the epidemic threshold. R₀ = T · excessDeg > 1 ↔ T > 1/excessDeg (when excessDeg > 0)."
  impl epidemic_threshold

sa_fail_forward "ConvergenceTheorems.R112b" 1 "extra hypothesis: impl epidemic_threshold requires 0 < T (_hT, unused in its proof), which the text ('R₀ > 1 iff T > T_c') and S1 do not assume; S1 quantifies over every real τ. From 1 < R0_heterogeneous τ m one gets 0 < τ only via real order lemmas and the data invariants secondFactorial_nonneg / mean_pos (τ ≤ 0 → τ·e ≤ 0), which is not structural. A faithful impl would drop the unused hypothesis."

sa_fail_forward "ConvergenceTheorems.R112b" 2 "extra hypothesis: impl epidemic_threshold requires 0 < T, which S2 (T_c m h < τ → 1 < R0_heterogeneous τ m, every real τ) does not assume. 0 < τ follows from T_c < τ only via 0 < T_c = mean/secondFactorial (data invariant mean_pos, div_pos) and lt_trans, which is not structural."

sa_fail_forward "ConvergenceTheorems.R112b" 3 "impl epidemic_threshold (an iff between 1 < R₀ and T_c < T) does not assert the identity R₀ = T·excessDeg; S3 (R0_heterogeneous τ m = τ * m.excessDegree) holds only by the definition R0_heterogeneous T m := T·excessDegree m (rfl, independent of h)."

sa_fail_forward "ConvergenceTheorems.R112b" 4 "impl epidemic_threshold is stated with hypotheses 0 < T and 0 < secondFactorial and conclusion T_c m hsf < T with T_c = mean/secondFactorial. S4 (0 < excessDegree → 1 < R₀ → 1/excessDegree < τ, every real τ) has neither hypothesis: 0 < secondFactorial from 0 < secondFactorial/mean needs mean_pos and div_pos_iff, 0 < τ needs order lemmas, and mean/secondFactorial = 1/(secondFactorial/mean) needs one_div_div; none is structural."

sa_fail_forward "ConvergenceTheorems.R112b" 5 "impl epidemic_threshold needs 0 < T and 0 < secondFactorial, and its threshold is mean/secondFactorial; S5 (0 < excessDegree → 1/excessDegree < τ → 1 < R₀, every real τ) supplies only 0 < secondFactorial/mean. Obtaining 0 < secondFactorial (div_pos_iff with mean_pos), 0 < τ (0 < 1/excessDegree, lt_trans) and 1/(sf/mean) = mean/sf (one_div_div) needs data invariants and library lemmas, not structural reasoning."

@[sa_backward "ConvergenceTheorems.R112b"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) (_s4 : S4) (_s5 : S5) :
    sa_impl% "ConvergenceTheorems.R112b" :=
  fun τ m _ hsf => ⟨s1 τ m hsf, s2 τ m hsf⟩

end Alignment.Shadows.ConvergenceTheorems.R112b

/-! ## `ConvergenceTheorems.R112c` -/
namespace Alignment.Shadows.ConvergenceTheorems.R112c

sa_claim "ConvergenceTheorems.R112c" group "ConvergenceTheorems" required
  text "**Result 112c.** The threshold depends only on first two moments. T_c = ⟨k⟩/⟨k(k-1)⟩ = ⟨k⟩/(⟨k²⟩ - ⟨k⟩)."
  impl threshold_moment_form

/-- Both thresholds are, by the impl, `mean / (secondMoment - mean)`; rewrite with the equal
first two moments. -/
@[sa_forward "ConvergenceTheorems.R112c" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.R112c") : S1 := by
  intro m₁ m₂ h₁ h₂ hmean hsm
  rw [h m₁ h₁, h m₂ h₂, hmean, hsm]

sa_fail_forward "ConvergenceTheorems.R112c" 2 "impl threshold_moment_form states only T_c = ⟨k⟩/(⟨k²⟩ - ⟨k⟩) = mean/(secondMoment - mean); the first form T_c = ⟨k⟩/⟨k(k-1)⟩ (S2: criticalTransmissibility m h = mean/secondFactorial) is not asserted and holds only by the definition criticalTransmissibility m _ := mean/secondFactorial (rfl, independent of h). Deriving it from the impl would need (secondFactorial + mean) - mean = secondFactorial (add_sub_cancel), which is not structural."

@[sa_forward "ConvergenceTheorems.R112c" 3]
theorem fwd3 (h : sa_impl% "ConvergenceTheorems.R112c") : S3 :=
  fun m hsf => h m hsf

@[sa_backward "ConvergenceTheorems.R112c"]
theorem bwd (_s1 : S1) (_s2 : S2) (s3 : S3) : sa_impl% "ConvergenceTheorems.R112c" :=
  fun m hsf => s3 m hsf

end Alignment.Shadows.ConvergenceTheorems.R112c

/-! ## `ConvergenceTheorems.R112d` -/
namespace Alignment.Shadows.ConvergenceTheorems.R112d

sa_claim "ConvergenceTheorems.R112d" group "ConvergenceTheorems" required
  text "**Result 112d.** For Poisson(κ), T_c = 1/κ."
  impl poisson_threshold

/-- The impl's positivity argument of `criticalTransmissibility` and the shadow's `h` are
definitionally equal (proof irrelevance). -/
@[sa_forward "ConvergenceTheorems.R112d" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.R112d") : S1 :=
  fun κ hκ _ => h κ hκ

sa_fail_backward "ConvergenceTheorems.R112d" "audit limitation only (no semantic gap): the impl's statement fixes T_c's positivity argument to the proof pow_pos hk 2 : 0 < κ^2 built inside the statement. S1 takes that proof as a hypothesis h : 0 < (poissonMoments κ hκ).secondFactorial, so applying S1 needs a proof of 0 < κ^2 from 0 < κ, which requires the library lemma pow_pos (or mul_pos) and is not structural."

end Alignment.Shadows.ConvergenceTheorems.R112d

/-! ## `ConvergenceTheorems.R112e` -/
namespace Alignment.Shadows.ConvergenceTheorems.R112e

sa_claim "ConvergenceTheorems.R112e" group "ConvergenceTheorems" required
  text "**Result 112e.** Higher variance lowers the epidemic threshold. If m₁ and m₂ have the same mean but Var(m₁) ≤ Var(m₂), then T_c(m₂) ≤ T_c(m₁): more heterogeneous networks have lower thresholds."
  impl variance_lowers_threshold

@[sa_forward "ConvergenceTheorems.R112e" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.R112e") : S1 :=
  fun m₁ m₂ h₁ h₂ hmean hvar => h m₁ m₂ h₁ h₂ hmean hvar

@[sa_backward "ConvergenceTheorems.R112e"]
theorem bwd (s1 : S1) : sa_impl% "ConvergenceTheorems.R112e" :=
  fun m₁ m₂ h₁ h₂ hmean hvar => s1 m₁ m₂ h₁ h₂ hmean hvar

end Alignment.Shadows.ConvergenceTheorems.R112e

/-! ## r0MassActionEqEdge (`Tedge d` unfolds to `β̃/(β̃ + γ̃)`) -/
namespace Alignment.Shadows.ConvergenceTheorems.r0MassActionEqEdge

sa_claim "ConvergenceTheorems.r0MassActionEqEdge" group "ConvergenceTheorems" required
  text "The mass-action R₀ β/γ with β = κβ̃ and γ = γ̃ + β̃ equals the Poisson EBCM R₀ κ · T_edge = κ · β̃/(β̃ + γ̃), exactly."
  impl R0_massAction_eq_edge

@[sa_forward "ConvergenceTheorems.r0MassActionEqEdge" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.r0MassActionEqEdge") : S1 := fun d => h d

sa_fail_forward "ConvergenceTheorems.r0MassActionEqEdge" 2 "impl gives β/γ = κ·(β̃/(β̃+γ̃)). S2 has R0_heterogeneous (Tedge d) (poissonMoments κ) on the right, which unfolds to Tedge d · (κ²/κ). κ·Tedge = Tedge·(κ²/κ) needs mul_comm and field cancellation (κ ≠ 0), which are not definitional in ℝ, so S2 does not follow structurally from h. Mathematically it holds, since the Poisson excess degree is κ."

@[sa_backward "ConvergenceTheorems.r0MassActionEqEdge"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "ConvergenceTheorems.r0MassActionEqEdge" :=
  fun d => s1 d

end Alignment.Shadows.ConvergenceTheorems.r0MassActionEqEdge

/-! ## sThetaChainRule -/
namespace Alignment.Shadows.ConvergenceTheorems.sThetaChainRule

sa_claim "ConvergenceTheorems.sThetaChainRule" group "ConvergenceTheorems" required
  text "The chain rule behind Result 105e: if `θ` has derivative `θ'` at `t`, then `S = exp(κ(θ − 1))` has derivative `κ · S · θ'` at `t`."
  impl S_theta_chain_rule

@[sa_forward "ConvergenceTheorems.sThetaChainRule" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.sThetaChainRule") : S1 :=
  fun d _θ _θ' _t hθ => h d.kappa hθ

sa_fail_backward "ConvergenceTheorems.sThetaChainRule" "impl S_theta_chain_rule holds for every real κ; S1 states the chain rule only for κ = d.kappa of a PoissonEBCMData, i.e. κ > 0. For κ ≤ 0 no PoissonEBCMData has that κ, so impl does not follow from S1: impl is stronger on its domain (the text's κ is the Poisson mean degree)."

end Alignment.Shadows.ConvergenceTheorems.sThetaChainRule

/-! ## finalSizeMapHasDerivAt -/
namespace Alignment.Shadows.ConvergenceTheorems.finalSizeMapHasDerivAt

sa_claim "ConvergenceTheorems.finalSizeMapHasDerivAt" group "ConvergenceTheorems" required
  text "The derivative of the final-size map: if `g` has derivative `g'` at `x`, then `θ ↦ f(θ) = 1 − T + T·g(θ)` has derivative `T·g'` at `x`."
  impl finalSizeMap_hasDerivAt

@[sa_forward "ConvergenceTheorems.finalSizeMapHasDerivAt" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.finalSizeMapHasDerivAt") : S1 :=
  fun T _g _g' _x hg => h T hg

@[sa_backward "ConvergenceTheorems.finalSizeMapHasDerivAt"]
theorem bwd (s1 : S1) : sa_impl% "ConvergenceTheorems.finalSizeMapHasDerivAt" := by
  intro T g g' x hg
  exact s1 T g g' x hg

end Alignment.Shadows.ConvergenceTheorems.finalSizeMapHasDerivAt

/-! ## dfeDerivativeAbsLeOneIff -/
namespace Alignment.Shadows.ConvergenceTheorems.dfeDerivativeAbsLeOneIff

sa_claim "ConvergenceTheorems.dfeDerivativeAbsLeOneIff" group "ConvergenceTheorems" required
  text "For `T ≥ 0` and `excessDeg ≥ 0`, `|f'(1)| ≤ 1 ↔ R₀ ≤ 1`, where `f'(1) = R₀ = T · excessDeg`."
  impl dfe_derivative_abs_le_one_iff

@[sa_forward "ConvergenceTheorems.dfeDerivativeAbsLeOneIff" 1]
theorem fwd1 (h : sa_impl% "ConvergenceTheorems.dfeDerivativeAbsLeOneIff") : S1 :=
  fun T e hT he => (h T e hT he).mp

@[sa_forward "ConvergenceTheorems.dfeDerivativeAbsLeOneIff" 2]
theorem fwd2 (h : sa_impl% "ConvergenceTheorems.dfeDerivativeAbsLeOneIff") : S2 :=
  fun T e hT he => (h T e hT he).mpr

@[sa_backward "ConvergenceTheorems.dfeDerivativeAbsLeOneIff"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "ConvergenceTheorems.dfeDerivativeAbsLeOneIff" :=
  fun T e hT he => ⟨s1 T e hT he, s2 T e hT he⟩

end Alignment.Shadows.ConvergenceTheorems.dfeDerivativeAbsLeOneIff

/-! ## `ConvergenceTheorems.R105` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.ConvergenceTheorems.R105

sa_claim "ConvergenceTheorems.R105" group "ConvergenceTheorems"
  text "For a Poisson(κ) degree distribution with per-edge transmission rate β̃ and recovery γ̃, the susceptible curve S(t) of the EBCM coincides with that of classical SIR with effective rates: β = κ β̃ and γ = γ̃ + β̃; the infected curves differ (Rempała 2023)."
  impl

end Alignment.Shadows.ConvergenceTheorems.R105

/-! ## `ConvergenceTheorems.R105.keyIdentity` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.ConvergenceTheorems.R105_keyIdentity

sa_claim "ConvergenceTheorems.R105.keyIdentity" group "ConvergenceTheorems"
  text "Key algebraic identity: the Poisson EBCM ODE θ̇ = -β̃ θ + β̃ exp(κ(θ-1)) + γ̃(1-θ) reduces to dS/dt = -β S I when S = exp(κ(θ-1)) and I := φ_I (the probability that a partner is infectious and has not yet transmitted), not the network prevalence."
  impl

end Alignment.Shadows.ConvergenceTheorems.R105_keyIdentity

/-! ## `ConvergenceTheorems.R105c.1` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.ConvergenceTheorems.R105c_1

sa_claim "ConvergenceTheorems.R105c.1" group "ConvergenceTheorems"
  text "**Result 105c.** Transmissibility consistency: with β = κβ̃ and γ = γ̃ + β̃, the mass-action R₀ is β/γ = κβ̃/(β̃ + γ̃)."
  impl

end Alignment.Shadows.ConvergenceTheorems.R105c_1

/-! ## `ConvergenceTheorems.R105c.2` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.ConvergenceTheorems.R105c_2

sa_claim "ConvergenceTheorems.R105c.2" group "ConvergenceTheorems"
  text "With the edge-based transmissibility T_edge = β̃/(β̃ + γ̃), the mass-action R₀ is exactly T_edge · κ, the Poisson EBCM R₀ (`R0_massAction_eq_edge`)."
  impl

end Alignment.Shadows.ConvergenceTheorems.R105c_2

/-! ## `ConvergenceTheorems.R105c.3` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.ConvergenceTheorems.R105c_3

sa_claim "ConvergenceTheorems.R105c.3" group "ConvergenceTheorems"
  text "There is no large-κ approximation: the two R₀ agree for every κ."
  impl

end Alignment.Shadows.ConvergenceTheorems.R105c_3

/-! ## `ConvergenceTheorems.R110b.2` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.ConvergenceTheorems.R110b_2

sa_claim "ConvergenceTheorems.R110b.2" group "ConvergenceTheorems"
  text "Linear stability of θ = 1 needs |f'(1)| < 1, i.e. R₀ < 1; at R₀ = 1 the linearisation is inconclusive, and θ = 1 is still attracting from below when f is strictly convex."
  impl

end Alignment.Shadows.ConvergenceTheorems.R110b_2
