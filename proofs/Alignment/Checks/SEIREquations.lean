import Alignment.Registry
import Alignment.Shadows.SEIREquations

/-!
# Checkers: group `SEIREquations`

Registrations, forward and backward checkers, and failure records for the claims of
`EBCMCategory/SEIREquations.lean`. The blind shadows are in
`Alignment/Shadows/SEIREquations.lean`.

No bridges are used. Every shadow is stated directly over the operations under test
(`SEIRState.edgeHazard`, `dθ`, `I_pop`, `I_pop_wrong`, `dE`, `dI`, `dR`). Where a shadow is a
closed formula for one of these operations (edgeHazard = β·φ_I, dθ = −β·φ_I, dI = σE − γI), that
formula *is* the claim, so a bridge stating it would smuggle the claim's content. A checker built
from such a bridge would also not use `h`.

Policy used for this group. Every operation here is a one-line definition, so almost every
shadow can be re-proved *from scratch* by unfolding. A check counts as proved only when the
shadow is an instance, projection or logical consequence of the implementation's statement,
and `h` supplies the content. Definitional unfolding may be used to move between two states
that differ only in fields the operation does not read. That is allowed only when `h` still
supplies a non-definitional fact, as in `iPopWrongNonzeroAtSeed` S2.

A check is recorded as failed in three cases:
* the implementation does not state the property;
* the only proof would re-use `h` to supply a definitional triviality such as `0 = 0` at another
  instance (a vacuity dodge, README limitation 1);
* the step needs field or order arithmetic on ℚ (`sub_le_sub_right`, `le_of_lt`, reassociation
  and cancellation) or a data invariant (`p.β_pos`), which is not structural.

Failures that come only from the last case are marked as audit limitations.
-/

/-! ## `SEIREquations.table.SEIR1` -/
namespace Alignment.Shadows.SEIREquations.table_SEIR1

sa_claim "SEIREquations.table.SEIR1" group "SEIREquations" required
  text "| SEIR1 | I_pop counts only infectious stages (I), not E |"
  impl I_pop_zero_at_seed

sa_fail_forward "SEIREquations.table.SEIR1" 1 "impl I_pop_zero_at_seed states I_pop = 0 only at the literal states <theta=1, phi_E=eps, phi_I=0, pop_E=eps, pop_I=0, pop_R=0> (one state per eps). S1 requires I_pop s = s.pop_I for every state s, and in particular for states with pop_I /= 0. The impl says nothing about those states. S1 holds only by the definition of SEIRState.I_pop, which would mean re-proving it without h."
sa_fail_forward "SEIREquations.table.SEIR1" 2 "impl I_pop_zero_at_seed is a statement about the literal seed states only (in which pop_E and phi_E vary together through eps, and pop_I = 0). S2 requires I_pop to be invariant under replacing pop_E by any x in every state s. The impl does not state this. It holds only because the definition of I_pop does not read pop_E, and using that means re-proving S2 without h."

/-- `S1` at the impl's literal state: `I_pop ⟨1, ε, 0, ε, 0, 0⟩ = pop_I ⟨1, ε, 0, ε, 0, 0⟩`, and
the projection `pop_I` of that literal state is `0` by reduction. -/
@[sa_backward "SEIREquations.table.SEIR1"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "SEIREquations.table.SEIR1" :=
  fun ε => s1 ⟨1, ε, 0, ε, 0, 0⟩

end Alignment.Shadows.SEIREquations.table_SEIR1

/-! ## `SEIREquations.table.SEIR2` -/
namespace Alignment.Shadows.SEIREquations.table_SEIR2

sa_claim "SEIREquations.table.SEIR2" group "SEIREquations" required
  text "| SEIR2 | E does not contribute to the edge hazard |"
  impl edge_hazard_independent_of_E

/-- `{s with φ_E := x}` and `s` have the same `φ_I` (projection of a record update), so `h`
identifies their edge hazards. -/
@[sa_forward "SEIREquations.table.SEIR2" 1]
theorem fwd1 (h : sa_impl% "SEIREquations.table.SEIR2") : S1 :=
  fun s p x => h { s with φ_E := x } s p rfl

sa_fail_backward "SEIREquations.table.SEIR2" "impl is stronger than S1. impl edge_hazard_independent_of_E says that s1.phi_I = s2.phi_I implies s1.edgeHazard p = s2.edgeHazard p, for states s1, s2 that may differ in every field other than phi_I (theta, phi_E, pop_E, pop_I, pop_R). S1 only gives invariance under changing phi_E. From S1 one gets edgeHazard s1 p = edgeHazard {s1 with phi_E := s2.phi_E} p, but that state still differs from s2 in theta and the population fields. Closing the gap needs the definition edgeHazard = beta * phi_I, i.e. re-proving the impl without S1."

end Alignment.Shadows.SEIREquations.table_SEIR2

/-! ## `SEIREquations.table.SEIR3` -/
namespace Alignment.Shadows.SEIREquations.table_SEIR3

sa_claim "SEIREquations.table.SEIR3" group "SEIREquations" required
  text "| SEIR3 | S + E + I + R = 1 (conservation, excluding seed) |"
  impl seir_population_conservation

sa_fail_forward "SEIREquations.table.SEIR3" 1 "impl seir_population_conservation gives dE p inc + dI p + dR p = inc. S1 requires ((dS inc + dE p inc) + dI p) + dR p = 0 with dS inc = -inc. Going from one to the other needs reassociation of + and the cancellation -inc + inc = 0 on Q (ring arithmetic), which is not structural, and no bridge on a trusted definition can carry it (audit limitation). The impl also has no susceptible fraction S and no normalisation S + E + I + R = 1. It is only the rate identity for the non-susceptible classes, with 'excluding seed' having no counterpart."
sa_fail_backward "SEIREquations.table.SEIR3" "impl dE + dI + dR = inc follows from S1 (-inc + dE + dI + dR = 0) only by ring arithmetic on Q (reassociation and adding inc to both sides), which is not structural (audit limitation). The two statements are equivalent algebraically."

end Alignment.Shadows.SEIREquations.table_SEIR3

/-! ## `SEIREquations.table.SEIR4` -/
namespace Alignment.Shadows.SEIREquations.table_SEIR4

sa_claim "SEIREquations.table.SEIR4" group "SEIREquations" required
  text "| SEIR4 | θ only decreases from I-edges (not E-edges) |"
  impl seir_theta_nonincreasing

sa_fail_forward "SEIREquations.table.SEIR4" 1 "impl seir_theta_nonincreasing states only 0 <= phi_I -> dtheta <= 0. S1 ('not E-edges') requires dtheta to be invariant under replacing phi_E by any x. The impl says nothing about phi_E. The invariance holds only because the definition dtheta = -(beta * phi_I) does not read phi_E, and using that means re-proving S1 without h."
sa_fail_forward "SEIREquations.table.SEIR4" 2 "impl gives an upper bound dtheta <= 0 when phi_I >= 0. S2 ('only from I-edges') requires the lower bound 0 <= dtheta when phi_I = 0. With phi_I = 0 the impl yields only dtheta <= 0, the opposite inequality. 0 <= dtheta follows only from the definition, via -(beta * 0) = 0 (mul_zero, neg_zero), which is not stated by the impl and not structural."
sa_fail_backward "SEIREquations.table.SEIR4" "SHADOW?: the text 'θ only decreases from I-edges (not E-edges)' asserts that the effect of I-edges on θ is a decrease. The shadow set drops that direction. S1 (dtheta independent of phi_E) and S2 (phi_I = 0 -> 0 <= dtheta) are both satisfied by dtheta = +beta * phi_I, in which θ increases through I-edges, and that violates the impl (0 <= phi_I -> dtheta <= 0) at phi_I > 0. So the impl states the decrease direction (it matches the verb 'decreases'), which no shadow requires, and it cannot be derived from S1 and S2."

end Alignment.Shadows.SEIREquations.table_SEIR4

/-! ## `SEIREquations.edgeHazard` -/
namespace Alignment.Shadows.SEIREquations.edgeHazard

sa_claim "SEIREquations.edgeHazard" group "SEIREquations" required
  text "The edge hazard: only I contributes (E has zero transmission rate). **SEIR2**: E does NOT contribute to edge hazard."
  impl edge_hazard_independent_of_E

/-- `{s with φ_E := x}` and `s` have the same `φ_I`, so `h` identifies their edge hazards. -/
@[sa_forward "SEIREquations.edgeHazard" 1]
theorem fwd1 (h : sa_impl% "SEIREquations.edgeHazard") : S1 :=
  fun s p x => h { s with φ_E := x } s p rfl

/-- `S2` ("determined by φ_I alone") is the implementation's statement. -/
@[sa_forward "SEIREquations.edgeHazard" 2]
theorem fwd2 (h : sa_impl% "SEIREquations.edgeHazard") : S2 :=
  fun s s' p hφ => h s s' p hφ

sa_fail_forward "SEIREquations.edgeHazard" 3 "impl edge_hazard_independent_of_E states only that two states with equal phi_I have equal edgeHazard p. It does not determine the value of the hazard. S3 requires the formula edgeHazard s p = beta * phi_I (0 * phi_E + beta * phi_I, 'E has zero transmission rate'). The formula is the definition of SEIRState.edgeHazard, but no impl conjunct states it. Any function of phi_I (e.g. beta^2 * phi_I, or 0) satisfies the impl, so a proof would have to re-prove S3 from the definition without h."

/-- `S2` is exactly the implementation's statement. -/
@[sa_backward "SEIREquations.edgeHazard"]
theorem bwd (_s1 : S1) (s2 : S2) (_s3 : S3) : sa_impl% "SEIREquations.edgeHazard" :=
  fun s₁ s₂ p hφ => s2 s₁ s₂ p hφ

end Alignment.Shadows.SEIREquations.edgeHazard

/-! ## `SEIREquations.dTheta` -/
namespace Alignment.Shadows.SEIREquations.dTheta

sa_claim "SEIREquations.dTheta" group "SEIREquations" required
  text "dθ/dt = −β·φ_I (only infectious edges cause transmission). **SEIR4**: θ does not decrease from E-edges."
  impl seir_theta_nonincreasing

sa_fail_forward "SEIREquations.dTheta" 1 "impl seir_theta_nonincreasing states only the sign 0 <= phi_I -> dtheta <= 0. S1 requires the formula dtheta = (-beta) * phi_I. The impl does not determine the value (any non-positive rate, e.g. dtheta = -beta^2 * phi_I or 0, satisfies it). The formula is the definition of SEIRState.dtheta (literally -(beta * phi_I), which equals (-beta) * phi_I only by neg_mul), and no impl conjunct states it. A bridge stating it would be the claim itself, and its checker would not use h."
sa_fail_forward "SEIREquations.dTheta" 2 "impl states only 0 <= phi_I -> dtheta <= 0. S2 ('θ does not decrease from E-edges') requires dtheta to be invariant under replacing phi_E by any x. The impl says nothing about phi_E. The invariance holds only because the definition of dtheta does not read phi_E, and using that means re-proving S2 without h."
sa_fail_backward "SEIREquations.dTheta" "impl 0 <= phi_I -> dtheta <= 0 follows from S1 (dtheta = (-beta) * phi_I) only by ordered-field arithmetic ((-beta) * phi_I <= 0 from beta > 0 and phi_I >= 0: neg_mul, mul_nonneg, neg_nonpos) and the data invariant p.beta_pos. Neither is structural (audit limitation). The impl is also a different statement from the text: the text gives the formula, and the impl gives only its sign."

end Alignment.Shadows.SEIREquations.dTheta

/-! ## `SEIREquations.seirPopulationConservation` -/
namespace Alignment.Shadows.SEIREquations.seirPopulationConservation

sa_claim "SEIREquations.seirPopulationConservation" group "SEIREquations" required
  text "**SEIR3.** Population conservation: d(E + I + R)/dt = incidence. The total non-susceptible fraction grows exactly at the incidence rate."
  impl seir_population_conservation

@[sa_forward "SEIREquations.seirPopulationConservation" 1]
theorem fwd1 (h : sa_impl% "SEIREquations.seirPopulationConservation") : S1 :=
  fun s p inc => h s p inc

@[sa_backward "SEIREquations.seirPopulationConservation"]
theorem bwd (s1 : S1) : sa_impl% "SEIREquations.seirPopulationConservation" :=
  fun s p inc => s1 s p inc

end Alignment.Shadows.SEIREquations.seirPopulationConservation

/-! ## `SEIREquations.iPopZeroAtSeed-a` -/
namespace Alignment.Shadows.SEIREquations.iPopZeroAtSeed_a

sa_claim "SEIREquations.iPopZeroAtSeed-a" group "SEIREquations" required
  text "**SEIR1.** I_pop counts only infectious stages."
  impl I_pop_zero_at_seed

sa_fail_forward "SEIREquations.iPopZeroAtSeed-a" 1 "impl I_pop_zero_at_seed states I_pop = 0 only at the literal states <1, eps, 0, eps, 0, 0> (a single-instance check proved by rfl). S1 requires I_pop s = s.pop_I for every state s, including states with pop_I /= 0 and pop_E /= 0. The impl says nothing about those states. The universal statement holds only by the definition of SEIRState.I_pop, which would mean re-proving it without h."

/-- `S1` at the impl's literal state; `pop_I ⟨1, ε, 0, ε, 0, 0⟩` reduces to `0`. -/
@[sa_backward "SEIREquations.iPopZeroAtSeed-a"]
theorem bwd (s1 : S1) : sa_impl% "SEIREquations.iPopZeroAtSeed-a" :=
  fun ε => s1 ⟨1, ε, 0, ε, 0, 0⟩

end Alignment.Shadows.SEIREquations.iPopZeroAtSeed_a

/-! ## `SEIREquations.iPopZeroAtSeed-b` -/
namespace Alignment.Shadows.SEIREquations.iPopZeroAtSeed_b

sa_claim "SEIREquations.iPopZeroAtSeed-b" group "SEIREquations" required
  text "At t=0 with seed in E: I_pop = 0, not ε."
  impl I_pop_zero_at_seed

sa_fail_forward "SEIREquations.iPopZeroAtSeed-b" 1 "impl I_pop_zero_at_seed fixes the edge variables of the seed state at theta = 1, phi_E = eps, phi_I = 0. S1 requires I_pop <theta, phiE, phiI, eps, 0, 0> = 0 for arbitrary theta, phiE, phiI. Both statements reduce definitionally to 0 = 0. A checker 'fun eps _ _ _ _ => h eps' would type-check, but it would use h only to supply rfl at a different instance (a vacuity dodge, README limitation 1). The impl's statement does not cover the other edge values."
sa_fail_forward "SEIREquations.iPopZeroAtSeed-b" 2 "impl does not state 'not ε' (I_pop /= eps), and it fixes theta = 1, phi_E = eps, phi_I = 0 where S2 quantifies over all edge variables. I_pop /= eps under 0 < eps follows only by rewriting the definitional I_pop = 0 into 0 < eps (the order fact 0 < 0 -> False). That needs no h, so any use of h would be a dodge."
sa_fail_backward "SEIREquations.iPopZeroAtSeed-b" "impl is stronger in eps. I_pop_zero_at_seed holds for every eps in Q with no positivity hypothesis, while S1 and S2 assume 0 < eps (the seed is positive) and so give nothing at eps <= 0. The only route would apply s1 at some positive eps' (itself needing a proof of 0 < eps', not structural) and rely on both statements reducing definitionally to 0 = 0. That re-uses a definitional triviality at a different instance and is not a derivation from the shadows."

end Alignment.Shadows.SEIREquations.iPopZeroAtSeed_b

/-! ## `SEIREquations.iPopWrongNonzeroAtSeed` -/
namespace Alignment.Shadows.SEIREquations.iPopWrongNonzeroAtSeed

sa_claim "SEIREquations.iPopWrongNonzeroAtSeed" group "SEIREquations" required
  text "The buggy version gives ε at t=0 (wrong)."
  impl I_pop_wrong_nonzero_at_seed

sa_fail_forward "SEIREquations.iPopWrongNonzeroAtSeed" 1 "impl I_pop_wrong_nonzero_at_seed states only I_pop_wrong /= 0 at the seed state <1, eps, 0, eps, 0, 0> under 0 < eps. S1 requires the value I_pop_wrong = eps ('gives ε'). The impl does not state the value (any nonzero value satisfies it). It follows only from the definition pop_E + pop_I = eps + 0 and eps + 0 = eps (add_zero, not definitional on Q), which is re-proving S1 without h."

/-- `I_pop_wrong` reads only `pop_E` and `pop_I`, so at the seed state with arbitrary edge
variables it unfolds to the same `ε + 0` as at the impl's literal state. The content
`ε + 0 ≠ 0` comes from `h`. -/
@[sa_forward "SEIREquations.iPopWrongNonzeroAtSeed" 2]
theorem fwd2 (h : sa_impl% "SEIREquations.iPopWrongNonzeroAtSeed") : S2 :=
  fun ε _θ _φE _φI hε => h ε hε

/-- `S2` at the impl's literal edge variables `θ = 1`, `φ_E = ε`, `φ_I = 0`. -/
@[sa_backward "SEIREquations.iPopWrongNonzeroAtSeed"]
theorem bwd (_s1 : S1) (s2 : S2) : sa_impl% "SEIREquations.iPopWrongNonzeroAtSeed" :=
  fun ε hε => s2 ε 1 ε 0 hε

end Alignment.Shadows.SEIREquations.iPopWrongNonzeroAtSeed

/-! ## `SEIREquations.iPopLeWrong` -/
namespace Alignment.Shadows.SEIREquations.iPopLeWrong

sa_claim "SEIREquations.iPopLeWrong" group "SEIREquations" required
  text "**SEIR1b.** I_pop ≤ I_pop_wrong (correct is always ≤ buggy)."
  impl I_pop_le_wrong

@[sa_forward "SEIREquations.iPopLeWrong" 1]
theorem fwd1 (h : sa_impl% "SEIREquations.iPopLeWrong") : S1 :=
  fun s hE => h s hE

@[sa_backward "SEIREquations.iPopLeWrong"]
theorem bwd (s1 : S1) : sa_impl% "SEIREquations.iPopLeWrong" :=
  fun s hE => s1 s hE

end Alignment.Shadows.SEIREquations.iPopLeWrong

/-! ## `SEIREquations.edgeHazardIndependentOfE` -/
namespace Alignment.Shadows.SEIREquations.edgeHazardIndependentOfE

sa_claim "SEIREquations.edgeHazardIndependentOfE" group "SEIREquations" required
  text "**SEIR2.** The edge hazard is independent of φ_E."
  impl edge_hazard_independent_of_E

/-- `{s with φ_E := x}` and `s` have the same `φ_I`, so `h` identifies their edge hazards. -/
@[sa_forward "SEIREquations.edgeHazardIndependentOfE" 1]
theorem fwd1 (h : sa_impl% "SEIREquations.edgeHazardIndependentOfE") : S1 :=
  fun s p x => h { s with φ_E := x } s p rfl

sa_fail_backward "SEIREquations.edgeHazardIndependentOfE" "impl is stronger than the text. edge_hazard_independent_of_E says that s1.phi_I = s2.phi_I implies equal edgeHazard, so the hazard is independent of every field other than phi_I (theta, phi_E, pop_E, pop_I, pop_R). S1 ('independent of φ_E') gives invariance under changing phi_E only. Two states with equal phi_I but different theta or population fields are not related by S1. Closing the gap needs the definition edgeHazard = beta * phi_I, i.e. re-proving the impl without S1."

end Alignment.Shadows.SEIREquations.edgeHazardIndependentOfE

/-! ## `SEIREquations.seirThetaNonincreasing` -/
namespace Alignment.Shadows.SEIREquations.seirThetaNonincreasing

sa_claim "SEIREquations.seirThetaNonincreasing" group "SEIREquations" required
  text "**SEIR4.** θ is non-increasing (same proof as SIR)."
  impl seir_theta_nonincreasing

@[sa_forward "SEIREquations.seirThetaNonincreasing" 1]
theorem fwd1 (h : sa_impl% "SEIREquations.seirThetaNonincreasing") : S1 :=
  fun s p hφ => h s p hφ

@[sa_backward "SEIREquations.seirThetaNonincreasing"]
theorem bwd (s1 : S1) : sa_impl% "SEIREquations.seirThetaNonincreasing" :=
  fun s p hφ => s1 s p hφ

end Alignment.Shadows.SEIREquations.seirThetaNonincreasing

/-! ## seirIGrowthBounded-a -/
namespace Alignment.Shadows.SEIREquations.seirIGrowthBounded_a

sa_claim "SEIREquations.seirIGrowthBounded-a" group "SEIREquations" required
  text "**SEIR5 (auxiliary; not a peak bound).** If σ·pop_E ≤ pop_E + pop_I, then dI/dt ≤ pop_E + pop_I − γ·pop_I. Since dI/dt = σ·pop_E − γ·pop_I, this only restates the hypothesis; it does not compare SEIR with SIR, and σ·pop_E can exceed the SIR incidence."
  impl seir_I_growth_bounded

@[sa_forward "SEIREquations.seirIGrowthBounded-a" 1]
theorem fwd1 (h : sa_impl% "SEIREquations.seirIGrowthBounded-a") : S1 := fun s p hE => h s p hE

sa_fail_forward "SEIREquations.seirIGrowthBounded-a" 2 "S2 (dI/dt = σ·pop_E − γ·pop_I) is the definition of SEIRState.dI (rfl). impl seir_I_growth_bounded states only the bound, so a checker could only prove S2 without h (vacuous)."

@[sa_backward "SEIREquations.seirIGrowthBounded-a"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "SEIREquations.seirIGrowthBounded-a" :=
  fun s p hE => s1 s p hE

end Alignment.Shadows.SEIREquations.seirIGrowthBounded_a
