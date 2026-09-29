import Alignment.Registry
import Alignment.Shadows.VolzMeyersEquations

/-!
# Checkers: group `VolzMeyersEquations`

Checker author (SA-PASS role 3, non-blind). For every claim of `EBCMCategory/VolzMeyersEquations.lean`
with `status: implemented` this file holds the `sa_claim` registration (verbatim registry text,
registry `impl` list), the forward checkers `sa_impl% → Sᵢ`, the backward checker
`S₁ → … → Sₙ → sa_impl%`, and `sa_fail_*` records where a check cannot be proved because the
implementation says something different from the shadow. The blind shadows are in
`Alignment/Shadows/VolzMeyersEquations.lean`.

No bridges are declared. The shadows use the trusted operations (`VMState.dθ`, `dI`, `dR`,
`incidence`, `P_R`, `staticParams`, `vmInitialState`) exactly as the implementation does, so
wherever the shadow and the implementation agree no identification is needed. Where they differ,
the difference is either real content (trajectories, ψ, S, limits, other parameter values) or a
closed formula for one of these one-line operations (e.g. `dθ = −β·P₁·θ` against the
implementation's `-(β * P₁ * θ)`). A bridge stating such a formula would be the claim itself and
would make the checker independent of `h`, so none is used.

Policy (the same as for the sibling group `SEIREquations`). Every operation here is a one-line
definition, so several shadows can be re-proved from scratch by unfolding. A check counts as proved
only when the shadow is an instance or logical consequence of the implementation's statement (or,
backward, the implementation of the shadows) and the hypothesis supplies the content. A check is
recorded as failed when:

* the implementation does not state the property (trajectories, ψ and S, ρ → ∞ limits, the P_S
  equation, other parameter values than the implementation's single instance);
* the only proof would use the hypothesis to supply a definitional triviality while the content
  comes from unfolding a definition (a vacuity dodge, README limitation 1). This covers
  `staticThetaEq-a` and the `dR` / `dθ` shadows of VM8, and the backward checks whose `impl` is
  itself provable by `rfl`;
* the step needs field or order arithmetic on ℚ or ℝ (`neg_mul`, `one_mul`, cancellation,
  `Rat.cast_le`, `Real.exp_pos`, …), which is not structural. Failures that come only from this
  case are marked `formulation only (audit limitation)`.

The `rfl`-failures quoted below were checked: over ℚ, `-(a*b*c) = -a*b*c`, `1*a*b = a*b` and
`a*1 = a` are not definitional equalities (`Rat.mul` normalises by gcd).
-/

/-! ## VM1 -/

namespace Alignment.Shadows.VolzMeyersEquations.table_VM1

sa_claim "VolzMeyersEquations.table.VM1" group "VolzMeyersEquations" required
  text "| VM1 | θ is non-increasing (dθ/dt ≤ 0) |"
  impl theta_nonincreasing

/-- `S1` is the implementation's statement (same binders, same hypotheses). -/
@[sa_forward "VolzMeyersEquations.table.VM1" 1]
theorem fwd1 (h : sa_impl% "VolzMeyersEquations.table.VM1") : S1 :=
  fun s p hP₁ hθ => h s p hP₁ hθ

sa_fail_forward "VolzMeyersEquations.table.VM1" 2 "impl theta_nonincreasing is the sign of the ℚ-valued rate expression s.dθ p (= -(β·P₁·θ)) at a single state with P₁ ≥ 0 and θ ≥ 0. S2 requires monotonicity in time: a real function θ : ℝ → ℝ is Antitone along every trajectory of θ' = -β·P₁(t)·θ(t) with P₁(t) ≥ 0, θ(t) ≥ 0. The impl has no trajectory, no time derivative and no real-valued solution. The step from a non-positive derivative to Antitone needs the mean value theorem (antitone_of_deriv_nonpos) and the order transfer from ℚ to ℝ; the impl states neither and neither is structural."

@[sa_backward "VolzMeyersEquations.table.VM1"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "VolzMeyersEquations.table.VM1" :=
  fun s p hP₁ hθ => s1 s p hP₁ hθ

end Alignment.Shadows.VolzMeyersEquations.table_VM1

namespace Alignment.Shadows.VolzMeyersEquations.thetaNonincreasing

sa_claim "VolzMeyersEquations.thetaNonincreasing" group "VolzMeyersEquations" required
  text "**VM1.** θ is non-increasing: dθ/dt ≤ 0 whenever β > 0, P₁ ≥ 0, θ ≥ 0."
  impl theta_nonincreasing

/-- `S1` is the implementation's statement; β > 0 is the `VMParams.β_pos` field in both. -/
@[sa_forward "VolzMeyersEquations.thetaNonincreasing" 1]
theorem fwd1 (h : sa_impl% "VolzMeyersEquations.thetaNonincreasing") : S1 :=
  fun s p hP₁ hθ => h s p hP₁ hθ

sa_fail_forward "VolzMeyersEquations.thetaNonincreasing" 2 "impl theta_nonincreasing is the sign condition s.dθ p ≤ 0 on the ℚ-valued rate expression at one state with P₁ ≥ 0, θ ≥ 0. S2 (the headline 'θ is non-increasing' read literally) requires θ : ℝ → ℝ to be Antitone along every real trajectory of θ' = -β·P₁(t)·θ(t) with P₁(t) ≥ 0 and θ(t) ≥ 0 at all times. The impl has no trajectory or time derivative. Deriving S2 needs the mean value theorem (antitone_of_deriv_nonpos) and the ℚ → ℝ order transfer, which the impl does not state and which are not structural."

@[sa_backward "VolzMeyersEquations.thetaNonincreasing"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "VolzMeyersEquations.thetaNonincreasing" :=
  fun s p hP₁ hθ => s1 s p hP₁ hθ

end Alignment.Shadows.VolzMeyersEquations.thetaNonincreasing

/-! ## VM2 -/

namespace Alignment.Shadows.VolzMeyersEquations.table_VM2

sa_claim "VolzMeyersEquations.table.VM2" group "VolzMeyersEquations" required
  text "| VM2 | Edge partition: P₁ + P_S + P_R = 1 (where P_R = 1-P₁-P_S) |"
  impl edge_partition

/-- `S1` is the implementation's statement; `P_R` is the operation `VMState.P_R` in both. -/
@[sa_forward "VolzMeyersEquations.table.VM2" 1]
theorem fwd1 (h : sa_impl% "VolzMeyersEquations.table.VM2") : S1 :=
  fun s => h s

@[sa_backward "VolzMeyersEquations.table.VM2"]
theorem bwd (s1 : S1) : sa_impl% "VolzMeyersEquations.table.VM2" :=
  fun s => s1 s

end Alignment.Shadows.VolzMeyersEquations.table_VM2

namespace Alignment.Shadows.VolzMeyersEquations.edgePartition

sa_claim "VolzMeyersEquations.edgePartition" group "VolzMeyersEquations" required
  text "**VM2.** Edge partition: P₁ + P_S + P_R = 1 (by definition of P_R)."
  impl edge_partition

@[sa_forward "VolzMeyersEquations.edgePartition" 1]
theorem fwd1 (h : sa_impl% "VolzMeyersEquations.edgePartition") : S1 :=
  fun s => h s

@[sa_backward "VolzMeyersEquations.edgePartition"]
theorem bwd (s1 : S1) : sa_impl% "VolzMeyersEquations.edgePartition" :=
  fun s => s1 s

end Alignment.Shadows.VolzMeyersEquations.edgePartition

/-! ## VM3 -/

namespace Alignment.Shadows.VolzMeyersEquations.table_VM3

sa_claim "VolzMeyersEquations.table.VM3" group "VolzMeyersEquations" required
  text "| VM3 | Population conservation: d(pop_I + pop_R)/dt = incidence |"
  impl population_influx

/-- `S1` is the implementation's statement (`dI + dR = incidence` at every state). -/
@[sa_forward "VolzMeyersEquations.table.VM3" 1]
theorem fwd1 (h : sa_impl% "VolzMeyersEquations.table.VM3") : S1 :=
  fun s p => h s p

@[sa_backward "VolzMeyersEquations.table.VM3"]
theorem bwd (s1 : S1) : sa_impl% "VolzMeyersEquations.table.VM3" :=
  fun s p => s1 s p

end Alignment.Shadows.VolzMeyersEquations.table_VM3

namespace Alignment.Shadows.VolzMeyersEquations.populationInflux_a

sa_claim "VolzMeyersEquations.populationInflux-a" group "VolzMeyersEquations" required
  text "**VM3.** Population dynamics: d(I + R)/dt = incidence."
  impl population_influx

@[sa_forward "VolzMeyersEquations.populationInflux-a" 1]
theorem fwd1 (h : sa_impl% "VolzMeyersEquations.populationInflux-a") : S1 :=
  fun s p => h s p

@[sa_backward "VolzMeyersEquations.populationInflux-a"]
theorem bwd (s1 : S1) : sa_impl% "VolzMeyersEquations.populationInflux-a" :=
  fun s p => s1 s p

end Alignment.Shadows.VolzMeyersEquations.populationInflux_a

/-! ## VM4 -/

namespace Alignment.Shadows.VolzMeyersEquations.table_VM4

sa_claim "VolzMeyersEquations.table.VM4" group "VolzMeyersEquations" required
  text "| VM4 | S is non-increasing (follows from VM1 and PGF monotonicity) |"
  impl S_nonincreasing

sa_fail_forward "VolzMeyersEquations.table.VM4" 1 "impl S_nonincreasing states only p.κ * s.dθ p ≤ 0 over ℚ, under 0 ≤ P₁, 0 ≤ θ and the extra hypothesis 0 < p.κ. S does not appear. S1 requires psi1 q θ * (dθ : ℝ) ≤ 0, i.e. dS/dt = ψ'(θ)·dθ/dt ≤ 0, for every degree distribution q and every parameter set (no κ > 0 hypothesis), at states with 0 ≤ θ ≤ 1. The factor ψ'(θ) is a real tsum, not the free scalar κ. Deriving S1 needs 0 ≤ ψ'(θ) (tsum_nonneg from the degree distribution), dθ ≤ 0 from κ·dθ ≤ 0 and κ > 0 (division, and unavailable when κ ≤ 0), the cast Rat.cast_nonpos and mul_nonpos_of_nonneg_of_nonpos. None of these is stated by the impl or structural."

sa_fail_forward "VolzMeyersEquations.table.VM4" 2 "impl is a sign statement about the ℚ-valued product κ·dθ at one state. S2 requires S(t) = ψ(θ(t)) to be Antitone along every real trajectory of θ' = -β·P₁·θ with P₁ ≥ 0 and θ ∈ [0,1], for every PGF ψ. The impl has no ψ, no S and no trajectory. The proof needs PGF monotonicity on [0,1] (termwise tsum comparison), the mean value theorem and the ℚ → ℝ transfer, none of which the impl states."

sa_fail_backward "VolzMeyersEquations.table.VM4" "impl is about the free scalar κ (free-scalar abstraction): p.κ * s.dθ p ≤ 0 over ℚ at every state with P₁ ≥ 0, θ ≥ 0 and κ > 0, including states with θ > 1. S1 constrains ψ'(θ)·dθ in ℝ for a PGF ψ and only at 0 ≤ θ ≤ 1, and S2 concerns trajectories. S1 gives nothing at θ > 1. At θ ≤ 1, turning psi1 q θ * dθ ≤ 0 into κ·dθ ≤ 0 needs a concrete PGF with ψ' ≡ 1 (evaluating a tsum), Rat.cast_le to return to ℚ, and mul_nonpos with κ > 0. That is not structural, and the impl's κ is not ψ'(θ)."

end Alignment.Shadows.VolzMeyersEquations.table_VM4

namespace Alignment.Shadows.VolzMeyersEquations.sNonincreasing_a

sa_claim "VolzMeyersEquations.sNonincreasing-a" group "VolzMeyersEquations" required
  text "**VM4.** S is non-increasing (for Poisson PGF, S = exp(κ(θ-1))). Since θ is non-increasing (VM1) and exp is monotone, S is non-increasing."
  impl S_nonincreasing

sa_fail_forward "VolzMeyersEquations.sNonincreasing-a" 1 "impl S_nonincreasing is a pointwise sign statement p.κ * s.dθ p ≤ 0 over ℚ. S1 requires t ↦ exp(κ(θ(t) - 1)) to be Antitone along every real trajectory of θ' = -β·P₁·θ with P₁ ≥ 0 and θ ≥ 0. The impl mentions neither S = exp(κ(θ-1)) nor a trajectory. The proof needs the mean value theorem, monotonicity of Real.exp and the ℚ → ℝ transfer, none of which the impl states."

sa_fail_forward "VolzMeyersEquations.sNonincreasing-a" 2 "impl states p.κ * s.dθ p ≤ 0 over ℚ. S2 requires deriv (fun x => Real.exp (κ(x-1))) θ * (dθ : ℝ) ≤ 0 over ℝ, i.e. dS/dt ≤ 0 for S = exp(κ(θ-1)). The impl mentions neither exp nor S. Closing the gap needs the derivative computation deriv = κ·exp(κ(θ-1)) (HasDerivAt.exp, a library theorem), Real.exp_pos, the casts Rat.cast_mul and Rat.cast_nonpos, and mul_nonpos after reassociation. The two agree only up to the positive factor exp(κ(θ-1)), which the impl omits. None of this is structural."

sa_fail_backward "VolzMeyersEquations.sNonincreasing-a" "impl p.κ * s.dθ p ≤ 0 (over ℚ) follows from S2 only through analysis and order steps that are not structural: computing deriv (fun x => exp(κ(x-1))) θ = κ·exp(κ(θ-1)), cancelling exp(κ(θ-1)) > 0, and reflecting the real inequality back to ℚ (Rat.cast_le). S1 is about real trajectories and gives no pointwise statement about the ℚ rate."

end Alignment.Shadows.VolzMeyersEquations.sNonincreasing_a

/-! ## sNonincreasing-b -/
namespace Alignment.Shadows.VolzMeyersEquations.sNonincreasing_b

sa_claim "VolzMeyersEquations.sNonincreasing-b" group "VolzMeyersEquations" required
  text "Motivated by: dS/dt = κ·S·dθ/dt ≤ 0 when κ > 0. The Lean statement is only κ·dθ/dt ≤ 0 (the factor S ≥ 0 is omitted); nothing is proved about S along solutions."
  impl S_nonincreasing

sa_fail_forward "VolzMeyersEquations.sNonincreasing-b" 1 "impl S_nonincreasing is the rational sign statement κ·dθ ≤ 0 at a state. S1 is the real chain rule dS/dt = κ·S·dθ/dt for S = exp(κ(θ − 1)) along a curve θ. The text says 'nothing is proved about S along solutions', and impl indeed has no derivative, curve or exponential."

sa_fail_forward "VolzMeyersEquations.sNonincreasing-b" 2 "impl gives κ·dθ ≤ 0; S2 is κ·S·dθ ≤ 0 for S ≥ 0. The text notes that impl omits the factor S. Inserting it needs mul_nonpos_of_nonneg_of_nonpos-type ordered-ring lemmas (and reassociation), which are not structural."

sa_fail_backward "VolzMeyersEquations.sNonincreasing-b" "impl (κ·dθ ≤ 0) would follow from S2 at S = 1 only after κ·1·dθ = κ·dθ (mul_one, not definitional in ℚ for variable κ and dθ). S1 is about real curves and does not help, so impl is not structurally derivable from the shadows."

end Alignment.Shadows.VolzMeyersEquations.sNonincreasing_b

/-! ## VM5 -/

namespace Alignment.Shadows.VolzMeyersEquations.table_VM5

sa_claim "VolzMeyersEquations.table.VM5" group "VolzMeyersEquations" required
  text "| VM5 | Static limit (ρ=0): θ̇ = −β P₁ θ reduces to static EBCM |"
  impl static_theta_eq

sa_fail_forward "VolzMeyersEquations.table.VM5" 1 "Formulation only (audit limitation). impl static_theta_eq states s.dθ (staticParams β γ κ hβ hγ) = -(β * s.P₁ * s.θ). S1 requires the same left-hand side to equal -β * s.P₁ * s.θ, i.e. ((-β) * P₁) * θ. The right-hand sides are equal over ℚ only via the ring lemma neg_mul (applied twice). They are not definitionally equal (rfl fails; Rat.mul normalises by gcd). The only trusted definition in the statement is VMState.dθ. A bridge dθ s p = -p.β * s.P₁ * s.θ would be the claim itself and would make the checker independent of h, so no bridge is used. The impl also names no static EBCM, so 'reduces to static EBCM' is carried only by the shadow's reading of −β P₁ θ as the static θ-equation."

sa_fail_backward "VolzMeyersEquations.table.VM5" "Formulation only (audit limitation). From S1 (dθ at staticParams = (-β)·P₁·θ), the impl's right-hand side -(β·P₁·θ) follows only via neg_mul, which is not definitional over ℚ. The impl is itself the definitional unfolding of dθ at ρ = 0 (provable by rfl). A proof by rfl would ignore S1 and re-prove the impl from the definition rather than derive it from the shadow, so it was not used."

end Alignment.Shadows.VolzMeyersEquations.table_VM5

namespace Alignment.Shadows.VolzMeyersEquations.staticThetaEq_a

sa_claim "VolzMeyersEquations.staticThetaEq-a" group "VolzMeyersEquations" required
  text "**VM5.** In the static limit, the θ equation dθ/dt = −β P₁ θ is independent of ρ"
  impl static_theta_eq

sa_fail_forward "VolzMeyersEquations.staticThetaEq-a" 1 "impl static_theta_eq evaluates dθ at one swap rate only, staticParams with ρ = 0: s.dθ (staticParams β γ κ hβ hγ) = -(β·P₁·θ). S1 requires dθ to agree at two arbitrary swap rates ρ₁ and ρ₂ (independence of ρ). The impl does not state that. The equality holds only because the definition of VMState.dθ does not read p.ρ. A checker could unfold dθ at ρ₁ and ρ₂ to -(β·P₁·θ) and cite h. But h would then supply only a definitional fact (the impl is provable by rfl), and the ρ-independence would come from unfolding the definition, which is re-proving S1 without h (vacuity dodge, README limitation 1)."

sa_fail_forward "VolzMeyersEquations.staticThetaEq-a" 2 "S2 requires s.dθ p = s.dθ (staticParams p.β p.γ p.κ p.β_pos p.γ_pos) for every parameter set p. That is, dθ at an arbitrary swap rate equals its value at ρ = 0. impl gives only the value at ρ = 0. The value at arbitrary p, and so the equality, comes only from unfolding VMState.dθ, not from h. The term (h s p.β p.γ p.κ p.β_pos p.γ_pos).symm does type-check against S2, because s.dθ p unfolds to -(p.β·P₁·θ). But the ρ-independence content would come from that unfolding, and h (itself an rfl-provable unfolding) would supply only a definitional triviality (vacuity dodge, README limitation 1). So it was not used."

sa_fail_backward "VolzMeyersEquations.staticThetaEq-a" "impl states the value -(β·P₁·θ) of dθ at ρ = 0. S1 and S2 state only that dθ does not depend on ρ. They do not determine its value: every ρ-free rate satisfies both (e.g. dθ := 0, or +β·P₁·θ), which would violate the impl. In the text the formula 'dθ/dt = −β P₁ θ' names the equation whose ρ-independence is asserted, and the shadows accordingly do not require it. The impl holds by rfl from the definition of VMState.dθ. That would re-prove the impl without the shadows and is not a derivation from S1 and S2."

end Alignment.Shadows.VolzMeyersEquations.staticThetaEq_a

/-! ## table.VM6 -/
namespace Alignment.Shadows.VolzMeyersEquations.table_VM6

sa_claim "VolzMeyersEquations.table.VM6" group "VolzMeyersEquations" required
  text "| VM6 | Swap term ρ(M₁ − P₁) vanishes at P₁ = M₁ (fast-mixing motivation) |"
  impl fast_mixing_P1_equilibrium

@[sa_forward "VolzMeyersEquations.table.VM6" 1]
theorem fwd1 (h : sa_impl% "VolzMeyersEquations.table.VM6") : S1 := fun s p hs => h s hs p

@[sa_backward "VolzMeyersEquations.table.VM6"]
theorem bwd (s1 : S1) : sa_impl% "VolzMeyersEquations.table.VM6" := fun s hs p => s1 s p hs

end Alignment.Shadows.VolzMeyersEquations.table_VM6

namespace Alignment.Shadows.VolzMeyersEquations.fastMixingP1Equilibrium_a

sa_claim "VolzMeyersEquations.fastMixingP1Equilibrium-a" group "VolzMeyersEquations" required
  text "**VM6.** In the fast-mixing limit, P₁ → M₁"
  impl fast_mixing_P1_equilibrium

sa_fail_forward "VolzMeyersEquations.fastMixingP1Equilibrium-a" 1 "impl fast_mixing_P1_equilibrium states only s.P₁ = s.M₁ → p.ρ * (s.M₁ - s.P₁) = 0 (the swap term vanishes at P₁ = M₁, at a fixed ρ). No ρ → ∞ limit and no convergence P₁ → M₁ is stated. S1 requires, for every ε > 0, some R such that for all ρ > R every root x ∈ [0,1] of the Ṗ₁ right-hand side rateP1 lies within ε of M₁. That needs a quantitative estimate of the non-swap terms and an Archimedean choice of R. The impl states none of this, and none of it is structural."

sa_fail_backward "VolzMeyersEquations.fastMixingP1Equilibrium-a" "impl states ρ(M₁ - P₁) = 0 whenever P₁ = M₁, for every ρ including ρ = 0. S1 is an asymptotic statement about the roots of rateP1 in ℝ for large ρ, and gives no information about the ℚ expression ρ(M₁ - P₁). The impl follows from its hypothesis only via sub_self and mul_zero over ℚ, i.e. by re-proving it without S1."

end Alignment.Shadows.VolzMeyersEquations.fastMixingP1Equilibrium_a

/-! ## fastMixingP1Equilibrium-d -/
namespace Alignment.Shadows.VolzMeyersEquations.fastMixingP1Equilibrium_d

sa_claim "VolzMeyersEquations.fastMixingP1Equilibrium-d" group "VolzMeyersEquations" required
  text "Motivated by: the swap terms ρ(M₁ − P₁) and ρ(ψ'(θ)/ψ'(1) − P_S) drive P₁ and P_S to their population-level values at rate ρ. The Lean statement is only that the swap term ρ(M₁ − P₁) vanishes when P₁ = M₁; no limit ρ → ∞ is formalised."
  impl fast_mixing_P1_equilibrium

sa_fail_forward "VolzMeyersEquations.fastMixingP1Equilibrium-d" 1 "impl fast_mixing_P1_equilibrium is only the algebraic fact ρ(M₁ − P₁) = 0 when P₁ = M₁; the text says 'no limit ρ → ∞ is formalised'. S1 (solutions of P′ = ρ(M₁ − P) relax to M₁ as (P(0) − M₁)e^{−ρt}) is a statement about ODE solutions that impl does not make."

sa_fail_forward "VolzMeyersEquations.fastMixingP1Equilibrium-d" 2 "impl is the algebraic vanishing of the P₁ swap term. S2 (solutions of P′ = ρ(c − P), the P_S swap, relax to c at rate ρ) is about ODE solutions and about the P_S term, neither of which impl mentions."

sa_fail_backward "VolzMeyersEquations.fastMixingP1Equilibrium-d" "impl (ρ(M₁ − P₁) = 0 when P₁ = M₁, over ℚ) is an algebraic identity at a state. The shadows describe real ODE solutions and do not give it. Proving it needs sub_self and mul_zero, which are not structural in any case."

end Alignment.Shadows.VolzMeyersEquations.fastMixingP1Equilibrium_d

/-! ## VM7 (initial conditions) -/

namespace Alignment.Shadows.VolzMeyersEquations.icEdgePartition

sa_claim "VolzMeyersEquations.icEdgePartition" group "VolzMeyersEquations" required
  text "**VM7.** IC consistency: the edge partition holds at t=0."
  impl ic_edge_partition

/-- `S1` is the implementation's statement at `vmInitialState sf`. -/
@[sa_forward "VolzMeyersEquations.icEdgePartition" 1]
theorem fwd1 (h : sa_impl% "VolzMeyersEquations.icEdgePartition") : S1 :=
  fun sf => h sf

@[sa_backward "VolzMeyersEquations.icEdgePartition"]
theorem bwd (s1 : S1) : sa_impl% "VolzMeyersEquations.icEdgePartition" :=
  fun sf => s1 sf

end Alignment.Shadows.VolzMeyersEquations.icEdgePartition

namespace Alignment.Shadows.VolzMeyersEquations.icPopulation

sa_claim "VolzMeyersEquations.icPopulation" group "VolzMeyersEquations" required
  text "**VM7b.** IC consistency: I(0) + R(0) = sf."
  impl ic_population

@[sa_forward "VolzMeyersEquations.icPopulation" 1]
theorem fwd1 (h : sa_impl% "VolzMeyersEquations.icPopulation") : S1 :=
  fun sf => h sf

@[sa_backward "VolzMeyersEquations.icPopulation"]
theorem bwd (s1 : S1) : sa_impl% "VolzMeyersEquations.icPopulation" :=
  fun sf => s1 sf

end Alignment.Shadows.VolzMeyersEquations.icPopulation

namespace Alignment.Shadows.VolzMeyersEquations.icTheta

sa_claim "VolzMeyersEquations.icTheta" group "VolzMeyersEquations" required
  text "**VM7c.** IC consistency: θ(0) = 1 (no transmission at t=0)."
  impl ic_theta

/-- `S1` is the implementation's statement. Both hold by `rfl` from `vmInitialState`, so this
pass is weak evidence (the shadow is literally the implementation). -/
@[sa_forward "VolzMeyersEquations.icTheta" 1]
theorem fwd1 (h : sa_impl% "VolzMeyersEquations.icTheta") : S1 :=
  fun sf => h sf

@[sa_backward "VolzMeyersEquations.icTheta"]
theorem bwd (s1 : S1) : sa_impl% "VolzMeyersEquations.icTheta" :=
  fun sf => s1 sf

end Alignment.Shadows.VolzMeyersEquations.icTheta

/-! ## table.VM8 -/
namespace Alignment.Shadows.VolzMeyersEquations.table_VM8

sa_claim "VolzMeyersEquations.table.VM8" group "VolzMeyersEquations" required
  text "| VM8 | Mass-action recovery for ψ(x)=x (k=1) in the fast-mixing limit |"
  impl mass_action_incidence

sa_fail_forward "VolzMeyersEquations.table.VM8" 1 "impl mass_action_incidence states only incidence = I·S for the one parameter record β = γ = κ = 1, ρ = 0 and the state (S, I, 1 − I, I, I, 0). S1 (dθ = −β·I·θ whenever P₁ = I, for all parameters) is about dθ, which impl does not mention. Also dθ is −(β·P₁·θ), which equals −β·I·θ only by neg_mul (not definitional in ℚ)."

sa_fail_forward "VolzMeyersEquations.table.VM8" 2 "S2 (dI = β·I·θ − γ·I whenever κ = 1 and P₁ = I, for all β, γ, ρ) is universal over parameters. impl covers only β = γ = κ = 1, ρ = 0 and states incidence = I·S rather than dI. Even at those parameters, β·I·θ·1 = β·I·θ needs mul_one (not definitional in ℚ)."

sa_fail_forward "VolzMeyersEquations.table.VM8" 3 "S3 (dR = γ·I) is the definition of VMState.dR (rfl). impl does not state it, so a checker could only prove S3 without h (vacuous)."

sa_fail_backward "VolzMeyersEquations.table.VM8" "impl (incidence = I·S at the specific record) does not follow structurally from the shadows. S2 at that record gives incidence − 1·I = 1·I·S − 1·I, and cancelling needs sub_left_inj / one_mul in ℚ, which are not structural."

end Alignment.Shadows.VolzMeyersEquations.table_VM8

/-! ## massActionIncidence-a -/
namespace Alignment.Shadows.VolzMeyersEquations.massActionIncidence_a

sa_claim "VolzMeyersEquations.massActionIncidence-a" group "VolzMeyersEquations" required
  text "**VM8.** For a homogeneous network with ψ(x) = x (every node has degree 1, κ=1), the VM model reduces to the standard SIR in the fast-mixing limit ρ → ∞. At ρ = 0 it describes isolated pairs, not mass action. In the fast-mixing limit: S = θ, P₁ = I, and the equations become dS/dt = −β·I·S, dI/dt = β·I·S − γ·I, dR/dt = γ·I."
  impl mass_action_incidence

sa_fail_forward "VolzMeyersEquations.massActionIncidence-a" 1 "impl mass_action_incidence states only incidence = I·S for the single record β = γ = κ = 1, ρ = 0. S1 (dθ = −β·I·θ whenever P₁ = I) is about dθ, which impl does not mention; dθ is −(β·P₁·θ), equal to −β·I·θ only by neg_mul."

sa_fail_forward "VolzMeyersEquations.massActionIncidence-a" 2 "S2 (dI = β·I·θ − γ·I for κ = 1 and P₁ = I, all β, γ) is universal over parameters. impl covers only β = γ = κ = 1, ρ = 0 and states incidence rather than dI; β·I·θ·1 = β·I·θ needs mul_one."

sa_fail_forward "VolzMeyersEquations.massActionIncidence-a" 3 "S3 (dR = γ·I) is the definition of VMState.dR (rfl). impl does not state it, so a checker could only prove S3 without h (vacuous)."

sa_fail_forward "VolzMeyersEquations.massActionIncidence-a" 4 "S4 (for ψ(x) = x, the M₁ equation −γM₁ + βP₁θ equals dI when M₁ = I) relates the M₁ and I equations of the model. impl states only the incidence value at one record, and matching β·P₁·θ with β·P₁·θ·κ at κ = 1 needs mul_one."

sa_fail_backward "VolzMeyersEquations.massActionIncidence-a" "impl (incidence = I·S at the specific record) is not structurally derivable from the shadows. S2 at that record gives dI = 1·I·S − 1·I, and extracting incidence = I·S needs cancellation (sub_left_inj) and one_mul in ℚ."

end Alignment.Shadows.VolzMeyersEquations.massActionIncidence_a

namespace Alignment.Shadows.VolzMeyersEquations.massActionIncidence_b

sa_claim "VolzMeyersEquations.massActionIncidence-b" group "VolzMeyersEquations" required
  text "We verify that the incidence = β·P₁·θ·κ = β·I·S when κ=1 and P₁=I, θ=S."
  impl mass_action_incidence

sa_fail_forward "VolzMeyersEquations.massActionIncidence-b" 1 "impl fixes β = 1, together with γ = 1, κ = 1 and ρ = 0, and a single state shape ⟨S, I, 1-I, I, I, 0⟩ (P_S = 1-I, M₁ = I, R = 0). S1 requires incidence = β·I·θ for every β and every state and parameter set with P₁ = I and κ = 1. The impl gives nothing for β ≠ 1 or for other P_S, M₁, R, γ, ρ. The general identity holds only from the definition incidence = β·P₁·θ·κ with the rewrite P₁ = I and mul_one (not definitional over ℚ), so it would be re-proved without h."

sa_fail_backward "VolzMeyersEquations.massActionIncidence-b" "Formulation only (audit limitation). S1 at the impl's state ⟨S, I, 1-I, I, I, 0⟩ and parameters ⟨1, 1, 0, 1, …⟩ (κ = 1 and P₁ = I hold by rfl) gives incidence = 1·I·S. The impl states incidence = I·S. The step 1·I·S = I·S is one_mul over ℚ. It is not definitional (rfl fails, because Rat.mul normalises by gcd) and not structural, and no trusted definition could carry it in a bridge."

end Alignment.Shadows.VolzMeyersEquations.massActionIncidence_b

/-! ## `VolzMeyersEquations.fastMixingP1Equilibrium-b` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.VolzMeyersEquations.fastMixingP1Equilibrium_b

sa_claim "VolzMeyersEquations.fastMixingP1Equilibrium-b" group "VolzMeyersEquations"
  text "and P_S → ψ'(θ)/ψ'(1)."
  impl

end Alignment.Shadows.VolzMeyersEquations.fastMixingP1Equilibrium_b

/-! ## `VolzMeyersEquations.header.popIEquation` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.VolzMeyersEquations.header_popIEquation

sa_claim "VolzMeyersEquations.header.popIEquation" group "VolzMeyersEquations"
  text "| pop_I | = β P₁ θ ψ'(θ) − γ pop_I | [...] The Lean incidence β·P₁·θ·κ. The Volz–Meyers incidence is β·P₁·θ·ψ'(θ); for Poisson, ψ'(θ) = κ·ψ(θ), so it is β·P₁·θ·κ·ψ(θ). This definition drops the factor ψ(θ) and agrees with the model only while ψ(θ) = 1, i.e. at θ = 1."
  impl

end Alignment.Shadows.VolzMeyersEquations.header_popIEquation

/-! ## `VolzMeyersEquations.populationInflux-b` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.VolzMeyersEquations.populationInflux_b

sa_claim "VolzMeyersEquations.populationInflux-b" group "VolzMeyersEquations"
  text "This is the influx of newly infected from the susceptible pool, with the Lean incidence (which drops the factor ψ(θ); see `VMState.incidence`)."
  impl

end Alignment.Shadows.VolzMeyersEquations.populationInflux_b

/-! ## `VolzMeyersEquations.table.VM7` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.VolzMeyersEquations.table_VM7

sa_claim "VolzMeyersEquations.table.VM7" group "VolzMeyersEquations"
  text "| VM7 | IC bookkeeping: with S(0) = ψ(1) = 1, S(0) + pop_I(0) + pop_R(0) = 1 + sf |"
  impl

end Alignment.Shadows.VolzMeyersEquations.table_VM7
