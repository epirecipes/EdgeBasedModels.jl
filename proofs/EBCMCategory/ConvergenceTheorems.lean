import EBCMCategory.EpiCategory
import Mathlib.Tactic

/-!
# Convergence and Exactness Theorems

States scalar identities motivated by convergence results connecting the
edge-based compartmental model (EBCM) to classical mass-action SIR, the
exactness of pair approximations on trees, the final-size fixed-point equation
and CLT scaling, together with PGF moment identities, R₀ amplification by
degree heterogeneity and the epidemic threshold. No convergence result, limit
theorem or ODE solution is formalised; the tree-exactness and CLT results are
cited prose (Results 106 and 111).

## References

* Rempała GA (2023). Equivalence of mass action and Poisson network SIR
  epidemic models. arXiv:2310.13866.
* Sharkey KJ, Kiss IZ, Wilkinson RR, Simon PL (2015). Exact equations for
  SIR epidemics on tree graphs. Bull Math Biol 77:614–645
  (doi:10.1007/s11538-013-9923-5).
* Ball F (2021). Central limit theorems for SIR epidemics and percolation
  on configuration model random graphs. Ann Appl Probab 31:2091–2142.
-/

noncomputable section

open Real

/-! ## Poisson EBCM parameters -/

/-- Data for the Poisson-network EBCM: Poisson(κ) degree distribution
with per-edge transmission rate β̃ and recovery rate γ̃. -/
structure PoissonEBCMData where
  kappa : ℝ          -- Poisson mean degree
  beta_tilde : ℝ     -- per-edge transmission rate
  gamma_tilde : ℝ    -- recovery rate
  kappa_pos : 0 < kappa
  beta_tilde_pos : 0 < beta_tilde
  gamma_tilde_pos : 0 < gamma_tilde

/-! ## Result 105: Poisson network ≡ mass-action (Rempała 2025)

For a Poisson(κ) degree distribution with per-edge transmission rate β̃ and
recovery γ̃, the susceptible curve S(t) of the EBCM coincides with that of
classical SIR with effective rates:
  β = κ β̃     and     γ = γ̃ + β̃;
the infected curves differ (Rempała 2023).

Key algebraic identity: the Poisson EBCM ODE
  θ̇ = -β̃ θ + β̃ exp(κ(θ-1)) + γ̃(1-θ)
reduces to dS/dt = -β S I when S = exp(κ(θ-1)) and I := φ_I (the probability
that a partner is infectious and has not yet transmitted), not the network
prevalence.

We verify the effective-rate identities algebraically. -/

/-- **Result 105a.** Effective mass-action transmission rate: β = κ β̃. -/
def effective_beta (d : PoissonEBCMData) : ℝ :=
  d.kappa * d.beta_tilde

/-- **Result 105b.** Effective mass-action recovery rate: γ = γ̃ + β̃. -/
def effective_gamma (d : PoissonEBCMData) : ℝ :=
  d.gamma_tilde + d.beta_tilde

/-- Effective β is positive. -/
theorem effective_beta_pos (d : PoissonEBCMData) : 0 < effective_beta d := by
  unfold effective_beta
  exact mul_pos d.kappa_pos d.beta_tilde_pos

/-- Effective γ is positive. -/
theorem effective_gamma_pos (d : PoissonEBCMData) : 0 < effective_gamma d := by
  unfold effective_gamma
  linarith [d.gamma_tilde_pos, d.beta_tilde_pos]

/-- **Result 105c.** Transmissibility consistency: with β = κβ̃ and
γ = γ̃ + β̃, the mass-action R₀ is β/γ = κβ̃/(β̃ + γ̃).
With the edge-based transmissibility T_edge = β̃/(β̃ + γ̃), the mass-action
R₀ is exactly T_edge · κ, the Poisson EBCM R₀ (`R0_massAction_eq_edge`).
There is no large-κ approximation: the two R₀ agree for every κ.

Here we verify the simpler identity: κ · β̃/(β̃ + γ̃) = κβ̃/(β̃ + γ̃). -/
theorem poisson_R0_edge_formula (kappa beta_tilde gamma_tilde : ℝ)
    (_hb : 0 < beta_tilde) (_hg : 0 < gamma_tilde) :
    kappa * (beta_tilde / (beta_tilde + gamma_tilde)) =
    kappa * beta_tilde / (beta_tilde + gamma_tilde) := by
  ring

/-- **Result 105d.** The Poisson PGF identity: for ψ(x) = exp(κ(x-1)),
ψ'(x) = κ·exp(κ(x-1)), so ψ'(1) = κ and ψ''(1) = κ².
Thus the excess degree ratio ψ''(1)/ψ'(1) = κ²/κ = κ. -/
theorem poisson_excess_degree_real (kappa : ℝ) (hk : 0 < kappa) :
    kappa ^ 2 / kappa = kappa := by
  have hk' : kappa ≠ 0 := ne_of_gt hk
  field_simp

/-- **Result 105e.** S-substitution identity: if S = exp(κ(θ-1)) and θ̇ = f(θ),
then dS/dt = κ·S·θ̇. This is the chain rule d/dt[exp(κ(θ-1))] = κ·exp(κ(θ-1))·θ̇.
The Lean statement `kappa * S = kappa * S` is tautological: it holds by
reflexivity. The chain rule itself is `S_theta_chain_rule`. -/
theorem S_theta_chain_rule_coeff (kappa S : ℝ) :
    kappa * S = kappa * S := by ring

/-- The mass-action R₀ β/γ with β = κβ̃ and γ = γ̃ + β̃ equals the Poisson
    EBCM R₀ κ · T_edge = κ · β̃/(β̃ + γ̃), exactly. -/
theorem R0_massAction_eq_edge (d : PoissonEBCMData) :
    effective_beta d / effective_gamma d =
      d.kappa * (d.beta_tilde / (d.beta_tilde + d.gamma_tilde)) := by
  unfold effective_beta effective_gamma
  rw [add_comm d.gamma_tilde]
  ring

/-- The chain rule behind Result 105e: if `θ` has derivative `θ'` at `t`, then
    `S = exp(κ(θ − 1))` has derivative `κ · S · θ'` at `t`. -/
theorem S_theta_chain_rule (kappa : ℝ) {θ : ℝ → ℝ} {θ' t : ℝ}
    (h : HasDerivAt θ θ' t) :
    HasDerivAt (fun s => Real.exp (kappa * (θ s - 1)))
      (kappa * Real.exp (kappa * (θ t - 1)) * θ') t := by
  have := ((h.sub_const 1).const_mul kappa).exp
  convert this using 1
  ring

/-! ## Result 106: Tree-exactness of pair closure (Sharkey et al 2015)

On tree networks (no cycles), the pair approximation is exact. Precisely
(Sharkey, Kiss, Wilkinson and Simon 2015, Theorem 1.1): for Markovian SIR
dynamics on a network whose underlying graph is a tree, started from a pure
state (or from uncorrelated initial node states), the individual-level closure
(A_i S_j B_k)·(S_j) = (A_i S_j)·(S_j B_k) holds exactly for every triple in
the pair equations, so the closed pair-based system reproduces the exact node
and pair probabilities.

**Result 106** (not formalised; cited). This library models no contact
network, pair probabilities or ODE solutions, so the result has no Lean
counterpart. (The former axiom `tree_pair_exactness` was stated over two
unconstrained type classes and was inconsistent: the instances `⟨True⟩` and
`⟨1⟩` on `Unit` gave `(1 : ℝ) = 0`. It has been removed together with those
classes.) -/

/-! ## PGF moment data for Results 107–112

We use ℝ-valued moments for the convergence and threshold results. -/

/-- PGF moment data over ℝ with mean, second factorial moment, and variance. -/
structure PGFMoments where
  mean : ℝ                -- ⟨k⟩ = ψ'(1)
  secondFactorial : ℝ     -- ⟨k(k-1)⟩ = ψ''(1)
  variance : ℝ             -- Var(k)
  mean_pos : 0 < mean
  secondFactorial_nonneg : 0 ≤ secondFactorial
  variance_nonneg : 0 ≤ variance
  /-- The consistency relation: ⟨k²⟩ = ⟨k(k-1)⟩ + ⟨k⟩ and Var = ⟨k²⟩ - ⟨k⟩²,
  so Var = ⟨k(k-1)⟩ + ⟨k⟩ - ⟨k⟩². -/
  variance_eq : variance = secondFactorial + mean - mean ^ 2

/-- The excess degree ratio ψ''(1)/ψ'(1). -/
def PGFMoments.excessDegree (m : PGFMoments) : ℝ :=
  m.secondFactorial / m.mean

/-- Second moment ⟨k²⟩ = ⟨k(k-1)⟩ + ⟨k⟩. -/
def PGFMoments.secondMoment (m : PGFMoments) : ℝ :=
  m.secondFactorial + m.mean

/-! ## Result 107: Excess degree ratio identity

For any PGF ψ with ψ(1)=1, ψ'(1)=⟨k⟩, ψ''(1)=⟨k(k-1)⟩, the excess degree
ratio has two equivalent forms:
  ψ''(1)/ψ'(1) = (⟨k²⟩ - ⟨k⟩)/⟨k⟩ = ⟨k⟩ + Var(k)/⟨k⟩ - 1. -/

/-- **Result 107a.** ψ''(1)/ψ'(1) = (⟨k²⟩ - ⟨k⟩)/⟨k⟩. -/
theorem excess_degree_second_moment (m : PGFMoments) :
    m.excessDegree = (m.secondMoment - m.mean) / m.mean := by
  unfold PGFMoments.excessDegree PGFMoments.secondMoment
  ring

/-- **Result 107b.** (⟨k²⟩ - ⟨k⟩)/⟨k⟩ = ⟨k⟩ + Var(k)/⟨k⟩ - 1.

This is the key identity linking excess degree to mean and variance. -/
theorem excess_degree_variance_form (m : PGFMoments) :
    m.excessDegree = m.mean + m.variance / m.mean - 1 := by
  unfold PGFMoments.excessDegree
  rw [m.variance_eq]
  have hm : m.mean ≠ 0 := ne_of_gt m.mean_pos
  field_simp
  ring

/-- **Result 107c.** The two forms are equal: (⟨k²⟩-⟨k⟩)/⟨k⟩ = ⟨k⟩+Var/⟨k⟩-1. -/
theorem excess_degree_forms_agree (m : PGFMoments) :
    (m.secondMoment - m.mean) / m.mean = m.mean + m.variance / m.mean - 1 := by
  rw [← excess_degree_second_moment, excess_degree_variance_form]

/-! ## Result 108: R₀ amplification by heterogeneity

R₀ = T · (⟨k⟩ + Var(k)/⟨k⟩ - 1). Since Var(k) ≥ 0, heterogeneity always
amplifies R₀ compared to a homogeneous (regular) network where R₀ = T·(k-1). -/

/-- R₀ for a heterogeneous network with transmissibility T. -/
def R0_heterogeneous (T : ℝ) (m : PGFMoments) : ℝ :=
  T * m.excessDegree

/-- R₀ for a homogeneous (regular) network where every node has degree k. -/
def R0_homogeneous (T : ℝ) (k : ℝ) : ℝ :=
  T * (k - 1)

/-- **Result 108a.** R₀ = T · (⟨k⟩ + Var(k)/⟨k⟩ - 1). -/
theorem R0_variance_formula (T : ℝ) (m : PGFMoments) :
    R0_heterogeneous T m = T * (m.mean + m.variance / m.mean - 1) := by
  unfold R0_heterogeneous
  rw [excess_degree_variance_form]

/-- **Result 108b.** Heterogeneity amplifies R₀: for any degree distribution
with mean ⟨k⟩ and Var ≥ 0, R₀ ≥ T·(⟨k⟩ - 1) = R₀(homogeneous). -/
theorem R0_heterogeneity_amplifies (T : ℝ) (m : PGFMoments)
    (hT : 0 ≤ T) :
    R0_homogeneous T m.mean ≤ R0_heterogeneous T m := by
  unfold R0_homogeneous R0_heterogeneous PGFMoments.excessDegree
  have hm : m.mean ≠ 0 := ne_of_gt m.mean_pos
  have hm' : 0 < m.mean := m.mean_pos
  suffices h : m.mean - 1 ≤ m.secondFactorial / m.mean by
    exact mul_le_mul_of_nonneg_left h hT
  have hv := m.variance_eq
  have hvn := m.variance_nonneg
  have key : (m.mean - 1) * m.mean ≤ m.secondFactorial := by nlinarith
  exact (le_div_iff₀ hm').mpr key

/-- **Result 108c.** Equality iff Var(k) = 0 (regular network). -/
theorem R0_heterogeneity_eq_iff_regular (T : ℝ) (m : PGFMoments)
    (hT : 0 < T) :
    R0_homogeneous T m.mean = R0_heterogeneous T m ↔ m.variance = 0 := by
  unfold R0_homogeneous R0_heterogeneous
  rw [excess_degree_variance_form]
  have hm : m.mean ≠ 0 := ne_of_gt m.mean_pos
  have hT' : T ≠ 0 := ne_of_gt hT
  constructor
  · intro h
    have h1 : m.variance / m.mean = 0 := by nlinarith
    rcases (div_eq_zero_iff.mp h1) with h2 | h2
    · exact h2
    · exact absurd h2 hm
  · intro h
    rw [h, zero_div, add_zero]

/-! ## Result 109: Poisson excess degree = mean

For Poisson(κ), ψ''(1) = κ², so ψ''(1)/ψ'(1) = κ²/κ = κ.
Consequently R₀ = T·κ. -/

/-- Poisson PGF moments over ℝ. -/
def poissonMoments (kappa : ℝ) (hk : 0 < kappa) : PGFMoments where
  mean := kappa
  secondFactorial := kappa ^ 2
  variance := kappa
  mean_pos := hk
  secondFactorial_nonneg := by positivity
  variance_nonneg := le_of_lt hk
  variance_eq := by ring

/-- **Result 109a.** Poisson excess degree equals the mean κ. -/
theorem poisson_excess_eq_mean (kappa : ℝ) (hk : 0 < kappa) :
    (poissonMoments kappa hk).excessDegree = kappa := by
  unfold PGFMoments.excessDegree poissonMoments
  simp
  have hk' : kappa ≠ 0 := ne_of_gt hk
  field_simp

/-- **Result 109b.** R₀ = T·κ for Poisson networks. -/
theorem poisson_R0 (T kappa : ℝ) (hk : 0 < kappa) :
    R0_heterogeneous T (poissonMoments kappa hk) = T * kappa := by
  unfold R0_heterogeneous
  rw [poisson_excess_eq_mean]

/-! ## Result 110: Final size fixed-point equation

The final size of an epidemic on a configuration-model network is determined
by the fixed point θ∞ of:
  θ∞ = 1 - T + T · ψ'(θ∞)/ψ'(1).

The disease-free fixed point θ = 1 is always a solution. For strictly convex
f (some degree ≥ 3 has positive probability) it is the only fixed point in
[0, 1] iff R₀ ≤ 1, where R₀ = f'(1) (not formalised here).

We verify algebraically that θ = 1 satisfies the equation and compute the
derivative of f (`finalSizeMap_hasDerivAt`). The statements `fixed_point_derivative`
and `dfe_stable_iff_R0_le_one` are tautological. -/

/-- The final-size fixed-point function: f(θ) = 1 - T + T · g(θ)
where g(θ) = ψ'(θ)/ψ'(1). At θ=1, g(1) = 1 (normalization). -/
def finalSizeMap (T : ℝ) (g_at_theta : ℝ) : ℝ :=
  1 - T + T * g_at_theta

/-- **Result 110a.** θ = 1 is always a fixed point: f(1) = 1 when g(1) = 1. -/
theorem disease_free_fixed_point (T : ℝ) :
    finalSizeMap T 1 = 1 := by
  unfold finalSizeMap
  ring

/-- **Result 110b.** The derivative f'(θ) = T · g'(θ).
At θ = 1: f'(1) = T · g'(1) = T · ψ''(1)/ψ'(1) = R₀.
Linear stability of θ = 1 needs |f'(1)| < 1, i.e. R₀ < 1; at R₀ = 1 the
linearisation is inconclusive, and θ = 1 is still attracting from below when
f is strictly convex.

**Tautological Lean statement:** `T * excessDeg = T * excessDeg`; the
derivative is computed in `finalSizeMap_hasDerivAt`. -/
theorem fixed_point_derivative (T excessDeg : ℝ) :
    T * excessDeg = T * excessDeg := by ring

/-- **Result 110c.** When R₀ ≤ 1, the disease-free equilibrium θ = 1 is stable:
|f'(1)| ≤ 1 iff T · excessDeg ≤ 1 (since both T and excessDeg are nonneg).
**Tautological Lean statement:** `T * excessDeg ≤ 1 ↔ T * excessDeg ≤ 1`,
proved by `Iff.rfl`; neither |f'(1)| nor stability appears in it. The
absolute-value step is `dfe_derivative_abs_le_one_iff`. -/
theorem dfe_stable_iff_R0_le_one (T excessDeg : ℝ)
    (_hT : 0 ≤ T) (_he : 0 ≤ excessDeg) :
    T * excessDeg ≤ 1 ↔ T * excessDeg ≤ 1 := by
  exact Iff.rfl

/-- The derivative of the final-size map: if `g` has derivative `g'` at `x`,
    then `θ ↦ f(θ) = 1 − T + T·g(θ)` has derivative `T·g'` at `x`. With
    `g = ψ'/ψ'(1)` and `x = 1`, `g'(1) = ψ''(1)/ψ'(1)`, so `f'(1) = R₀`. -/
theorem finalSizeMap_hasDerivAt (T : ℝ) {g : ℝ → ℝ} {g' x : ℝ}
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun θ => finalSizeMap T (g θ)) (T * g') x :=
  (hg.const_mul T).const_add (1 - T)

/-- For `T ≥ 0` and `excessDeg ≥ 0`, `|f'(1)| ≤ 1 ↔ R₀ ≤ 1`, where
    `f'(1) = R₀ = T · excessDeg`. -/
theorem dfe_derivative_abs_le_one_iff (T excessDeg : ℝ)
    (hT : 0 ≤ T) (he : 0 ≤ excessDeg) :
    |T * excessDeg| ≤ 1 ↔ T * excessDeg ≤ 1 := by
  rw [abs_of_nonneg (mul_nonneg hT he)]

/-- **Result 110d.** When T = 0 (no transmission), the fixed point is trivially θ = 1. -/
theorem no_transmission_fixed_point (g_val : ℝ) :
    finalSizeMap 0 g_val = 1 := by
  unfold finalSizeMap
  ring

/-! ## Result 111: CLT for final size (Ball 2021)

For SIR epidemics on configuration-model random graphs with bounded degrees
and an arbitrary infectious-period distribution, the final size Z_n satisfies
√n(Z_n/n − ρ) ⇒ N(0, σ²) with an explicit σ² (so Z_n/n → ρ in probability) in
any of three regimes (Ball 2021): the initially infected fraction converges
to a limit ε ∈ (0, 1) (Theorem 2.1); R₀ > 1, the number of initial infectives
is fixed, and the statement is conditional on a major outbreak, of size at
least log n (Theorem 2.2); or R₀ > 1 and the number of initial infectives
tends to infinity while their fraction tends to zero, without conditioning
(Theorem 2.3). Without the conditioning of Theorem 2.2, Z_n/n does not
converge to ρ > 0 for an epidemic started by a fixed number of infectives,
because a minor outbreak has positive probability.

**Result 111** (not formalised; cited). This library models no random graph,
epidemic process or limit theorem, so the result has no Lean counterpart.
(The former axiom `final_size_CLT`, whose conclusion was `True`, has been
removed together with the unused structure `FinalSizeCLTData`.) -/

/-! ## Result 112: Epidemic threshold universality

R₀ > 1 iff T > ψ'(1)/ψ''(1) (the reciprocal of the excess degree ratio).
This threshold depends only on the first two moments of the degree distribution.

In other words, the critical transmissibility is T_c = 1/excessDegree. -/

/-- The critical transmissibility: T_c = ψ'(1)/ψ''(1) = 1/excessDegree. -/
def criticalTransmissibility (m : PGFMoments) (_hsf : 0 < m.secondFactorial) : ℝ :=
  m.mean / m.secondFactorial

/-- **Result 112a.** T_c = 1 / excessDegree. -/
theorem critical_T_eq_inv_excess (m : PGFMoments) (hsf : 0 < m.secondFactorial) :
    criticalTransmissibility m hsf = 1 / m.excessDegree := by
  unfold criticalTransmissibility PGFMoments.excessDegree
  have hm : m.mean ≠ 0 := ne_of_gt m.mean_pos
  have hsf' : m.secondFactorial ≠ 0 := ne_of_gt hsf
  field_simp

/-- **Result 112b.** R₀ > 1 iff T > T_c: the epidemic threshold.
R₀ = T · excessDeg > 1  ↔  T > 1/excessDeg  (when excessDeg > 0). -/
theorem epidemic_threshold (T : ℝ) (m : PGFMoments)
    (_hT : 0 < T) (hsf : 0 < m.secondFactorial) :
    1 < R0_heterogeneous T m ↔ criticalTransmissibility m hsf < T := by
  unfold R0_heterogeneous criticalTransmissibility PGFMoments.excessDegree
  have hm : 0 < m.mean := m.mean_pos
  rw [show T * (m.secondFactorial / m.mean) = T * m.secondFactorial / m.mean from by ring]
  rw [one_lt_div hm, div_lt_iff₀ hsf]

/-- **Result 112c.** The threshold depends only on first two moments.
T_c = ⟨k⟩/⟨k(k-1)⟩ = ⟨k⟩/(⟨k²⟩ - ⟨k⟩). -/
theorem threshold_moment_form (m : PGFMoments) (hsf : 0 < m.secondFactorial) :
    criticalTransmissibility m hsf =
    m.mean / (m.secondMoment - m.mean) := by
  unfold criticalTransmissibility PGFMoments.secondMoment
  ring

/-- **Result 112d.** For Poisson(κ), T_c = 1/κ. -/
theorem poisson_threshold (kappa : ℝ) (hk : 0 < kappa) :
    criticalTransmissibility (poissonMoments kappa hk)
      (show 0 < (poissonMoments kappa hk).secondFactorial from by
        simp [poissonMoments]; positivity) =
    1 / kappa := by
  unfold criticalTransmissibility poissonMoments
  simp
  have hk' : kappa ≠ 0 := ne_of_gt hk
  field_simp

/-- **Result 112e.** Higher variance lowers the epidemic threshold.
If m₁ and m₂ have the same mean but Var(m₁) ≤ Var(m₂), then
T_c(m₂) ≤ T_c(m₁): more heterogeneous networks have lower thresholds. -/
theorem variance_lowers_threshold (m₁ m₂ : PGFMoments)
    (hsf1 : 0 < m₁.secondFactorial) (hsf2 : 0 < m₂.secondFactorial)
    (hmean : m₁.mean = m₂.mean)
    (hvar : m₁.variance ≤ m₂.variance) :
    criticalTransmissibility m₂ hsf2 ≤ criticalTransmissibility m₁ hsf1 := by
  unfold criticalTransmissibility
  have h1 := m₁.variance_eq
  have h2 := m₂.variance_eq
  rw [div_le_div_iff₀ hsf2 hsf1]
  -- Goal: m₂.mean * m₁.secondFactorial ≤ m₁.mean * m₂.secondFactorial
  rw [hmean]
  -- Goal: m₂.mean * m₁.secondFactorial ≤ m₂.mean * m₂.secondFactorial
  apply mul_le_mul_of_nonneg_left _ (le_of_lt m₂.mean_pos)
  -- Goal: m₁.secondFactorial ≤ m₂.secondFactorial
  -- variance = secondFactorial + mean - mean^2, and means are equal
  -- so secondFactorial = variance - mean + mean^2
  -- Thus sf₁ ≤ sf₂ iff var₁ ≤ var₂
  nlinarith [hmean, m₁.mean_pos, m₂.mean_pos]

end
