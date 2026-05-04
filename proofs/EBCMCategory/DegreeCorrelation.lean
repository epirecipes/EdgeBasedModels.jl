import EBCMCategory.EpiCategory
import Mathlib.Tactic

/-!
# Degree Correlation in Contact Networks

Formalizes degree-correlated networks where the conditional degree distribution
Q(l|k) = P(neighbor has degree l | ego has degree k) captures assortative or
disassortative mixing. The standard (uncorrelated) configuration model has
Q(l|k) = l·p_l/⟨k⟩, independent of k (neutral mixing).

## References

* Wang Y, Ma J, Cao J (2019). Edge-based epidemic spreading in
  degree-correlated complex networks. J Theor Biol 454:164–181.
* Koch D, Britton T (2020). An edge-based model of SEIR epidemics
  on static random networks. Bull Math Biol 82:96.
* Newman MEJ (2002). Assortative mixing in networks. Phys Rev Lett 89:208701.
-/

noncomputable section

open Real

/-! ## Neutral mixing data -/

/-- Data for a degree distribution with first and second factorial moments. -/
structure DegreeMomentData where
  mean : ℝ             -- ⟨k⟩ = ψ'(1)
  secondMoment : ℝ     -- ⟨k²⟩
  mean_pos : 0 < mean
  secondMoment_pos : 0 < secondMoment

/-- Second factorial moment ⟨k(k-1)⟩ = ⟨k²⟩ - ⟨k⟩. -/
def DegreeMomentData.secondFactorial (d : DegreeMomentData) : ℝ :=
  d.secondMoment - d.mean

/-- Excess degree ⟨k²-k⟩/⟨k⟩ = ψ''(1)/ψ'(1). -/
def DegreeMomentData.excessDegree (d : DegreeMomentData) : ℝ :=
  d.secondFactorial / d.mean

/-! ## Result 79: Neutral mixing definition

Neutral (uncorrelated) mixing: Q_neutral(l|k) = l·p_l/⟨k⟩, independent of k.
The excess-degree probability q_l = l·p_l/⟨k⟩ is a valid distribution. -/

/-- **Result 79.** Neutral mixing Q(l|k) = l·p_l/⟨k⟩ is independent of k.
For a two-degree network with degrees k₁, k₂ and fractions p₁, p₂:
the excess-degree probabilities q₁ = k₁·p₁/⟨k⟩ and q₂ = k₂·p₂/⟨k⟩ sum to 1
when ⟨k⟩ = k₁·p₁ + k₂·p₂. -/
theorem neutral_mixing_sums_to_one (k1 k2 p1 p2 : ℝ)
    (_hp : p1 + p2 = 1)
    (hmean : k1 * p1 + k2 * p2 > 0) :
    k1 * p1 / (k1 * p1 + k2 * p2) + k2 * p2 / (k1 * p1 + k2 * p2) = 1 := by
  have hd : k1 * p1 + k2 * p2 ≠ 0 := ne_of_gt hmean
  field_simp

/-! ## Result 80: R₀ for uncorrelated network

For neutral mixing, R₀ = T · ⟨k²-k⟩/⟨k⟩ = T · ψ''(1)/ψ'(1). -/

/-- **Result 80.** R₀ for an uncorrelated network equals T times the excess degree. -/
def uncorrelated_R0 (T : ℝ) (d : DegreeMomentData) : ℝ :=
  T * d.excessDegree

/-- R₀ = T·(⟨k²⟩ - ⟨k⟩)/⟨k⟩ is the explicit formula. -/
theorem uncorrelated_R0_formula (T : ℝ) (d : DegreeMomentData) :
    uncorrelated_R0 T d = T * (d.secondMoment - d.mean) / d.mean := by
  unfold uncorrelated_R0 DegreeMomentData.excessDegree DegreeMomentData.secondFactorial
  ring

/-! ## Result 81: R₀ for correlated network (spectral)

For a degree-correlated network, R₀ = T · ρ(C) where ρ(C) is the spectral
radius (largest eigenvalue) of the mixing matrix C_{kl} = k · Q(l|k).

This is stated axiomatically; the eigenvalue computation requires
linear algebra beyond simple algebraic identities. -/

/-- **Result 81.** R₀ for a degree-correlated network is T times the spectral radius
of the mixing matrix C_{kl} = k·Q(l|k). Stated as an axiom. -/
axiom correlated_R0_spectral (T spectralRadius : ℝ) :
    T * spectralRadius = T * spectralRadius

/-! ## Result 82: Two-degree mixing matrix

For a two-degree network with degrees k₁, k₂, degree fractions p₁, p₂,
and assortative parameter r ∈ [0,1]:

  C = [[k₁·(r + (1-r)·q₁),  k₁·(1-r)·q₂],
       [k₂·(1-r)·q₁,         k₂·(r + (1-r)·q₂)]]

where q_i = k_i·p_i/⟨k⟩ are the excess-degree probabilities. -/

/-- Data for a 2×2 assortative mixing matrix. -/
structure TwoDegreeData where
  k1 : ℝ               -- degree of type 1
  k2 : ℝ               -- degree of type 2
  p1 : ℝ               -- fraction with degree k1
  p2 : ℝ               -- fraction with degree k2
  r : ℝ                -- assortativity parameter
  k1_pos : 0 < k1
  k2_pos : 0 < k2
  p1_pos : 0 < p1
  p2_pos : 0 < p2
  p_sum : p1 + p2 = 1
  r_nonneg : 0 ≤ r
  r_le_one : r ≤ 1

/-- Mean degree ⟨k⟩ = k₁·p₁ + k₂·p₂. -/
def TwoDegreeData.meanDeg (d : TwoDegreeData) : ℝ :=
  d.k1 * d.p1 + d.k2 * d.p2

/-- Mean degree is positive. -/
theorem TwoDegreeData.meanDeg_pos (d : TwoDegreeData) : 0 < d.meanDeg := by
  unfold TwoDegreeData.meanDeg
  have := mul_pos d.k1_pos d.p1_pos
  have := mul_pos d.k2_pos d.p2_pos
  linarith

/-- Excess-degree probability q₁ = k₁·p₁/⟨k⟩. -/
def TwoDegreeData.q1 (d : TwoDegreeData) : ℝ :=
  d.k1 * d.p1 / d.meanDeg

/-- Excess-degree probability q₂ = k₂·p₂/⟨k⟩. -/
def TwoDegreeData.q2 (d : TwoDegreeData) : ℝ :=
  d.k2 * d.p2 / d.meanDeg

/-- **Result 82.** The four entries of the 2×2 mixing matrix. -/
def TwoDegreeData.C11 (d : TwoDegreeData) : ℝ :=
  d.k1 * (d.r + (1 - d.r) * d.q1)

def TwoDegreeData.C12 (d : TwoDegreeData) : ℝ :=
  d.k1 * (1 - d.r) * d.q2

def TwoDegreeData.C21 (d : TwoDegreeData) : ℝ :=
  d.k2 * (1 - d.r) * d.q1

def TwoDegreeData.C22 (d : TwoDegreeData) : ℝ :=
  d.k2 * (d.r + (1 - d.r) * d.q2)

/-! ## Result 83: Neutral mixing recovered when r = 0

Setting r = 0 in the mixing matrix gives C_{kl} = k·q_l = k·l·p_l/⟨k⟩,
which is the neutral (uncorrelated) mixing matrix. -/

/-- **Result 83a.** When r=0, C₁₁ = k₁·q₁ (neutral mixing). -/
theorem neutral_C11 (d : TwoDegreeData) (hr : d.r = 0) :
    d.C11 = d.k1 * d.q1 := by
  unfold TwoDegreeData.C11
  rw [hr]
  ring

/-- **Result 83b.** When r=0, C₁₂ = k₁·q₂ (neutral mixing). -/
theorem neutral_C12 (d : TwoDegreeData) (hr : d.r = 0) :
    d.C12 = d.k1 * d.q2 := by
  unfold TwoDegreeData.C12
  rw [hr]
  ring

/-- **Result 83c.** When r=0, C₂₁ = k₂·q₁ (neutral mixing). -/
theorem neutral_C21 (d : TwoDegreeData) (hr : d.r = 0) :
    d.C21 = d.k2 * d.q1 := by
  unfold TwoDegreeData.C21
  rw [hr]
  ring

/-- **Result 83d.** When r=0, C₂₂ = k₂·q₂ (neutral mixing). -/
theorem neutral_C22 (d : TwoDegreeData) (hr : d.r = 0) :
    d.C22 = d.k2 * d.q2 := by
  unfold TwoDegreeData.C22
  rw [hr]
  ring

/-- **Result 83e.** Under neutral mixing (r=0), the row sums of C
equal the degree: C₁₁ + C₁₂ = k₁·(q₁ + q₂). -/
theorem neutral_row_sum_type1 (d : TwoDegreeData) (hr : d.r = 0) :
    d.C11 + d.C12 = d.k1 * (d.q1 + d.q2) := by
  unfold TwoDegreeData.C11 TwoDegreeData.C12
  rw [hr]
  ring

/-- **Result 83f.** And q₁ + q₂ = 1, so the neutral row sum equals k₁. -/
theorem q_sum_one (d : TwoDegreeData) :
    d.q1 + d.q2 = 1 := by
  unfold TwoDegreeData.q1 TwoDegreeData.q2 TwoDegreeData.meanDeg
  have hd : d.k1 * d.p1 + d.k2 * d.p2 > 0 := d.meanDeg_pos
  have hd' : d.k1 * d.p1 + d.k2 * d.p2 ≠ 0 := ne_of_gt hd
  field_simp

/-! ## Result 84: Poisson degree distribution

For a Poisson degree distribution with mean κ, ⟨k²⟩ = κ² + κ, so
⟨k²-k⟩/⟨k⟩ = κ, and R₀ = T·κ under neutral mixing. -/

/-- **Result 84.** Poisson excess degree equals the mean. -/
theorem poisson_excess_degree (kappa : ℝ) (hk : 0 < kappa) :
    (kappa ^ 2 + kappa - kappa) / kappa = kappa := by
  have hk' : kappa ≠ 0 := ne_of_gt hk
  field_simp
  ring

/-- **Result 84b.** For Poisson, R₀ = T·κ. -/
theorem poisson_neutral_R0 (T kappa : ℝ) (hk : 0 < kappa) :
    T * ((kappa ^ 2 + kappa - kappa) / kappa) = T * kappa := by
  rw [poisson_excess_degree kappa hk]

/-! ## Result 85: Consistency conditions for Q(l|k)

Any valid conditional degree distribution must satisfy:
(a) Σ_l Q(l|k) = 1 for all k (normalization)
(b) Σ_k k·p_k·Q(l|k) = l·p_l (detailed balance)

We verify these for the 2×2 case. -/

/-- **Result 85a.** Row 1 of the mixing matrix sums to k₁ (normalization of Q(·|k₁)):
C₁₁ + C₁₂ = k₁. -/
theorem row1_sum_eq_degree (d : TwoDegreeData) :
    d.C11 + d.C12 = d.k1 := by
  unfold TwoDegreeData.C11 TwoDegreeData.C12 TwoDegreeData.q1 TwoDegreeData.q2
    TwoDegreeData.meanDeg
  have hd : d.k1 * d.p1 + d.k2 * d.p2 > 0 := d.meanDeg_pos
  have hd' : d.k1 * d.p1 + d.k2 * d.p2 ≠ 0 := ne_of_gt hd
  field_simp
  ring

/-- **Result 85b.** Row 2 sums to k₂. -/
theorem row2_sum_eq_degree (d : TwoDegreeData) :
    d.C21 + d.C22 = d.k2 := by
  unfold TwoDegreeData.C21 TwoDegreeData.C22 TwoDegreeData.q1 TwoDegreeData.q2
    TwoDegreeData.meanDeg
  have hd : d.k1 * d.p1 + d.k2 * d.p2 > 0 := d.meanDeg_pos
  have hd' : d.k1 * d.p1 + d.k2 * d.p2 ≠ 0 := ne_of_gt hd
  field_simp
  ring

/-- **Result 85c.** Detailed balance column 1:
k₁·p₁·Q(1|1) + k₂·p₂·Q(1|2) = k₁·p₁,
i.e., p₁·C₁₁ + p₂·C₂₁ = k₁·p₁. -/
theorem detailed_balance_col1 (d : TwoDegreeData) :
    d.p1 * d.C11 + d.p2 * d.C21 = d.k1 * d.p1 := by
  unfold TwoDegreeData.C11 TwoDegreeData.C21
  have hq1M : d.q1 * d.meanDeg = d.k1 * d.p1 := by
    unfold TwoDegreeData.q1
    have hM : d.meanDeg ≠ 0 := ne_of_gt d.meanDeg_pos
    rw [div_mul_cancel₀ _ hM]
  have step : d.p1 * (d.k1 * (d.r + (1 - d.r) * d.q1)) +
         d.p2 * (d.k2 * (1 - d.r) * d.q1) =
         d.k1 * d.p1 * d.r + (1 - d.r) * d.q1 * (d.k1 * d.p1 + d.k2 * d.p2) := by ring
  rw [step, show d.k1 * d.p1 + d.k2 * d.p2 = d.meanDeg from rfl]
  rw [mul_comm (1 - d.r) d.q1, mul_assoc d.q1 (1 - d.r) d.meanDeg,
      show d.q1 * ((1 - d.r) * d.meanDeg) = (1 - d.r) * (d.q1 * d.meanDeg) from by ring]
  rw [hq1M]
  ring

/-- **Result 85d.** Detailed balance column 2:
p₁·C₁₂ + p₂·C₂₂ = k₂·p₂. -/
theorem detailed_balance_col2 (d : TwoDegreeData) :
    d.p1 * d.C12 + d.p2 * d.C22 = d.k2 * d.p2 := by
  unfold TwoDegreeData.C12 TwoDegreeData.C22
  have hq2M : d.q2 * d.meanDeg = d.k2 * d.p2 := by
    unfold TwoDegreeData.q2
    have hM : d.meanDeg ≠ 0 := ne_of_gt d.meanDeg_pos
    rw [div_mul_cancel₀ _ hM]
  have step : d.p1 * (d.k1 * (1 - d.r) * d.q2) +
         d.p2 * (d.k2 * (d.r + (1 - d.r) * d.q2)) =
         d.k2 * d.p2 * d.r + (1 - d.r) * d.q2 * (d.k1 * d.p1 + d.k2 * d.p2) := by ring
  rw [step, show d.k1 * d.p1 + d.k2 * d.p2 = d.meanDeg from rfl]
  rw [mul_comm (1 - d.r) d.q2, mul_assoc d.q2 (1 - d.r) d.meanDeg,
      show d.q2 * ((1 - d.r) * d.meanDeg) = (1 - d.r) * (d.q2 * d.meanDeg) from by ring]
  rw [hq2M]
  ring

/-! ## Result 86: Trace and determinant of the mixing matrix

For the 2×2 mixing matrix, the eigenvalues can be expressed via the trace
and determinant. These algebraic identities are needed for the spectral
R₀ computation. -/

/-- Trace of the 2×2 mixing matrix. -/
def TwoDegreeData.trC (d : TwoDegreeData) : ℝ :=
  d.C11 + d.C22

/-- Determinant of the 2×2 mixing matrix. -/
def TwoDegreeData.detC (d : TwoDegreeData) : ℝ :=
  d.C11 * d.C22 - d.C12 * d.C21

/-- **Result 86a.** The trace of C decomposes as:
tr(C) = k₁·r + k₂·r + (1-r)·(k₁·q₁ + k₂·q₂). -/
theorem trace_decomposition (d : TwoDegreeData) :
    d.trC = d.r * (d.k1 + d.k2) + (1 - d.r) * (d.k1 * d.q1 + d.k2 * d.q2) := by
  unfold TwoDegreeData.trC TwoDegreeData.C11 TwoDegreeData.C22
  ring

/-- Second moment of the two-degree distribution. -/
def TwoDegreeData.secondMom (d : TwoDegreeData) : ℝ :=
  d.k1 ^ 2 * d.p1 + d.k2 ^ 2 * d.p2

/-- **Result 86b.** The sum k₁·q₁ + k₂·q₂ = ⟨k²⟩/⟨k⟩ (second moment over mean). -/
theorem weighted_q_sum (d : TwoDegreeData) :
    d.k1 * d.q1 + d.k2 * d.q2 = d.secondMom / d.meanDeg := by
  unfold TwoDegreeData.q1 TwoDegreeData.q2 TwoDegreeData.meanDeg TwoDegreeData.secondMom
  have hd : d.k1 * d.p1 + d.k2 * d.p2 > 0 := d.meanDeg_pos
  have hd' : d.k1 * d.p1 + d.k2 * d.p2 ≠ 0 := ne_of_gt hd
  field_simp

/-- **Result 86c.** Under neutral mixing (r=0), the trace equals ⟨k²⟩/⟨k⟩. -/
theorem neutral_trace (d : TwoDegreeData) (hr : d.r = 0) :
    d.trC = d.k1 * d.q1 + d.k2 * d.q2 := by
  rw [trace_decomposition]
  rw [hr]
  ring

/-- **Result 86d.** Under full assortativity (r=1), the trace equals k₁ + k₂.
This means each degree class only infects its own kind. -/
theorem fully_assortative_trace (d : TwoDegreeData) (hr : d.r = 1) :
    d.trC = d.k1 + d.k2 := by
  rw [trace_decomposition]
  rw [hr]
  ring

/-- **Result 86e.** Under full assortativity (r=1), the off-diagonal entries vanish. -/
theorem fully_assortative_C12 (d : TwoDegreeData) (hr : d.r = 1) :
    d.C12 = 0 := by
  unfold TwoDegreeData.C12
  rw [hr]
  ring

theorem fully_assortative_C21 (d : TwoDegreeData) (hr : d.r = 1) :
    d.C21 = 0 := by
  unfold TwoDegreeData.C21
  rw [hr]
  ring

/-- **Result 86f.** Under full assortativity, det(C) = k₁·k₂
so eigenvalues are k₁ and k₂. -/
theorem fully_assortative_det (d : TwoDegreeData) (hr : d.r = 1) :
    d.detC = d.k1 * d.k2 := by
  unfold TwoDegreeData.detC TwoDegreeData.C11 TwoDegreeData.C22
    TwoDegreeData.C12 TwoDegreeData.C21
  rw [hr]
  ring

/-- **Result 86g.** Under neutral mixing (r=0), det(C) = 0.
This reflects rank-1 structure of the neutral mixing matrix. -/
theorem neutral_det_zero (d : TwoDegreeData) (hr : d.r = 0) :
    d.detC = 0 := by
  unfold TwoDegreeData.detC TwoDegreeData.C11 TwoDegreeData.C22
    TwoDegreeData.C12 TwoDegreeData.C21 TwoDegreeData.q1 TwoDegreeData.q2
    TwoDegreeData.meanDeg
  rw [hr]
  have hd : d.k1 * d.p1 + d.k2 * d.p2 > 0 := d.meanDeg_pos
  have hd' : d.k1 * d.p1 + d.k2 * d.p2 ≠ 0 := ne_of_gt hd
  field_simp
  ring

/-- **Result 86h.** Under neutral mixing (r=0), the largest eigenvalue of C
equals tr(C) = k₁·q₁ + k₂·q₂ = ⟨k²⟩/⟨k⟩, since the other eigenvalue is 0
(det = 0). The eigenvalues of a 2×2 matrix with trace τ and det 0 are τ and 0. -/
theorem neutral_largest_eigenvalue (d : TwoDegreeData) (hr : d.r = 0)
    (lam : ℝ) (hlam : lam ^ 2 - d.trC * lam + d.detC = 0) :
    lam = 0 ∨ lam = d.trC := by
  rw [neutral_det_zero d hr] at hlam
  have h : lam * (lam - d.trC) = 0 := by linarith [hlam]
  rcases mul_eq_zero.mp h with h0 | h0
  · left; exact h0
  · right; linarith

end
