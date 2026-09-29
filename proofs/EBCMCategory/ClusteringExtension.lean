import EBCMCategory.EpiCategory
import Mathlib.Tactic

/-!
# Clustering Extension for EBCM

Records scalar quantities of the bivariate PGF framework for networks with
tunable clustering, following Volz et al. (2011) and Miller & Volz (2013). A
clustered network is described by g(x,y) = Σ p_{s,t} x^s y^t where s counts
single-edge stubs and t counts triangles at a node. The PGF g itself is not
formalised: the records below store free rationals.

## References

* Volz EM, Miller JC, Galvani A, Ancel Meyers L (2011). Effects of
  heterogeneous and clustered contact patterns on infectious disease
  dynamics. PLoS Comput Biol 7(6): e1002042.
* Miller JC, Volz EM (2013). Incorporating disease and population structure
  into models of SIR disease in contact networks. PLoS ONE 8(8):e69162.
-/

/-! ## Clustered network data -/

/-- Data for a clustered network with bivariate PGF g(x,y). -/
structure ClusteredPGFData where
  mean_single : ℚ      -- ⟨s⟩ = g_x(1,1)
  mean_triangle : ℚ     -- ⟨t⟩ = g_y(1,1)
  excess_single : ℚ     -- ⟨s(s-1)⟩/⟨s+2t⟩ (excess degree through single edges)
  single_pos : 0 < mean_single
  triangle_nonneg : 0 ≤ mean_triangle

/-! ## Result 69: Clustering coefficient -/

/-- **Result 69.** The triangle stub fraction 2⟨t⟩/(2⟨t⟩+⟨s⟩): the fraction
    of stubs that are triangle stubs (named `clustering_coefficient` for
    compatibility).
    It is not the clustering coefficient, which is C = 2⟨t⟩/⟨k(k−1)⟩ with
    k = s + 2t (the fraction of connected triples that are closed); for
    independent Poisson single and triangle degrees with means κ_s, κ_t,
    C = 2κ_t/((κ_s + 2κ_t)² + 2κ_t). -/
def clustering_coefficient (d : ClusteredPGFData) : ℚ :=
  2 * d.mean_triangle / (2 * d.mean_triangle + d.mean_single)

/-- The triangle stub fraction lies in [0,1]. -/
theorem clustering_in_unit_interval (d : ClusteredPGFData) :
    0 ≤ clustering_coefficient d ∧ clustering_coefficient d ≤ 1 := by
  unfold clustering_coefficient
  have hn : (0 : ℚ) ≤ 2 * d.mean_triangle := by linarith [d.triangle_nonneg]
  have hd : (0 : ℚ) < 2 * d.mean_triangle + d.mean_single := by
    linarith [d.single_pos, d.triangle_nonneg]
  constructor
  · exact div_nonneg hn (le_of_lt hd)
  · rw [div_le_one hd]
    linarith [d.single_pos]

/-! ## Result 70: Zero clustering recovers standard EBCM -/

/-- **Result 70.** Clustering is zero iff there are no triangle edges. -/
theorem zero_clustering_iff_no_triangles (d : ClusteredPGFData) :
    clustering_coefficient d = 0 ↔ d.mean_triangle = 0 := by
  unfold clustering_coefficient
  have hd : (0 : ℚ) < 2 * d.mean_triangle + d.mean_single := by
    linarith [d.single_pos, d.triangle_nonneg]
  constructor
  · intro h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · linarith [d.triangle_nonneg]
    · linarith
  · intro h
    simp [h]

/-! ## Result 71: Triangle transmission probability

Within a triangle, a susceptible node can be infected directly (prob T)
or indirectly via the third node. The total probability of infection through
a triangle pair is 1 - (1-T)(1-T²) = T + T² - T³ (independent edges).
This is not T(2-T) = 1 - (1-T)², the probability that at least one of two
independent edges transmits. -/

/-- **Result 71a.** Pair transmission through a triangle. -/
theorem triangle_pair_transmission (T : ℚ) :
    1 - (1 - T) * (1 - T ^ 2) = T + T ^ 2 - T ^ 3 := by ring

/-- **Result 71b.** The ring identity T(2 − T) = 2T − T².
    It is not the per-partner transmissibility in a triangle, which is
    T + T² − T³ (Result 71a); at T = 1/2 the two are 3/4 and 5/8. -/
theorem triangle_per_partner (T : ℚ) :
    T * (2 - T) = 2 * T - T ^ 2 := by ring

/-! ## Result 72: R₀ for clustered networks -/

/-- Data for R₀ computation in a clustered network. -/
structure ClusteredR0Data extends ClusteredPGFData where
  T : ℚ                -- edge transmissibility
  T_pos : 0 < T
  T_le_one : T ≤ 1

/-- **Result 72.** The scalar `clustered_R0` =
  T·(⟨s(s-1)⟩/⟨s+2t⟩) + T·(2⟨t⟩/⟨s+2t⟩)·(1+T), kept for compatibility.
  It is not the R₀ of a clustered network: its triangle term does not scale
  with the excess triangle degree. For triangle-clustered configuration
  models, R₀ is the spectral radius of the next-generation matrix over
  single-edge and triangle-edge infection types (Miller 2009); it is not
  formalised here. -/
def clustered_R0 (d : ClusteredR0Data) : ℚ :=
  d.T * d.excess_single +
  d.T * (2 * d.mean_triangle / (d.mean_single + 2 * d.mean_triangle)) * (1 + d.T)

/-! ## Result 73: Clustering reduces R₀ (algebraic form)

Converting a triangle (⟨t⟩→⟨t⟩-1) to two single edges (⟨s⟩→⟨s⟩+2) preserves
mean degree ⟨k⟩ = ⟨s⟩+2⟨t⟩. In the scalar formula `clustered_R0`, a
triangle's two stubs contribute T·(1+T) in total, i.e. T(1+T)/2 per stub,
which is at most the contribution T of a single-edge stub. This is a
statement about that formula, not a derivation of R₀ for clustered networks.

The key inequality: for 0 < T ≤ 1, T(1+T)/2 ≤ T, since
T(1+T)/2 ≤ T ↔ (1+T)/2 ≤ 1 ↔ T ≤ 1. The per-stub value T(1+T)/2 comes from
`clustered_R0` and is not sourced. -/

/-- **Result 73.** Triangle edges contribute less per edge than single edges to R₀. -/
theorem triangle_per_edge_le_single (T : ℚ) (hT : 0 < T) (hT1 : T ≤ 1) :
    T * (1 + T) / 2 ≤ T := by
  have h1 : T * (1 + T) / 2 - T = -(T * (1 - T) / 2) := by ring
  have h2 : 0 ≤ T * (1 - T) / 2 :=
    div_nonneg (mul_nonneg (le_of_lt hT) (sub_nonneg.mpr hT1)) (by norm_num)
  linarith

/-! ## Result 74: Mean total degree -/

/-- **Result 74.** Mean total degree ⟨k⟩ = ⟨s⟩ + 2⟨t⟩. -/
def mean_total_degree (d : ClusteredPGFData) : ℚ :=
  d.mean_single + 2 * d.mean_triangle

/-- Mean total degree is positive. -/
theorem mean_degree_positive (d : ClusteredPGFData) :
    0 < mean_total_degree d := by
  unfold mean_total_degree
  linarith [d.single_pos, d.triangle_nonneg]

/-! ## Result 75: Poisson clustered network

For independent Poisson single/triangle edges with means κ_s, κ_t:
g(x,y) = exp(κ_s(x-1) + κ_t(y-1)).
The triangle stub fraction equals 2κ_t/(2κ_t + κ_s); the clustering
coefficient is 2⟨t⟩/⟨k(k−1)⟩ = 2κ_t/((κ_s + 2κ_t)² + 2κ_t). -/

/-- **Result 75.** A Poisson clustered network has triangle stub fraction
    2κ_t/(2κ_t+κ_s). Its clustering coefficient is
    2κ_t/((κ_s + 2κ_t)² + 2κ_t). -/
theorem poisson_clustering (kappa_s kappa_t : ℚ) (hs : 0 < kappa_s) (ht : 0 ≤ kappa_t) :
    2 * kappa_t / (2 * kappa_t + kappa_s) =
    clustering_coefficient ⟨kappa_s, kappa_t, kappa_s, hs, ht⟩ := by
  simp [clustering_coefficient]

/-! ## Result 76: Degree conversion preserves mean

Replacing 1 triangle with 2 single edges: ⟨s'⟩ = ⟨s⟩+2, ⟨t'⟩ = ⟨t⟩-1
preserves mean total degree. -/

/-- **Result 76.** Triangle-to-single conversion preserves mean degree. -/
theorem degree_conversion_preserves_mean (s t : ℚ) :
    (s + 2) + 2 * (t - 1) = s + 2 * t := by ring
