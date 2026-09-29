import EBCMCategory.EpiCategory
import Mathlib.Tactic

/-!
# Categorical Composition of EBCM Models

States scalar identities motivated by categorical constructions on
edge-based compartmental models: products (multiplex networks), coproducts
(stratified populations), natural transformations (adding stages, adding
clustering), monoidal structure and functoriality. No categorical structure
is formalised: no category, functor, natural transformation or monoidal
product is defined, and the identities below are about real and natural
numbers attached to layer records.

## References

* Miller JC, Slim AC, Volz EM (2012). Edge-based compartmental modelling
  for infectious disease spread. J. R. Soc. Interface 9, 890–906.
* Allard A, Hébert-Dufresne L, Young J-G, Dubé LJ (2015). General and
  exact approach to percolation on random graphs. Phys Rev E 92:062807.
* Sherborne N, Miller JC, Blyuss KB, Kiss IZ (2018). Mean-field models
  for non-Markovian epidemics on networks. J. Math. Biol. 76, 755–778.
-/

noncomputable section

open Real

/-! ## EBCM layer data

A single EBCM layer is specified by a PGF (degree distribution) and SIR-like
disease parameters. The ODE system it maps to has a dimension and basic
reproduction number R₀. -/

/-- An EBCM layer: a (Graph, Disease) pair with its derived quantities. -/
structure EBCMLayer where
  mean : ℝ               -- ψ'(1) = ⟨k⟩
  secondFactorial : ℝ    -- ψ''(1) = ⟨k(k-1)⟩
  T : ℝ                  -- edge transmissibility
  dim : ℕ                -- ODE dimension
  mean_pos : 0 < mean
  sf_nonneg : 0 ≤ secondFactorial
  T_pos : 0 < T
  T_le_one : T ≤ 1

/-- Excess degree for a layer: ψ''(1)/ψ'(1). -/
def EBCMLayer.excessDegree (l : EBCMLayer) : ℝ :=
  l.secondFactorial / l.mean

/-- R₀ for a single EBCM layer. -/
def EBCMLayer.R0 (l : EBCMLayer) : ℝ :=
  l.T * l.excessDegree

/-! ## Result 95: EBCM as a functor

The EBCM construction maps each (degree distribution, disease progression)
pair to an ODE system. It would be a functor F: Graph × Disease → ODE once
categories of such pairs and of ODE systems are defined; neither is defined here.

Functoriality means: F preserves identity and composition of morphisms.
We record the layer data and verify the R₀ formula. The
categorical coherence (identity/composition laws) is not formalised: this
library defines no category of (graph, disease) pairs and no category of
ODE systems. -/

/-- **Result 95a.** The EBCM construction maps (PGF, SIR params) to an ODE system (not formalised).
We verify that R₀ = T · ψ''(1)/ψ'(1) for the resulting system. -/
theorem ebcm_functor_R0 (l : EBCMLayer) :
    l.R0 = l.T * (l.secondFactorial / l.mean) := by
  unfold EBCMLayer.R0 EBCMLayer.excessDegree
  ring

/-! **Result 95b** (not formalised). Functoriality: the EBCM functor preserves
the identity morphism—the identity graph homomorphism and identity disease map
yield the same ODE system. No category, morphism or ODE system is defined in
this library, so the statement has no Lean counterpart. (The former axiom
`ebcm_functor_identity`, which stated `l.R0 = l.R0`, was content-free and has
been removed.) -/

/-! **Result 95c** (not formalised). Functoriality: F preserves composition. If
φ: G₁ → G₂ and ψ: D₁ → D₂ are morphisms, then F(ψ∘φ) = F(ψ)∘F(φ). The
statement has no Lean counterpart. (The former axiom
`ebcm_functor_composition`, which stated transitivity of `≤` on layer R₀
values, was unrelated to this statement and has been removed.) -/

/-! ## Result 96: Product of independent layers (multiplex)

For independent multiplex layers (G₁,D₁) and (G₂,D₂), the joint susceptible
fraction is the product: S(t) = ψ₁(θ₁(t)) · ψ₂(θ₂(t)).

The product ODE dimension is the sum of individual dimensions. -/

/-- Data for a multiplex product of two EBCM layers. -/
structure MultiplexProduct where
  layer1 : EBCMLayer
  layer2 : EBCMLayer

/-- **Result 96a.** Product susceptible fraction: S = S₁ · S₂.
For layer susceptible fractions S₁ ∈ (0,1] and S₂ ∈ (0,1],
the product S₁·S₂ ∈ (0,1]. -/
theorem product_susceptible_pos (S1 S2 : ℝ)
    (h1 : 0 < S1) (h2 : 0 < S2)
    (h1' : S1 ≤ 1) (h2' : S2 ≤ 1) :
    0 < S1 * S2 ∧ S1 * S2 ≤ 1 := by
  constructor
  · exact mul_pos h1 h2
  · exact mul_le_one₀ h1' (le_of_lt h2) h2'

/-- **Result 96b.** The product dimension is defined as the sum of the layer
    dimensions; the compact multiplex system needs fewer ODEs (one θ-equation
    per layer plus one recovery equation, `compactMultiplexDim`). -/
def MultiplexProduct.dim (p : MultiplexProduct) : ℕ :=
  p.layer1.dim + p.layer2.dim

/-- **Result 96c.** The sum T₁e₁ + T₂e₂ of the per-layer R₀ values; it
matches the former compact implementation in `src/multiplex.jl`.
It is not the R₀ of independent multiplex layers, which is ρ(K) with
K = [[T₁e₁, T₁⟨k₁⟩], [T₂⟨k₂⟩, T₂e₂]] and eᵢ = ψᵢ''(1)/ψᵢ'(1) (`MultiplexProduct.K11` …).
The sum T₁e₁ + T₂e₂ equals ρ(K) iff det K = 0, i.e. e₁e₂ = ⟨k₁⟩⟨k₂⟩, for
example for two Poisson layers; it underestimates ρ(K) when
e₁e₂ < ⟨k₁⟩⟨k₂⟩. Two 3-regular layers with T = 6/25 give sum 24/25 but
ρ(K) = 6/5 (`multiplex_R0_sum_ne_spectral`). -/
def MultiplexProduct.R0_sum (p : MultiplexProduct) : ℝ :=
  p.layer1.R0 + p.layer2.R0

/-- The compact two-layer multiplex implementation has one θ-equation per layer
plus one shared recovery equation. -/
def compactMultiplexDim (nLayers : ℕ) : ℕ :=
  nLayers + 1

/-- **Result 96d.** A two-layer compact multiplex system has 3 ODEs. -/
theorem compact_multiplex_dim_two :
    compactMultiplexDim 2 = 3 := by
  rfl

/-- **Result 96e.** A three-layer compact multiplex system has 4 ODEs. -/
theorem compact_multiplex_dim_three :
    compactMultiplexDim 3 = 4 := by
  rfl

/-- **Result 96f.** If the summed multiplex contribution is at most one, the
sum is at most one. **Tautological Lean statement:** its hypothesis is its
conclusion. The multiplex product itself need not be subcritical: for two
3-regular layers with T = 6/25 the sum is 24/25 but R₀ = ρ(K) = 6/5
(`multiplex_R0_sum_ne_spectral`). -/
theorem product_subcritical (p : MultiplexProduct)
    (hsum : p.R0_sum ≤ 1) :
    p.R0_sum ≤ 1 := by
  exact hsum

/-- **Result 96g.** If the first layer is supercritical, then the additive
multiplex threshold is also supercritical.
This concerns the additive quantity `R0_sum`. The multiplex R₀ ρ(K) is also
greater than 1 in this case, because ρ(K) ≥ K₁₁ = T₁e₁ for the nonnegative
matrix K. -/
theorem product_supercritical_left (p : MultiplexProduct)
    (h1 : 1 < p.layer1.R0) :
    1 < p.R0_sum := by
  have h2_nonneg : 0 ≤ p.layer2.R0 := by
    unfold EBCMLayer.R0 EBCMLayer.excessDegree
    have hmean : 0 ≤ p.layer2.mean := le_of_lt p.layer2.mean_pos
    have hexcess : 0 ≤ p.layer2.secondFactorial / p.layer2.mean := by
      exact div_nonneg p.layer2.sf_nonneg hmean
    exact mul_nonneg (le_of_lt p.layer2.T_pos) hexcess
  unfold MultiplexProduct.R0_sum
  linarith

/-! ### Multiplex next-generation matrix (corrects Results 96c and 96f) -/

/-- Entry (1,1) of the multiplex next-generation matrix: T₁e₁. -/
def MultiplexProduct.K11 (p : MultiplexProduct) : ℝ := p.layer1.T * p.layer1.excessDegree

/-- Entry (1,2) of the multiplex next-generation matrix: T₁⟨k₁⟩ (layer-1
    infections caused by a node infected through layer 2). -/
def MultiplexProduct.K12 (p : MultiplexProduct) : ℝ := p.layer1.T * p.layer1.mean

/-- Entry (2,1) of the multiplex next-generation matrix: T₂⟨k₂⟩. -/
def MultiplexProduct.K21 (p : MultiplexProduct) : ℝ := p.layer2.T * p.layer2.mean

/-- Entry (2,2) of the multiplex next-generation matrix: T₂e₂. -/
def MultiplexProduct.K22 (p : MultiplexProduct) : ℝ := p.layer2.T * p.layer2.excessDegree

/-- The additive rule `R0_sum` is the trace of the multiplex next-generation
    matrix K. -/
theorem MultiplexProduct.R0_sum_eq_trace (p : MultiplexProduct) :
    p.R0_sum = p.K11 + p.K22 := rfl

/-- A 3-regular layer (⟨k⟩ = 3, ψ''(1) = 6, excess degree 2) with T = 6/25. -/
def threeRegularLayer : EBCMLayer where
  mean := 3
  secondFactorial := 6
  T := 6 / 25
  dim := 2
  mean_pos := by norm_num
  sf_nonneg := by norm_num
  T_pos := by norm_num
  T_le_one := by norm_num

/-- **The additive multiplex R₀ is not the spectral radius.** For two 3-regular
    layers with T = 6/25, K = [[12/25, 18/25], [18/25, 12/25]] has the
    eigenvectors (1, 1) with eigenvalue 6/5 and (1, −1) with eigenvalue
    −6/25, so ρ(K) = 6/5 > 1, while `R0_sum` = 24/25 < 1. -/
theorem multiplex_R0_sum_ne_spectral :
    ∃ p : MultiplexProduct,
      p.K11 + p.K12 = 6 / 5 ∧ p.K21 + p.K22 = 6 / 5 ∧
      p.K11 - p.K12 = -6 / 25 ∧ p.K21 - p.K22 = 6 / 25 ∧
      p.R0_sum = 24 / 25 := by
  refine ⟨⟨threeRegularLayer, threeRegularLayer⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [MultiplexProduct.K11, MultiplexProduct.K12, MultiplexProduct.K21,
        MultiplexProduct.K22, MultiplexProduct.R0_sum, EBCMLayer.R0,
        EBCMLayer.excessDegree, threeRegularLayer]
      norm_num

/-! ## Result 97: Stratification as a coproduct

For K types with degree distributions and a K×K mixing matrix M,
the multi-type EBCM couples K single-type EBCMs through M. It is not a
coproduct: with mixing, the types interact, so the joint system is not a
disjoint union of the single-type systems.

We formalize the 2-type case explicitly. -/

/-- Data for a 2-type stratified model with mixing matrix. -/
structure StratifiedData where
  layer1 : EBCMLayer     -- type 1 EBCM
  layer2 : EBCMLayer     -- type 2 EBCM
  p1 : ℝ                 -- proportion of type 1
  p2 : ℝ                 -- proportion of type 2
  m11 : ℝ                -- mixing M₁₁
  m12 : ℝ                -- mixing M₁₂
  m21 : ℝ                -- mixing M₂₁
  m22 : ℝ                -- mixing M₂₂
  p1_pos : 0 < p1
  p2_pos : 0 < p2
  p_sum : p1 + p2 = 1
  m_nonneg : 0 ≤ m11 ∧ 0 ≤ m12 ∧ 0 ≤ m21 ∧ 0 ≤ m22

/-- **Result 97a.** Overall susceptible fraction is the population-weighted sum:
S(t) = p₁·S₁(t) + p₂·S₂(t). It is a convex combination of the type
susceptible fractions, not a coproduct injection. -/
def StratifiedData.S_total (S1 S2 : ℝ) (d : StratifiedData) : ℝ :=
  d.p1 * S1 + d.p2 * S2

/-- **Result 97b.** The coproduct susceptible fraction at t=0 is 1
(everyone starts susceptible). -/
theorem stratified_S_initial (d : StratifiedData) :
    d.S_total 1 1 = 1 := by
  unfold StratifiedData.S_total
  linarith [d.p_sum]

/-- **Result 97c.** The coproduct susceptible fraction is in [0,1]
when each Si ∈ [0,1]. -/
theorem stratified_S_in_unit (d : StratifiedData) (S1 S2 : ℝ)
    (h1 : 0 ≤ S1) (h2 : 0 ≤ S2)
    (h1' : S1 ≤ 1) (h2' : S2 ≤ 1) :
    0 ≤ d.S_total S1 S2 ∧ d.S_total S1 S2 ≤ 1 := by
  unfold StratifiedData.S_total
  constructor
  · have := mul_nonneg (le_of_lt d.p1_pos) h1
    have := mul_nonneg (le_of_lt d.p2_pos) h2
    linarith
  · have := mul_le_mul_of_nonneg_left h1' (le_of_lt d.p1_pos)
    have := mul_le_mul_of_nonneg_left h2' (le_of_lt d.p2_pos)
    linarith [d.p_sum]

/-- **Result 97d.** The coproduct dimension is the sum of individual dimensions.
**Tautological Lean statement:** `d₁ + d₂ = d₁ + d₂`, proved by `rfl`.
With mixing, a single type's system is not an invariant subsystem of the
joint system, so it is not injected into it. -/
theorem stratified_dim (d : StratifiedData) :
    d.layer1.dim + d.layer2.dim = d.layer1.dim + d.layer2.dim := by rfl

/-! ## Result 98: Natural transformation — adding stages

The method of stages defines a map η_n: EBCM_Exp → EBCM_Erlang (informally a
natural transformation; no category is defined) that replaces each exponential
infectious period with n Erlang sub-stages.

Key property: η_n preserves the PGF and the mean infectious period.
T_n = 1 − (nγ/(β+nγ))^n increases with n towards 1 − exp(−β/γ), so R₀ and the
final size change (`stages_change_transmissibility`). -/

/-- Data for the stages natural transformation. -/
structure StagesNatTransData where
  beta : ℝ       -- per-edge transmission rate
  gamma : ℝ      -- recovery rate (base)
  n : ℕ          -- number of Erlang stages
  beta_pos : 0 < beta
  gamma_pos : 0 < gamma
  n_pos : 0 < n

/-- Transmissibility for the exponential model: T_exp = β/(β+γ). -/
def StagesNatTransData.T_exp (d : StagesNatTransData) : ℝ :=
  d.beta / (d.beta + d.gamma)

/-- Transmissibility for the n-stage Erlang model:
T_n = 1 - (nγ/(β+nγ))^n. -/
def StagesNatTransData.T_erlang (d : StagesNatTransData) : ℝ :=
  1 - (↑d.n * d.gamma / (d.beta + ↑d.n * d.gamma)) ^ d.n

/-- **Result 98a.** For n=1, the Erlang transmissibility equals the
exponential transmissibility: T₁ = β/(β+γ). -/
theorem stages_n1_recovers_exp (beta gamma : ℝ) (hb : 0 < beta) (hg : 0 < gamma) :
    1 - ((1 : ℝ) * gamma / (beta + (1 : ℝ) * gamma)) ^ 1 =
    beta / (beta + gamma) := by
  have h : beta + gamma ≠ 0 := ne_of_gt (add_pos hb hg)
  simp
  field_simp
  ring

/-- **Result 98b.** Excess-degree preservation: the excess degree ratio is independent
of the number of stages (it depends only on the PGF). Hence for any layer,
R₀ = T · excessDeg where excessDeg is fixed across the transformation.
R₀ itself changes, because T changes from T_exp to T_n.
The map η_n sends T_exp to T_n and keeps the PGF.
The Lean statement is the field identity T·e/e = T for e ≠ 0; it does not
mention stages. -/
theorem stages_preserve_excess_degree (excessDeg : ℝ) (T1 T2 : ℝ) :
    T1 * excessDeg / excessDeg = T1 ∧ T2 * excessDeg / excessDeg = T2 ∨
    excessDeg = 0 := by
  by_cases h : excessDeg = 0
  · right; exact h
  · left
    constructor <;> field_simp

/-- **Result 98c.** Mean infectious period is preserved: E[Erlang(n,nγ)] = 1/γ.
It is the identity that fixes the sub-stage rate nγ. -/
theorem stages_mean_preserved (n : ℕ) (gamma : ℝ) (hn : 0 < n) (hg : 0 < gamma) :
    (n : ℝ) / ((n : ℝ) * gamma) = 1 / gamma := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- Staging changes the transmissibility: with n = 2 stages,
    T_exp = β/(β+γ) < T_2 = 1 − (2γ/(β+2γ))², since the difference is
    β²γ/((β+γ)(β+2γ)²) > 0. So η_2 changes R₀ and the final size. -/
theorem stages_change_transmissibility (d : StagesNatTransData) (hn : d.n = 2) :
    d.T_exp < d.T_erlang := by
  unfold StagesNatTransData.T_exp StagesNatTransData.T_erlang
  rw [hn]
  simp only [Nat.cast_ofNat]
  have hb := d.beta_pos
  have hg := d.gamma_pos
  have h1 : d.beta + d.gamma ≠ 0 := by positivity
  have h2 : d.beta + 2 * d.gamma ≠ 0 := by positivity
  have key : 1 - (2 * d.gamma / (d.beta + 2 * d.gamma)) ^ 2 - d.beta / (d.beta + d.gamma) =
      d.beta ^ 2 * d.gamma / ((d.beta + d.gamma) * (d.beta + 2 * d.gamma) ^ 2) := by
    field_simp
    ring
  have hpos : 0 < d.beta ^ 2 * d.gamma / ((d.beta + d.gamma) * (d.beta + 2 * d.gamma) ^ 2) := by
    positivity
  linarith

/-- **Result 98d.** Final-size equation: the final size equation
θ∞ = 1 - T + T·g(θ∞) depends on T and the PGF g, not on the sojourn
time distribution within the infectious period. Different T values from
different stage counts may yield different final sizes, but the mapping
T ↦ finalSize(T) is the same functional form. -/
theorem stages_final_size_map (T g_val : ℝ) :
    1 - T + T * g_val = 1 - T * (1 - g_val) := by ring

/-! ## Result 99: Natural transformation — adding clustering

The clustering extension maps an unclustered EBCM to a clustered one
(informally a natural transformation η_C; no category is defined).

Key property: when the triangle stub fraction is 0, the clustered model
reduces to the standard model. -/

/-- **Result 99a.** When the clustering coefficient is zero (no triangles),
the clustered model susceptible fraction reduces to the standard EBCM
susceptible fraction. So the clustered model with no triangles is the
standard model.

The triangle stub fraction 2⟨t⟩/(2⟨t⟩+⟨s⟩) (called the clustering coefficient
in ClusteringExtension; the clustering coefficient is 2⟨t⟩/⟨k(k−1)⟩) vanishes
when ⟨t⟩ = 0. -/
theorem clustering_zero_is_identity (mean_s : ℚ) (_hs : 0 < mean_s) :
    2 * (0 : ℚ) / (2 * 0 + mean_s) = 0 := by
  simp

/-- **Result 99b.** The clustered R₀ reduces to the standard R₀ when
there are no triangle edges (⟨t⟩ = 0).
The scalar `clustered_R0` = T·excess_single + T·(2⟨t⟩/(⟨s⟩+2⟨t⟩))·(1+T) is
not the R₀ of a clustered network (ClusteringExtension, Result 72).
When ⟨t⟩ = 0: R₀_clustered = T·excess_single = R₀_standard. -/
theorem clustering_zero_R0 (T excess_s : ℚ) :
    T * excess_s + T * (2 * 0 / (excess_s + 2 * 0)) * (1 + T) =
    T * excess_s := by ring

/-! **Result 99c** (not formalised). Naturality: for any graph morphism φ that
preserves the clustering structure, the diagram commutes — applying φ then
computing the clustered EBCM gives the same result as computing the
unclustered EBCM then applying η_C. No graph morphism or natural
transformation is defined in this library, so the statement has no Lean
counterpart. (The former axiom `clustering_naturality`, whose conclusion was
`True`, has been removed.) -/

/-! ## Result 100: Monoidal structure

The multiplex product of layers (Result 96) behaves like a monoidal product
on susceptible fractions and dimensions (informal: no category is defined).
Its unit is the trivial network: degree 0, no edges.

We verify the corresponding identities for real multiplication and
natural-number addition. -/

/-- The trivial (unit) layer: degree 0, no edges, T irrelevant. The PGF is
ψ(x) = 1 (deterministic degree 0), so ψ'(1) = 0. We model the unit via its
effect on the product: S_unit = ψ_unit(θ) = 1 for all θ.

**Result 100a.** Left unitality: the trivial layer is a left unit for the
susceptible product. S_unit · S = 1 · S = S. -/
theorem monoidal_left_unit (S : ℝ) : 1 * S = S := by ring

/-- **Result 100b.** Right unitality: S · S_unit = S · 1 = S. -/
theorem monoidal_right_unit (S : ℝ) : S * 1 = S := by ring

/-- **Result 100c.** Associativity of the multiplex product:
(S₁ · S₂) · S₃ = S₁ · (S₂ · S₃). -/
theorem monoidal_assoc (S1 S2 S3 : ℝ) :
    S1 * S2 * S3 = S1 * (S2 * S3) := by ring

/-- **Result 100d.** The product ODE dimension is associative:
(d₁ + d₂) + d₃ = d₁ + (d₂ + d₃). -/
theorem monoidal_dim_assoc (d1 d2 d3 : ℕ) :
    d1 + d2 + d3 = d1 + (d2 + d3) := by omega

/-- **Result 100e.** The unit dimension is 0 (trivial ODE system):
0 + d = d and d + 0 = d. -/
theorem monoidal_dim_unit_left (d : ℕ) : 0 + d = d := by omega

theorem monoidal_dim_unit_right (d : ℕ) : d + 0 = d := by omega

/-- **Result 100f.** The real-number identities that the pentagon and
triangle identities would reduce to hold (no associator or unitor is
defined). These are
automatically satisfied for the product of real numbers (since ℝ
multiplication is a strict monoidal operation). -/
theorem monoidal_pentagon (S1 S2 S3 S4 : ℝ) :
    S1 * S2 * S3 * S4 = S1 * (S2 * (S3 * S4)) := by ring

theorem monoidal_triangle (S1 S2 : ℝ) :
    S1 * 1 * S2 = S1 * (1 * S2) := by ring

/-! ## Result 101: Epidemic threshold as a natural transformation

R₀ is a real-valued function of the layer data (informally a natural
transformation to the constant functor ℝ; no functor is defined). The key
structural property is that R₀ is monotone in
transmissibility: if T₁ ≤ T₂ then R₀(T₁) ≤ R₀(T₂). -/

/-- **Result 101a.** R₀ is monotone in transmissibility:
if T₁ ≤ T₂ and the excess degree is the same, then R₀(T₁) ≤ R₀(T₂). -/
theorem R0_monotone_in_T (T1 T2 excessDeg : ℝ)
    (hT : T1 ≤ T2) (he : 0 ≤ excessDeg) :
    T1 * excessDeg ≤ T2 * excessDeg := by
  exact mul_le_mul_of_nonneg_right hT he

/-- **Result 101b.** Strict monotonicity when excessDeg > 0. -/
theorem R0_strict_monotone_in_T (T1 T2 excessDeg : ℝ)
    (hT : T1 < T2) (he : 0 < excessDeg) :
    T1 * excessDeg < T2 * excessDeg := by
  exact mul_lt_mul_of_pos_right hT he

/-- **Result 101c.** R₀ = 0 when T = 0 (no transmission). -/
theorem R0_zero_at_T_zero (excessDeg : ℝ) :
    0 * excessDeg = 0 := by ring

/-- **Result 101d.** R₀ = excessDeg when T = 1 (complete transmission). -/
theorem R0_at_T_one (excessDeg : ℝ) :
    1 * excessDeg = excessDeg := by ring

/-- **Result 101e.** Monotonicity of R₀ in the excess degree: if e₁ ≤ e₂ and
T ≥ 0, then T·e₁ ≤ T·e₂. -/
theorem R0_monotone_in_excess (T e1 e2 : ℝ)
    (hT : 0 ≤ T) (he : e1 ≤ e2) :
    T * e1 ≤ T * e2 := by
  exact mul_le_mul_of_nonneg_left he hT

/-! ## Result 102: Pullback construction for degree correlation

The degree-correlated model is built from a mixing matrix Q and the degree
distribution (informally a pullback; no category of mixing matrices is
defined). Neutral mixing (Q(l|k) = l·pₗ/⟨k⟩) is the special case r = 0 of the
assortative family below; no category of mixing matrices, and so no terminal
object, is defined.

We formalize this using the 2-type mixing matrix from DegreeCorrelation. -/

/-- Data for the pullback construction: a mixing matrix parameterized
by assortativity r ∈ [0,1], where r=0 gives neutral (terminal) mixing. -/
structure MixingPullbackData where
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

/-- Mean degree. -/
def MixingPullbackData.meanDeg (d : MixingPullbackData) : ℝ :=
  d.k1 * d.p1 + d.k2 * d.p2

/-- Mean degree is positive. -/
theorem MixingPullbackData.meanDeg_pos (d : MixingPullbackData) :
    0 < d.meanDeg := by
  unfold MixingPullbackData.meanDeg
  have := mul_pos d.k1_pos d.p1_pos
  have := mul_pos d.k2_pos d.p2_pos
  linarith

/-- Excess degree probabilities. -/
def MixingPullbackData.q1 (d : MixingPullbackData) : ℝ :=
  d.k1 * d.p1 / d.meanDeg

def MixingPullbackData.q2 (d : MixingPullbackData) : ℝ :=
  d.k2 * d.p2 / d.meanDeg

/-- **Result 102a.** Neutral mixing: when r=0, the
mixing matrix Q(l|k) = q_l is independent of k. Setting r = 0 is a
specialisation of the family, not a universal property.
We verify that for any r, the r=0 specialization gives q₁. -/
theorem neutral_is_terminal_q1 (k1 q1 : ℝ) :
    k1 * ((0 : ℝ) + (1 - (0 : ℝ)) * q1) = k1 * q1 := by ring

/-- **Result 102b.** At r=0, the off-diagonal mixing entry k₁·(1-r)·q₂
reduces to k₁·q₂, the neutral mixing value. -/
theorem pullback_neutral_offdiag (d : MixingPullbackData) :
    d.k1 * (1 - (0 : ℝ)) * d.q2 = d.k1 * d.q2 := by ring

/-- **Result 102c.** The r = 0 specialisation of the assortative mixing
matrix.

We verify that the r=0 specialization of every mixing entry recovers
the neutral form. -/
theorem pullback_C11_neutral (k1 q1 : ℝ) :
    k1 * ((0 : ℝ) + (1 - (0 : ℝ)) * q1) = k1 * q1 := by ring

theorem pullback_C12_neutral (k1 q2 : ℝ) :
    k1 * (1 - (0 : ℝ)) * q2 = k1 * q2 := by ring

theorem pullback_C21_neutral (k2 q1 : ℝ) :
    k2 * (1 - (0 : ℝ)) * q1 = k2 * q1 := by ring

theorem pullback_C22_neutral (k2 q2 : ℝ) :
    k2 * ((0 : ℝ) + (1 - (0 : ℝ)) * q2) = k2 * q2 := by ring

/-- **Result 102d.** The neutral mixing matrix is rank-1 (det = 0): it
factors through the degree distribution. We verify that det(C_neutral) = 0 for 2×2. -/
theorem neutral_mixing_det_zero (k1 k2 q1 q2 : ℝ)
    (_hq : q1 + q2 = 1) :
    k1 * q1 * (k2 * q2) - k1 * q2 * (k2 * q1) = 0 := by ring

/-- **Result 102e.** Pullback compatibility: the degree-correlated model
recovers the uncorrelated R₀ when r=0.
For r=0, the largest eigenvalue of C = k·Q equals ⟨k²⟩/⟨k⟩, which is one
more than the largest eigenvalue ⟨k²-k⟩/⟨k⟩ of the next-generation matrix
K = (k-1)·Q; R₀ = T·⟨k²-k⟩/⟨k⟩ is the standard uncorrelated formula
(DegreeCorrelation `neutral_traceK`). The Lean statement below is the field
identity T·a/b = T·(a/b), with a/b = ⟨k²⟩/⟨k⟩. -/
theorem pullback_R0_at_neutral (T k1 k2 p1 p2 : ℝ)
    (hp : 0 < k1 * p1 + k2 * p2) :
    T * (k1 ^ 2 * p1 + k2 ^ 2 * p2) / (k1 * p1 + k2 * p2) =
    T * ((k1 ^ 2 * p1 + k2 ^ 2 * p2) / (k1 * p1 + k2 * p2)) := by
  have hd : k1 * p1 + k2 * p2 ≠ 0 := ne_of_gt hp
  field_simp

end
