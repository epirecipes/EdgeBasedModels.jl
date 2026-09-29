import Alignment.Registry
import EBCMCategory.CategoricalComposition
import EBCMCategory.ClusteringExtension
import Mathlib.Probability.Distributions.Gamma
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Blind shadow sets: group `CategoricalComposition`

Written blind. The author read only `Alignment/README.md`, `SA-PASS_SKILL.md`,
`Alignment/Example/ExampleShadows.lean`, `Alignment/DataTypes/CategoricalComposition.md`, the
entries of this group's ids in `Alignment/claims_blind.yaml`, Mathlib sources, and papers under
`papers/` (for the meaning of the degree-correlated next-generation matrix, `degreecorrelation.md`,
and the clustered-network setting, `clustering1.md`). `#check` was used only on the data types and
operations listed in the DataTypes file.

Vocabulary used (DataTypes): `EBCMLayer` (fields `mean` = ψ'(1), `secondFactorial` = ψ''(1),
`T`, `dim`), `EBCMLayer.excessDegree` (ψ''(1)/ψ'(1)), `EBCMLayer.R0`, `MultiplexProduct`
(`layer1`, `layer2`), `MultiplexProduct.R0_sum` (product R₀), `compactMultiplexDim`,
`StratifiedData` and `StratifiedData.S_total` (coproduct susceptible fraction),
`StagesNatTransData` with `T_exp`, `T_erlang`, `MixingPullbackData` with `meanDeg`, `q1`, `q2`.

Claim skipped: `CategoricalComposition.R98d.1` (see the note at its place below).

Re-authored blind (second pass, from the claim texts only): the blocks marked "(re-authored
blind)" or "(blind)" near the end of this file. That pass also imports
`EBCMCategory.ClusteringExtension` for the operations `clustering_coefficient`, `clustered_R0`,
`mean_total_degree` listed in `DataTypes/ClusteringExtension.md`, which the Result 99 texts name.
Claims of that pass not formalised (the text only describes which categorical notions are, or are
not, defined, or needs a model the vocabulary lacks): `R95.functor`, `R95a.1`, `R97.coproduct`,
`R97d.2`, `R98.natTrans`, `R98d.1`, `R99.natTrans`, `R101.natTrans`, `R102.pullback`, `R102a.2`,
`header.scope`.
-/

noncomputable section

namespace Alignment.Shadows.CategoricalComposition

/-! ## Shared helpers: text notions in primitive terms (not registered, inlined by the audit) -/

/-- The text's clustering coefficient (Result 99a), over `ℚ` as DataTypes says the clustering
claims are phrased: `C = 2⟨t⟩/(2⟨t⟩+⟨s⟩)`, with `⟨t⟩` the mean number of triangles and `⟨s⟩` the
mean number of single edges per node. -/
def clusteringCoeff (t s : ℚ) : ℚ := 2 * t / (2 * t + s)

/-- R₀ as a function of the transmissibility `τ` for the network of layer `l`, in the text's own
terms (Results 95a / 101): `R₀(τ) = τ · excessDeg`. Needed because `EBCMLayer` forces `0 < T`, so
"R₀ when T = 0" cannot be expressed through `EBCMLayer.R0`. -/
def R0atT (τ : ℝ) (l : EBCMLayer) : ℝ := τ * l.excessDegree

/-! ### r-parameterised degree mixing (Result 102)

`P(j|i)` is the probability that an edge leaving a type-`i` node ends at a type-`j` node, in the
standard assortative form `r·δᵢⱼ + (1 − r)·qⱼ` (r = 0: neutral / proportionate mixing,
r = 1: fully assortative). This agrees with the off-diagonal entry `k₁·(1-r)·q₂` quoted in
Result 102b. The mixing entries are `Cᵢⱼ = kᵢ·P(j|i)`, the connectivity matrix `C_kl = k Q(l|k)`
of the degree-correlation literature; the neutral form is `Cᵢⱼ = kᵢ·qⱼ`. -/

/-- `P(1|1) = r + (1 − r)·q₁`. -/
def P11 (d : MixingPullbackData) : ℝ := d.r + (1 - d.r) * d.q1
/-- `P(2|1) = (1 − r)·q₂`. -/
def P12 (d : MixingPullbackData) : ℝ := (1 - d.r) * d.q2
/-- `P(1|2) = (1 − r)·q₁`. -/
def P21 (d : MixingPullbackData) : ℝ := (1 - d.r) * d.q1
/-- `P(2|2) = r + (1 − r)·q₂`. -/
def P22 (d : MixingPullbackData) : ℝ := d.r + (1 - d.r) * d.q2

/-- Mixing entry `C₁₁ = k₁·(r + (1 − r)·q₁)`. -/
def C11 (d : MixingPullbackData) : ℝ := d.k1 * (d.r + (1 - d.r) * d.q1)
/-- Mixing entry `C₁₂ = k₁·(1-r)·q₂` (verbatim form of Result 102b). -/
def C12 (d : MixingPullbackData) : ℝ := d.k1 * (1 - d.r) * d.q2
/-- Mixing entry `C₂₁ = k₂·(1-r)·q₁`. -/
def C21 (d : MixingPullbackData) : ℝ := d.k2 * (1 - d.r) * d.q1
/-- Mixing entry `C₂₂ = k₂·(r + (1 − r)·q₂)`. -/
def C22 (d : MixingPullbackData) : ℝ := d.k2 * (d.r + (1 - d.r) * d.q2)

/-- Edge-based next-generation matrix of the degree-correlated model with transmissibility `τ`:
`Mᵢⱼ = τ·P(j|i)·(kⱼ − 1)` (an edge reaching a degree-`kⱼ` node opens `kⱼ − 1` further edges;
`D_kl = (l − 1) Q(l|k)` in `papers/degreecorrelation.md`). Its largest eigenvalue is the R₀ of the
degree-correlated model. -/
def ngm (d : MixingPullbackData) (τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![τ * P11 d * (d.k1 - 1), τ * P12 d * (d.k2 - 1);
     τ * P21 d * (d.k1 - 1), τ * P22 d * (d.k2 - 1)]

/-- Uncorrelated (configuration-model) R₀ for the two-class degree distribution
(`P(k₁) = p₁`, `P(k₂) = p₂`), in primitive terms: `τ·⟨k(k−1)⟩/⟨k⟩`. -/
def R0uncorr (d : MixingPullbackData) (τ : ℝ) : ℝ :=
  τ * (d.p1 * d.k1 * (d.k1 - 1) + d.p2 * d.k2 * (d.k2 - 1)) / (d.p1 * d.k1 + d.p2 * d.k2)

end Alignment.Shadows.CategoricalComposition

/-! ## `CategoricalComposition.R95a.2`

Text: "We verify that R₀ = T · ψ''(1)/ψ'(1) for the resulting system." -/
namespace Alignment.Shadows.CategoricalComposition.R95a_2

-- AMBIGUITY: "for the resulting system" read as: for every EBCM layer (every composed
-- (Graph, Disease) system, which DataTypes represents as `EBCMLayer`).
-- AMBIGUITY: "T · ψ''(1)/ψ'(1)" read as T · (ψ''(1)/ψ'(1)) (the same real as (T·ψ''(1))/ψ'(1)).
/-- Intended statement: every layer has R₀ = T · ψ''(1)/ψ'(1), in the layer's primitive fields. -/
@[sa_reference "CategoricalComposition.R95a.2"]
def T : Prop := ∀ l : EBCMLayer, l.R0 = l.T * (l.secondFactorial / l.mean)

/-- S1: the R₀ formula (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R95a.2" 1]
def S1 : Prop := ∀ l : EBCMLayer, l.R0 = l.T * (l.secondFactorial / l.mean)

@[sa_ref_forward "CategoricalComposition.R95a.2" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R95a.2"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R95a_2

/-! ## `CategoricalComposition.R96a`

Text: "**Result 96a.** Product susceptible fraction: S = S₁ · S₂. For layer susceptible fractions
S₁ ∈ (0,1] and S₂ ∈ (0,1], the product S₁·S₂ ∈ (0,1]." -/
namespace Alignment.Shadows.CategoricalComposition.R96a

-- VOCAB-GAP: there is no Lean definition of a layer's susceptible fraction or of the product
-- susceptible fraction; S = S₁ · S₂ is taken as the text's definition and stated on reals.
/-- Intended statement: for S₁, S₂ ∈ (0,1], the product S₁·S₂ lies in (0,1]. -/
@[sa_reference "CategoricalComposition.R96a"]
def T : Prop :=
  ∀ S₁ S₂ : ℝ, 0 < S₁ → S₁ ≤ 1 → 0 < S₂ → S₂ ≤ 1 → 0 < S₁ * S₂ ∧ S₁ * S₂ ≤ 1

/-- S1: the product is positive. -/
@[sa_shadow "CategoricalComposition.R96a" 1]
def S1 : Prop := ∀ S₁ S₂ : ℝ, 0 < S₁ → S₁ ≤ 1 → 0 < S₂ → S₂ ≤ 1 → 0 < S₁ * S₂

/-- S2: the product is at most one. -/
@[sa_shadow "CategoricalComposition.R96a" 2]
def S2 : Prop := ∀ S₁ S₂ : ℝ, 0 < S₁ → S₁ ≤ 1 → 0 < S₂ → S₂ ≤ 1 → S₁ * S₂ ≤ 1

@[sa_ref_forward "CategoricalComposition.R96a" 1]
theorem ref_fwd1 : T → S1 := fun t a b h1 h2 h3 h4 => (t a b h1 h2 h3 h4).1

@[sa_ref_forward "CategoricalComposition.R96a" 2]
theorem ref_fwd2 : T → S2 := fun t a b h1 h2 h3 h4 => (t a b h1 h2 h3 h4).2

@[sa_complete "CategoricalComposition.R96a"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun a b h1 h2 h3 h4 => ⟨s1 a b h1 h2 h3 h4, s2 a b h1 h2 h3 h4⟩

end Alignment.Shadows.CategoricalComposition.R96a

/-! ## `CategoricalComposition.R96d`

Text: "**Result 96d.** A two-layer compact multiplex system has 3 ODEs." -/
namespace Alignment.Shadows.CategoricalComposition.R96d

/-- Intended statement: the compact multiplex system with 2 layers has 3 ODEs. -/
@[sa_reference "CategoricalComposition.R96d"]
def T : Prop := compactMultiplexDim 2 = 3

/-- S1: the ODE count for two layers is 3. -/
@[sa_shadow "CategoricalComposition.R96d" 1]
def S1 : Prop := compactMultiplexDim 2 = 3

@[sa_ref_forward "CategoricalComposition.R96d" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R96d"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R96d

/-! ## `CategoricalComposition.R96e`

Text: "**Result 96e.** A three-layer compact multiplex system has 4 ODEs." -/
namespace Alignment.Shadows.CategoricalComposition.R96e

/-- Intended statement: the compact multiplex system with 3 layers has 4 ODEs. -/
@[sa_reference "CategoricalComposition.R96e"]
def T : Prop := compactMultiplexDim 3 = 4

/-- S1: the ODE count for three layers is 4. -/
@[sa_shadow "CategoricalComposition.R96e" 1]
def S1 : Prop := compactMultiplexDim 3 = 4

@[sa_ref_forward "CategoricalComposition.R96e" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R96e"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R96e

/-! ## `CategoricalComposition.R96g`

Text: "**Result 96g.** If the first layer is supercritical, then the additive multiplex threshold
is also supercritical." -/
namespace Alignment.Shadows.CategoricalComposition.R96g

-- AMBIGUITY: "supercritical" read as R₀ > 1; "the additive multiplex threshold" read as the
-- product R₀ `R0_sum` (the additive combination of per-layer contributions).
/-- Intended statement: for every multiplex product, layer1.R0 > 1 implies R0_sum > 1. -/
@[sa_reference "CategoricalComposition.R96g"]
def T : Prop := ∀ p : MultiplexProduct, 1 < p.layer1.R0 → 1 < p.R0_sum

/-- S1: the supercriticality implication (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R96g" 1]
def S1 : Prop := ∀ p : MultiplexProduct, 1 < p.layer1.R0 → 1 < p.R0_sum

@[sa_ref_forward "CategoricalComposition.R96g" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R96g"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R96g

/-! ## `CategoricalComposition.R97b`

Text: "**Result 97b.** The coproduct susceptible fraction at t=0 is 1 (everyone starts
susceptible)." -/
namespace Alignment.Shadows.CategoricalComposition.R97b

-- VOCAB-GAP: no Lean definition of the layer susceptible fractions S₁(t), S₂(t). "Everyone
-- starts susceptible" is taken as S₁(0) = S₂(0) = 1, fed to the coproduct operation `S_total`.
/-- Intended statement: for every stratified model, S_total at S₁ = S₂ = 1 equals 1. -/
@[sa_reference "CategoricalComposition.R97b"]
def T : Prop := ∀ d : StratifiedData, d.S_total 1 1 = 1

/-- S1: the initial coproduct susceptible fraction is 1. -/
@[sa_shadow "CategoricalComposition.R97b" 1]
def S1 : Prop := ∀ d : StratifiedData, d.S_total 1 1 = 1

@[sa_ref_forward "CategoricalComposition.R97b" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R97b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R97b

/-! ## `CategoricalComposition.R97c`

Text: "**Result 97c.** The coproduct susceptible fraction is in [0,1] when each Si ∈ [0,1]." -/
namespace Alignment.Shadows.CategoricalComposition.R97c

/-- Intended statement: for every stratified model and S₁, S₂ ∈ [0,1], S_total ∈ [0,1]. -/
@[sa_reference "CategoricalComposition.R97c"]
def T : Prop :=
  ∀ (d : StratifiedData) (S₁ S₂ : ℝ), 0 ≤ S₁ → S₁ ≤ 1 → 0 ≤ S₂ → S₂ ≤ 1 →
    0 ≤ d.S_total S₁ S₂ ∧ d.S_total S₁ S₂ ≤ 1

/-- S1: lower bound 0. -/
@[sa_shadow "CategoricalComposition.R97c" 1]
def S1 : Prop :=
  ∀ (d : StratifiedData) (S₁ S₂ : ℝ), 0 ≤ S₁ → S₁ ≤ 1 → 0 ≤ S₂ → S₂ ≤ 1 → 0 ≤ d.S_total S₁ S₂

/-- S2: upper bound 1. -/
@[sa_shadow "CategoricalComposition.R97c" 2]
def S2 : Prop :=
  ∀ (d : StratifiedData) (S₁ S₂ : ℝ), 0 ≤ S₁ → S₁ ≤ 1 → 0 ≤ S₂ → S₂ ≤ 1 → d.S_total S₁ S₂ ≤ 1

@[sa_ref_forward "CategoricalComposition.R97c" 1]
theorem ref_fwd1 : T → S1 := fun t d a b h1 h2 h3 h4 => (t d a b h1 h2 h3 h4).1

@[sa_ref_forward "CategoricalComposition.R97c" 2]
theorem ref_fwd2 : T → S2 := fun t d a b h1 h2 h3 h4 => (t d a b h1 h2 h3 h4).2

@[sa_complete "CategoricalComposition.R97c"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun d a b h1 h2 h3 h4 => ⟨s1 d a b h1 h2 h3 h4, s2 d a b h1 h2 h3 h4⟩

end Alignment.Shadows.CategoricalComposition.R97c

/-! ## `CategoricalComposition.R97d.1`

Text: "**Result 97d.** The coproduct dimension is the sum of individual dimensions." -/
namespace Alignment.Shadows.CategoricalComposition.R97d_1

-- VOCAB-GAP: DataTypes lists no dimension operation for the coproduct (`StratifiedData`). The
-- coproduct system's dimension is stated as the number of its state variables: the ODE variables
-- of the coproduct are the disjoint union (the coproduct in finite sets) of the two layers'
-- variable index sets `Fin dim₁ ⊕ Fin dim₂`.
/-- Intended statement: for every stratified (coproduct) model, the number of state variables of
the coproduct system is dim₁ + dim₂. -/
@[sa_reference "CategoricalComposition.R97d.1"]
def T : Prop :=
  ∀ d : StratifiedData,
    Fintype.card (Fin d.layer1.dim ⊕ Fin d.layer2.dim) = d.layer1.dim + d.layer2.dim

/-- S1: the coproduct dimension formula (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R97d.1" 1]
def S1 : Prop :=
  ∀ d : StratifiedData,
    Fintype.card (Fin d.layer1.dim ⊕ Fin d.layer2.dim) = d.layer1.dim + d.layer2.dim

@[sa_ref_forward "CategoricalComposition.R97d.1" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R97d.1"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R97d_1

/-! ## `CategoricalComposition.R98a`

Text: "**Result 98a.** For n=1, the Erlang transmissibility equals the exponential
transmissibility: T₁ = β/(β+γ)." -/
namespace Alignment.Shadows.CategoricalComposition.R98a

/-- Intended statement: for every stages datum with n = 1, T_erlang = T_exp and
T_erlang = β/(β+γ). -/
@[sa_reference "CategoricalComposition.R98a"]
def T : Prop :=
  ∀ d : StagesNatTransData, d.n = 1 →
    d.T_erlang = d.T_exp ∧ d.T_erlang = d.beta / (d.beta + d.gamma)

/-- S1: for n = 1 the Erlang transmissibility equals the exponential-model operation `T_exp`. -/
@[sa_shadow "CategoricalComposition.R98a" 1]
def S1 : Prop := ∀ d : StagesNatTransData, d.n = 1 → d.T_erlang = d.T_exp

/-- S2: for n = 1 the Erlang transmissibility is β/(β+γ) in primitive terms. -/
@[sa_shadow "CategoricalComposition.R98a" 2]
def S2 : Prop := ∀ d : StagesNatTransData, d.n = 1 → d.T_erlang = d.beta / (d.beta + d.gamma)

@[sa_ref_forward "CategoricalComposition.R98a" 1]
theorem ref_fwd1 : T → S1 := fun t d h => (t d h).1

@[sa_ref_forward "CategoricalComposition.R98a" 2]
theorem ref_fwd2 : T → S2 := fun t d h => (t d h).2

@[sa_complete "CategoricalComposition.R98a"]
theorem complete (s1 : S1) (s2 : S2) : T := fun d h => ⟨s1 d h, s2 d h⟩

end Alignment.Shadows.CategoricalComposition.R98a

/-! ## `CategoricalComposition.R98c.1`

Text: "**Result 98c.** Mean infectious period is preserved: E[Erlang(n,nγ)] = 1/γ." -/
namespace Alignment.Shadows.CategoricalComposition.R98c_1

-- VOCAB-GAP: no Erlang distribution or expectation in the DataTypes. Erlang(n, nγ) is the gamma
-- distribution with integer shape n and rate nγ (`ProbabilityTheory.gammaMeasure n (n·γ)`), and
-- E[·] is the integral of the identity against it.
-- AMBIGUITY: "E[Erlang(n,nγ)]" read as the actual expectation (measure-theoretic integral), not
-- as the closed-form shape/rate ratio n/(nγ).
/-- Intended statement: for every stages datum, ∫ x d(Erlang(n, nγ)) = 1/γ. -/
@[sa_reference "CategoricalComposition.R98c.1"]
def T : Prop :=
  ∀ d : StagesNatTransData,
    MeasureTheory.integral (ProbabilityTheory.gammaMeasure (d.n : ℝ) ((d.n : ℝ) * d.gamma))
      (fun x : ℝ => x) = 1 / d.gamma

/-- S1: the mean of Erlang(n, nγ) is 1/γ (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R98c.1" 1]
def S1 : Prop :=
  ∀ d : StagesNatTransData,
    MeasureTheory.integral (ProbabilityTheory.gammaMeasure (d.n : ℝ) ((d.n : ℝ) * d.gamma))
      (fun x : ℝ => x) = 1 / d.gamma

@[sa_ref_forward "CategoricalComposition.R98c.1" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R98c.1"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R98c_1

/-! ## `CategoricalComposition.R98d.1` — SKIPPED (no falsifiable content)

Text: "**Result 98d.** Final size preservation: the final size equation θ∞ = 1 - T + T·g(θ∞)
depends on T and the PGF g, not on the sojourn time distribution within the infectious period."

No shadow set is written. The DataTypes have no sojourn-time distribution beyond the stage data,
and no final size of any model. The only formal rendering of "the equation depends on T and g
only" is: for stage data `d₁`, `d₂` with equal transmissibility, the fixed-point sets of
`x ↦ 1 − T + T·g(x)` coincide. That is a congruence (`h ▸ Iff.rfl`), a tautology that no
implementation can falsify, which the guidelines forbid as a shadow. -/

/-! ## `CategoricalComposition.R99b.1`

Text: "**Result 99b.** The clustered R₀ reduces to the standard R₀ when there are no triangle
edges (⟨t⟩ = 0). [...] When ⟨t⟩ = 0: R₀_clustered = T·excess_single = R₀_standard." -/
namespace Alignment.Shadows.CategoricalComposition.R99b_1

-- VOCAB-GAP: there is no Lean definition of a clustered R₀, and the blind text gives no formula
-- for it (the omitted "[...]" lines may hold one). Only the checkable part is formalised, the
-- identity "T·excess_single = R₀_standard": with no triangle edges every edge is a single edge,
-- so the network is an ordinary EBCM layer whose excess degree is the single-edge excess degree.
-- The main content, "R₀_clustered = T·excess_single when ⟨t⟩ = 0", is NOT checked by this set.
/-- Intended statement (checkable part): every EBCM layer has R₀ = T · excessDegree. -/
@[sa_reference "CategoricalComposition.R99b.1"]
def T : Prop := ∀ l : EBCMLayer, l.R0 = l.T * l.excessDegree

/-- S1: the standard R₀ equals T times the (single-edge) excess degree. -/
@[sa_shadow "CategoricalComposition.R99b.1" 1]
def S1 : Prop := ∀ l : EBCMLayer, l.R0 = l.T * l.excessDegree

@[sa_ref_forward "CategoricalComposition.R99b.1" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R99b.1"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R99b_1

/-! ## `CategoricalComposition.R100a`

Text: "**Result 100a.** Left unitality: the trivial layer is a left unit for the susceptible
product. S_unit · S = 1 · S = S." -/
namespace Alignment.Shadows.CategoricalComposition.R100a

-- VOCAB-GAP: no Lean trivial layer or susceptible fraction; per the text, S_unit = 1 and the
-- susceptible product is real multiplication.
/-- Intended statement: 1 · S = S for every susceptible fraction S. -/
@[sa_reference "CategoricalComposition.R100a"]
def T : Prop := ∀ S : ℝ, 1 * S = S

/-- S1: left unit law (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R100a" 1]
def S1 : Prop := ∀ S : ℝ, 1 * S = S

@[sa_ref_forward "CategoricalComposition.R100a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R100a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R100a

/-! ## `CategoricalComposition.R100b`

Text: "**Result 100b.** Right unitality: S · S_unit = S · 1 = S." -/
namespace Alignment.Shadows.CategoricalComposition.R100b

-- VOCAB-GAP: as in R100a (S_unit = 1, product = real multiplication).
/-- Intended statement: S · 1 = S for every susceptible fraction S. -/
@[sa_reference "CategoricalComposition.R100b"]
def T : Prop := ∀ S : ℝ, S * 1 = S

/-- S1: right unit law (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R100b" 1]
def S1 : Prop := ∀ S : ℝ, S * 1 = S

@[sa_ref_forward "CategoricalComposition.R100b" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R100b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R100b

/-! ## `CategoricalComposition.R100c`

Text: "**Result 100c.** Associativity of the multiplex product: (S₁ · S₂) · S₃ = S₁ · (S₂ · S₃)." -/
namespace Alignment.Shadows.CategoricalComposition.R100c

-- VOCAB-GAP: the multiplex product on susceptible fractions is real multiplication (Result 96a).
/-- Intended statement: the susceptible product is associative. -/
@[sa_reference "CategoricalComposition.R100c"]
def T : Prop := ∀ S₁ S₂ S₃ : ℝ, (S₁ * S₂) * S₃ = S₁ * (S₂ * S₃)

/-- S1: associativity (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R100c" 1]
def S1 : Prop := ∀ S₁ S₂ S₃ : ℝ, (S₁ * S₂) * S₃ = S₁ * (S₂ * S₃)

@[sa_ref_forward "CategoricalComposition.R100c" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R100c"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R100c

/-! ## `CategoricalComposition.R100d`

Text: "**Result 100d.** The product ODE dimension is associative: (d₁ + d₂) + d₃ = d₁ + (d₂ + d₃)." -/
namespace Alignment.Shadows.CategoricalComposition.R100d

-- VOCAB-GAP: `MultiplexProduct` has exactly two layers, so a triple product cannot be formed;
-- the claim is stated, as the text writes it, on natural-number dimensions.
/-- Intended statement: addition of ODE dimensions is associative. -/
@[sa_reference "CategoricalComposition.R100d"]
def T : Prop := ∀ d₁ d₂ d₃ : ℕ, (d₁ + d₂) + d₃ = d₁ + (d₂ + d₃)

/-- S1: associativity of the dimension sum (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R100d" 1]
def S1 : Prop := ∀ d₁ d₂ d₃ : ℕ, (d₁ + d₂) + d₃ = d₁ + (d₂ + d₃)

@[sa_ref_forward "CategoricalComposition.R100d" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R100d"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R100d

/-! ## `CategoricalComposition.R100e`

Text: "**Result 100e.** The unit dimension is 0 (trivial ODE system): 0 + d = d and d + 0 = d." -/
namespace Alignment.Shadows.CategoricalComposition.R100e

-- VOCAB-GAP: no Lean trivial ODE system; its dimension is 0 per the text, and the unit laws are
-- stated on natural-number dimensions as written.
-- NOTE: S2 (`d + 0 = d`) holds definitionally in ℕ. It is kept because the text states it
-- explicitly as half of the conjunction.
/-- Intended statement: 0 is a two-sided unit for the dimension sum. -/
@[sa_reference "CategoricalComposition.R100e"]
def T : Prop := (∀ d : ℕ, 0 + d = d) ∧ (∀ d : ℕ, d + 0 = d)

/-- S1: left unit law for dimensions. -/
@[sa_shadow "CategoricalComposition.R100e" 1]
def S1 : Prop := ∀ d : ℕ, 0 + d = d

/-- S2: right unit law for dimensions. -/
@[sa_shadow "CategoricalComposition.R100e" 2]
def S2 : Prop := ∀ d : ℕ, d + 0 = d

@[sa_ref_forward "CategoricalComposition.R100e" 1]
theorem ref_fwd1 : T → S1 := fun t => t.1

@[sa_ref_forward "CategoricalComposition.R100e" 2]
theorem ref_fwd2 : T → S2 := fun t => t.2

@[sa_complete "CategoricalComposition.R100e"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.CategoricalComposition.R100e

/-! ## `CategoricalComposition.R101a`

Text: "**Result 101a.** R₀ is monotone in transmissibility: if T₁ ≤ T₂ and the excess degree is
the same, then R₀(T₁) ≤ R₀(T₂)." -/
namespace Alignment.Shadows.CategoricalComposition.R101a

-- AMBIGUITY: read over EBCM layers: two layers with the same excess degree, whose
-- transmissibilities satisfy T₁ ≤ T₂, have ordered R₀. No other field is constrained.
/-- Intended statement: for layers with equal excess degree, T₁ ≤ T₂ implies R₀₁ ≤ R₀₂. -/
@[sa_reference "CategoricalComposition.R101a"]
def T : Prop :=
  ∀ l₁ l₂ : EBCMLayer, l₁.T ≤ l₂.T → l₁.excessDegree = l₂.excessDegree → l₁.R0 ≤ l₂.R0

/-- S1: monotonicity in T (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R101a" 1]
def S1 : Prop :=
  ∀ l₁ l₂ : EBCMLayer, l₁.T ≤ l₂.T → l₁.excessDegree = l₂.excessDegree → l₁.R0 ≤ l₂.R0

@[sa_ref_forward "CategoricalComposition.R101a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R101a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R101a

/-! ## `CategoricalComposition.R101b`

Text: "**Result 101b.** Strict monotonicity when excessDeg > 0." -/
namespace Alignment.Shadows.CategoricalComposition.R101b

-- AMBIGUITY: read as the strict version of Result 101a, "if T₁ < T₂, the excess degree is the
-- same and positive, then R₀(T₁) < R₀(T₂)", over EBCM layers.
/-- Intended statement: for layers with equal positive excess degree, T₁ < T₂ implies
R₀₁ < R₀₂. -/
@[sa_reference "CategoricalComposition.R101b"]
def T : Prop :=
  ∀ l₁ l₂ : EBCMLayer, l₁.T < l₂.T → l₁.excessDegree = l₂.excessDegree →
    0 < l₁.excessDegree → l₁.R0 < l₂.R0

/-- S1: strict monotonicity in T (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R101b" 1]
def S1 : Prop :=
  ∀ l₁ l₂ : EBCMLayer, l₁.T < l₂.T → l₁.excessDegree = l₂.excessDegree →
    0 < l₁.excessDegree → l₁.R0 < l₂.R0

@[sa_ref_forward "CategoricalComposition.R101b" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R101b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R101b

/-! ## `CategoricalComposition.R101c`

Text: "**Result 101c.** R₀ = 0 when T = 0 (no transmission)." -/
namespace Alignment.Shadows.CategoricalComposition.R101c

-- VOCAB-GAP: `EBCMLayer` requires 0 < T, so "R₀ of a layer with T = 0" would be vacuous. R₀ is
-- instead read as the function of transmissibility of Results 95a/101, R₀(τ) = τ·excessDeg
-- (`R0atT`), evaluated at τ = 0 for the network of any layer.
/-- Intended statement: for every layer's network, R₀(0) = 0. -/
@[sa_reference "CategoricalComposition.R101c"]
def T : Prop := ∀ l : EBCMLayer, R0atT 0 l = 0

/-- S1: zero transmissibility gives zero R₀ (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R101c" 1]
def S1 : Prop := ∀ l : EBCMLayer, R0atT 0 l = 0

@[sa_ref_forward "CategoricalComposition.R101c" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R101c"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R101c

/-! ## `CategoricalComposition.R101d`

Text: "**Result 101d.** R₀ = excessDeg when T = 1 (complete transmission)." -/
namespace Alignment.Shadows.CategoricalComposition.R101d

-- AMBIGUITY: read over EBCM layers (T = 1 is allowed by `T_le_one`): a layer with T = 1 has
-- R0 = excessDegree.
/-- Intended statement: every layer with T = 1 has R₀ equal to its excess degree. -/
@[sa_reference "CategoricalComposition.R101d"]
def T : Prop := ∀ l : EBCMLayer, l.T = 1 → l.R0 = l.excessDegree

/-- S1: complete transmission gives R₀ = excess degree (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R101d" 1]
def S1 : Prop := ∀ l : EBCMLayer, l.T = 1 → l.R0 = l.excessDegree

@[sa_ref_forward "CategoricalComposition.R101d" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R101d"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R101d

/-! ## `CategoricalComposition.meanDegPos`

Text: "Mean degree is positive." -/
namespace Alignment.Shadows.CategoricalComposition.meanDegPos

-- AMBIGUITY: "Mean degree" read as the operation `MixingPullbackData.meanDeg` (the only
-- mean-degree operation in the DataTypes; `EBCMLayer.mean` is a field with a built-in positivity
-- invariant).
/-- Intended statement: every mixing-pullback datum has positive mean degree. -/
@[sa_reference "CategoricalComposition.meanDegPos"]
def T : Prop := ∀ d : MixingPullbackData, 0 < d.meanDeg

/-- S1: positivity of the mean degree (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.meanDegPos" 1]
def S1 : Prop := ∀ d : MixingPullbackData, 0 < d.meanDeg

@[sa_ref_forward "CategoricalComposition.meanDegPos" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.meanDegPos"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.meanDegPos

/-! ## `CategoricalComposition.R102a.3`

Text: "We verify that for any r, the r=0 specialization gives q₁." -/
namespace Alignment.Shadows.CategoricalComposition.R102a_3

-- VOCAB-GAP: no Lean mixing matrix. The r-dependent quantity that "gives q₁" at r = 0 is read as
-- the same-type mixing probability P(1|1) = r + (1 − r)·q₁ (`P11`).
-- AMBIGUITY: the text gives no formula for the r-dependent quantity. The assortative convex
-- combination r·δᵢⱼ + (1 − r)·qⱼ is chosen, consistent with the off-diagonal entry k₁·(1-r)·q₂ of
-- Result 102b. "for any r, the r=0 specialization" is read as: for every mixing datum, when its
-- assortativity r is 0.
/-- Intended statement: for every mixing datum with r = 0, P(1|1) = q₁. -/
@[sa_reference "CategoricalComposition.R102a.3"]
def T : Prop := ∀ d : MixingPullbackData, d.r = 0 → P11 d = d.q1

/-- S1: the r = 0 specialization of P(1|1) is q₁ (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R102a.3" 1]
def S1 : Prop := ∀ d : MixingPullbackData, d.r = 0 → P11 d = d.q1

@[sa_ref_forward "CategoricalComposition.R102a.3" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R102a.3"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R102a_3

/-! ## `CategoricalComposition.R102b`

Text: "**Result 102b.** At r=0, the off-diagonal mixing entry k₁·(1-r)·q₂ reduces to k₁·q₂, the
neutral mixing value." -/
namespace Alignment.Shadows.CategoricalComposition.R102b

/-- Intended statement: for every mixing datum with r = 0, k₁·(1-r)·q₂ = k₁·q₂. -/
@[sa_reference "CategoricalComposition.R102b"]
def T : Prop := ∀ d : MixingPullbackData, d.r = 0 → d.k1 * (1 - d.r) * d.q2 = d.k1 * d.q2

/-- S1: the off-diagonal entry reduces to its neutral value (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R102b" 1]
def S1 : Prop := ∀ d : MixingPullbackData, d.r = 0 → d.k1 * (1 - d.r) * d.q2 = d.k1 * d.q2

@[sa_ref_forward "CategoricalComposition.R102b" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R102b"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R102b

/-! ## `CategoricalComposition.R102c.2`

Text: "We verify that the r=0 specialization of every mixing entry recovers the neutral form." -/
namespace Alignment.Shadows.CategoricalComposition.R102c_2

-- VOCAB-GAP: no Lean mixing matrix; the entries are Cᵢⱼ = kᵢ·P(j|i) (`C11`, `C12`, `C21`,
-- `C22`), and the neutral form is Cᵢⱼ = kᵢ·qⱼ.
-- AMBIGUITY: only the off-diagonal entry k₁·(1-r)·q₂ is given by the text (Result 102b). The
-- diagonal entries use the assortative form kᵢ·(r + (1 − r)·qᵢ) and the other off-diagonal entry
-- k₂·(1-r)·q₁ by symmetry.
/-- Intended statement: at r = 0 each of the four mixing entries equals its neutral value. -/
@[sa_reference "CategoricalComposition.R102c.2"]
def T : Prop :=
  ∀ d : MixingPullbackData, d.r = 0 →
    C11 d = d.k1 * d.q1 ∧ C12 d = d.k1 * d.q2 ∧ C21 d = d.k2 * d.q1 ∧ C22 d = d.k2 * d.q2

/-- S1: entry (1,1) recovers k₁·q₁. -/
@[sa_shadow "CategoricalComposition.R102c.2" 1]
def S1 : Prop := ∀ d : MixingPullbackData, d.r = 0 → C11 d = d.k1 * d.q1

/-- S2: entry (1,2) recovers k₁·q₂. -/
@[sa_shadow "CategoricalComposition.R102c.2" 2]
def S2 : Prop := ∀ d : MixingPullbackData, d.r = 0 → C12 d = d.k1 * d.q2

/-- S3: entry (2,1) recovers k₂·q₁. -/
@[sa_shadow "CategoricalComposition.R102c.2" 3]
def S3 : Prop := ∀ d : MixingPullbackData, d.r = 0 → C21 d = d.k2 * d.q1

/-- S4: entry (2,2) recovers k₂·q₂. -/
@[sa_shadow "CategoricalComposition.R102c.2" 4]
def S4 : Prop := ∀ d : MixingPullbackData, d.r = 0 → C22 d = d.k2 * d.q2

@[sa_ref_forward "CategoricalComposition.R102c.2" 1]
theorem ref_fwd1 : T → S1 := fun t d h => (t d h).1

@[sa_ref_forward "CategoricalComposition.R102c.2" 2]
theorem ref_fwd2 : T → S2 := fun t d h => (t d h).2.1

@[sa_ref_forward "CategoricalComposition.R102c.2" 3]
theorem ref_fwd3 : T → S3 := fun t d h => (t d h).2.2.1

@[sa_ref_forward "CategoricalComposition.R102c.2" 4]
theorem ref_fwd4 : T → S4 := fun t d h => (t d h).2.2.2

@[sa_complete "CategoricalComposition.R102c.2"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T :=
  fun d h => ⟨s1 d h, s2 d h, s3 d h, s4 d h⟩

end Alignment.Shadows.CategoricalComposition.R102c_2

/-! ## `CategoricalComposition.R102d.2`

Text: "We verify that det(C_neutral) = 0 for 2×2." -/
namespace Alignment.Shadows.CategoricalComposition.R102d_2

-- VOCAB-GAP: no Lean mixing matrix. C_neutral = [[k₁q₁, k₁q₂], [k₂q₁, k₂q₂]] (neutral form,
-- Result 102b/102c).
-- AMBIGUITY: "det ... for 2×2" read as the 2×2 determinant C₁₁·C₂₂ − C₁₂·C₂₁ in primitive terms.
-- It equals `Matrix.det !![…]` by `Matrix.det_fin_two`; the Matrix API is not used.
/-- Intended statement: for every mixing datum the neutral 2×2 mixing matrix has zero
determinant. -/
@[sa_reference "CategoricalComposition.R102d.2"]
def T : Prop :=
  ∀ d : MixingPullbackData,
    (d.k1 * d.q1) * (d.k2 * d.q2) - (d.k1 * d.q2) * (d.k2 * d.q1) = 0

/-- S1: the determinant vanishes (single atomic requirement). -/
@[sa_shadow "CategoricalComposition.R102d.2" 1]
def S1 : Prop :=
  ∀ d : MixingPullbackData,
    (d.k1 * d.q1) * (d.k2 * d.q2) - (d.k1 * d.q2) * (d.k2 * d.q1) = 0

@[sa_ref_forward "CategoricalComposition.R102d.2" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "CategoricalComposition.R102d.2"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R102d_2

/-! ## `CategoricalComposition.R102e.1`

Text: "**Result 102e.** Pullback compatibility: the degree-correlated model recovers the
uncorrelated R₀ when r=0." -/
namespace Alignment.Shadows.CategoricalComposition.R102e_1

-- VOCAB-GAP: no Lean degree-correlated R₀ and no eigenvalues in the DataTypes. The R₀ of the
-- degree-correlated model is read as the largest eigenvalue of the edge-based next-generation
-- matrix `ngm d τ` (Mᵢⱼ = τ·P(j|i)·(kⱼ − 1); papers/degreecorrelation.md, D_kl = (l−1)Q(l|k)).
-- The uncorrelated R₀ is τ·⟨k(k−1)⟩/⟨k⟩ for the two-class degree distribution (`R0uncorr`).
-- AMBIGUITY: the transmissibility τ is not a field of `MixingPullbackData`; it is quantified over
-- (0, 1] as for `EBCMLayer.T`.
-- AMBIGUITY: degrees kᵢ read as ≥ 1 (a node reached along an edge has kᵢ − 1 ≥ 0 further
-- edges). Without this the "largest eigenvalue" part fails for 0 < kᵢ < 1, where τ·⟨k(k−1)⟩/⟨k⟩
-- is negative.
-- AMBIGUITY: "recovers" is split into (S1) the uncorrelated R₀ is an eigenvalue of the r = 0
-- matrix, and (S2) no eigenvalue exceeds it.
/-- Intended statement: at r = 0, the uncorrelated R₀ is the largest eigenvalue of the
degree-correlated next-generation matrix. -/
@[sa_reference "CategoricalComposition.R102e.1"]
def T : Prop :=
  ∀ (d : MixingPullbackData) (τ : ℝ), 0 < τ → τ ≤ 1 → 1 ≤ d.k1 → 1 ≤ d.k2 → d.r = 0 →
    Module.End.HasEigenvalue (Matrix.toLin' (ngm d τ)) (R0uncorr d τ) ∧
    ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (ngm d τ)) μ → μ ≤ R0uncorr d τ

/-- S1: the uncorrelated R₀ is an eigenvalue of the degree-correlated NGM at r = 0. -/
@[sa_shadow "CategoricalComposition.R102e.1" 1]
def S1 : Prop :=
  ∀ (d : MixingPullbackData) (τ : ℝ), 0 < τ → τ ≤ 1 → 1 ≤ d.k1 → 1 ≤ d.k2 → d.r = 0 →
    Module.End.HasEigenvalue (Matrix.toLin' (ngm d τ)) (R0uncorr d τ)

/-- S2: every eigenvalue of the degree-correlated NGM at r = 0 is at most the uncorrelated R₀. -/
@[sa_shadow "CategoricalComposition.R102e.1" 2]
def S2 : Prop :=
  ∀ (d : MixingPullbackData) (τ : ℝ), 0 < τ → τ ≤ 1 → 1 ≤ d.k1 → 1 ≤ d.k2 → d.r = 0 →
    ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (ngm d τ)) μ → μ ≤ R0uncorr d τ

@[sa_ref_forward "CategoricalComposition.R102e.1" 1]
theorem ref_fwd1 : T → S1 := fun t d τ h1 h2 h3 h4 h5 => (t d τ h1 h2 h3 h4 h5).1

@[sa_ref_forward "CategoricalComposition.R102e.1" 2]
theorem ref_fwd2 : T → S2 := fun t d τ h1 h2 h3 h4 h5 => (t d τ h1 h2 h3 h4 h5).2

@[sa_complete "CategoricalComposition.R102e.1"]
theorem complete (s1 : S1) (s2 : S2) : T :=
  fun d τ h1 h2 h3 h4 h5 => ⟨s1 d τ h1 h2 h3 h4 h5, s2 d τ h1 h2 h3 h4 h5⟩

end Alignment.Shadows.CategoricalComposition.R102e_1

/-! ## `CategoricalComposition.R100.monoidal` (re-authored blind)

Text: "The multiplex product of layers (Result 96) behaves like a monoidal product on susceptible
fractions and dimensions (informal: no category is defined). Its unit is the trivial network:
degree 0, no edges."

The monoidal behaviour is split into its laws: associativity and the two unit laws, once on
susceptible fractions (tensor = product `S₁·S₂`, Result 96) and once on dimensions (tensor = the
dimension of the multiplex product, `MultiplexProduct.dim`). The sentence in parentheses (no
category is defined) is a remark about the library and is not formalised. -/
namespace Alignment.Shadows.CategoricalComposition.R100_monoidal

/-- PGF of the trivial network, every node of degree 0: `ψ₀(x) = x⁰`. Its susceptible fraction
is `ψ₀(θ)`. -/
def trivialPGF (x : ℝ) : ℝ := x ^ (0 : ℕ)

-- AMBIGUITY: "on susceptible fractions" read as: for values in [0, 1] (fractions), with the
-- product S₁·S₂ of Result 96 as the tensor.
-- AMBIGUITY: "on ... dimensions": the product of two layers is a `MultiplexProduct`, not a layer,
-- so associativity is stated for layers `l₁₂`, `l₂₃` that stand for the inner products (same
-- dimension), and the unit is a layer of dimension 0 ("no edges": no equations), since a trivial
-- network cannot be an `EBCMLayer` (its mean degree would be 0).
@[sa_reference "CategoricalComposition.R100.monoidal"]
def T : Prop :=
  (∀ a b c : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → 0 ≤ c → c ≤ 1 → a * b * c = a * (b * c)) ∧
  (∀ θ S : ℝ, 0 ≤ S → S ≤ 1 → trivialPGF θ * S = S) ∧
  (∀ θ S : ℝ, 0 ≤ S → S ≤ 1 → S * trivialPGF θ = S) ∧
  (∀ l₁ l₂ l₃ l₁₂ l₂₃ : EBCMLayer, l₁₂.dim = (MultiplexProduct.mk l₁ l₂).dim →
      l₂₃.dim = (MultiplexProduct.mk l₂ l₃).dim →
      (MultiplexProduct.mk l₁₂ l₃).dim = (MultiplexProduct.mk l₁ l₂₃).dim) ∧
  (∀ l u : EBCMLayer, u.dim = 0 → (MultiplexProduct.mk u l).dim = l.dim) ∧
  (∀ l u : EBCMLayer, u.dim = 0 → (MultiplexProduct.mk l u).dim = l.dim)

/-- S1: the product of susceptible fractions is associative. -/
@[sa_shadow "CategoricalComposition.R100.monoidal" 1]
def S1 : Prop :=
  ∀ a b c : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → 0 ≤ c → c ≤ 1 → a * b * c = a * (b * c)

/-- S2: the trivial network's susceptible fraction `ψ₀(θ)` is a left unit. -/
@[sa_shadow "CategoricalComposition.R100.monoidal" 2]
def S2 : Prop := ∀ θ S : ℝ, 0 ≤ S → S ≤ 1 → trivialPGF θ * S = S

/-- S3: the trivial network's susceptible fraction `ψ₀(θ)` is a right unit. -/
@[sa_shadow "CategoricalComposition.R100.monoidal" 3]
def S3 : Prop := ∀ θ S : ℝ, 0 ≤ S → S ≤ 1 → S * trivialPGF θ = S

/-- S4: the multiplex product is associative on dimensions. -/
@[sa_shadow "CategoricalComposition.R100.monoidal" 4]
def S4 : Prop :=
  ∀ l₁ l₂ l₃ l₁₂ l₂₃ : EBCMLayer, l₁₂.dim = (MultiplexProduct.mk l₁ l₂).dim →
    l₂₃.dim = (MultiplexProduct.mk l₂ l₃).dim →
    (MultiplexProduct.mk l₁₂ l₃).dim = (MultiplexProduct.mk l₁ l₂₃).dim

/-- S5: a dimension-0 (edgeless) layer is a left unit on dimensions. -/
@[sa_shadow "CategoricalComposition.R100.monoidal" 5]
def S5 : Prop := ∀ l u : EBCMLayer, u.dim = 0 → (MultiplexProduct.mk u l).dim = l.dim

/-- S6: a dimension-0 (edgeless) layer is a right unit on dimensions. -/
@[sa_shadow "CategoricalComposition.R100.monoidal" 6]
def S6 : Prop := ∀ l u : EBCMLayer, u.dim = 0 → (MultiplexProduct.mk l u).dim = l.dim

@[sa_ref_forward "CategoricalComposition.R100.monoidal" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "CategoricalComposition.R100.monoidal" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "CategoricalComposition.R100.monoidal" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "CategoricalComposition.R100.monoidal" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2.1
@[sa_ref_forward "CategoricalComposition.R100.monoidal" 5] theorem ref_fwd5 : T → S5 :=
  fun t => t.2.2.2.2.1
@[sa_ref_forward "CategoricalComposition.R100.monoidal" 6] theorem ref_fwd6 : T → S6 :=
  fun t => t.2.2.2.2.2

@[sa_complete "CategoricalComposition.R100.monoidal"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) : T :=
  ⟨s1, s2, s3, s4, s5, s6⟩

end Alignment.Shadows.CategoricalComposition.R100_monoidal

/-! ## `CategoricalComposition.R100f.1` (re-authored blind)

Text: "**Result 100f.** The real-number identities that the pentagon and triangle identities would
reduce to hold (no associator or unitor is defined)."

For the product of susceptible fractions (Result 100), the pentagon reduces to the equality of
the two extreme bracketings of four factors, and the triangle to `(a·1)·b = a·(1·b)` with the unit
`1` (the trivial network's susceptible fraction). -/
namespace Alignment.Shadows.CategoricalComposition.R100f_1

-- AMBIGUITY: "the real-number identities that the pentagon ... would reduce to": read as the
-- equality of the two ends of the pentagon, ((a·b)·c)·d = a·(b·(c·d)), for all reals.
@[sa_reference "CategoricalComposition.R100f.1"]
def T : Prop :=
  (∀ a b c d : ℝ, a * b * c * d = a * (b * (c * d))) ∧ (∀ a b : ℝ, a * 1 * b = a * (1 * b))

/-- S1: pentagon identity for the product of reals. -/
@[sa_shadow "CategoricalComposition.R100f.1" 1]
def S1 : Prop := ∀ a b c d : ℝ, a * b * c * d = a * (b * (c * d))

/-- S2: triangle identity for the product of reals with unit 1. -/
@[sa_shadow "CategoricalComposition.R100f.1" 2]
def S2 : Prop := ∀ a b : ℝ, a * 1 * b = a * (1 * b)

@[sa_ref_forward "CategoricalComposition.R100f.1" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "CategoricalComposition.R100f.1" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "CategoricalComposition.R100f.1"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.CategoricalComposition.R100f_1

/-! ## `CategoricalComposition.R101e` (re-authored blind)

Text: "**Result 101e.** Monotonicity of R₀ in the excess degree: if e₁ ≤ e₂ and T ≥ 0, then
T·e₁ ≤ T·e₂." -/
namespace Alignment.Shadows.CategoricalComposition.R101e

-- AMBIGUITY: "Monotonicity of R₀ in the excess degree" is followed by the scalar inequality.
-- Both readings are required: the scalar inequality as written (S1), and the monotonicity of the
-- layer R₀ (`EBCMLayer.R0`) in the layer's excess degree at equal transmissibility (S2).
@[sa_reference "CategoricalComposition.R101e"]
def T : Prop :=
  (∀ τ e₁ e₂ : ℝ, e₁ ≤ e₂ → 0 ≤ τ → τ * e₁ ≤ τ * e₂) ∧
  (∀ l₁ l₂ : EBCMLayer, l₁.T = l₂.T → l₁.excessDegree ≤ l₂.excessDegree → l₁.R0 ≤ l₂.R0)

/-- S1: the scalar inequality `e₁ ≤ e₂ ∧ T ≥ 0 → T·e₁ ≤ T·e₂`. -/
@[sa_shadow "CategoricalComposition.R101e" 1]
def S1 : Prop := ∀ τ e₁ e₂ : ℝ, e₁ ≤ e₂ → 0 ≤ τ → τ * e₁ ≤ τ * e₂

/-- S2: the layer R₀ is monotone in the layer's excess degree at fixed transmissibility. -/
@[sa_shadow "CategoricalComposition.R101e" 2]
def S2 : Prop :=
  ∀ l₁ l₂ : EBCMLayer, l₁.T = l₂.T → l₁.excessDegree ≤ l₂.excessDegree → l₁.R0 ≤ l₂.R0

@[sa_ref_forward "CategoricalComposition.R101e" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "CategoricalComposition.R101e" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "CategoricalComposition.R101e"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.CategoricalComposition.R101e

/-! ## `CategoricalComposition.R102.terminal` (re-authored blind)

Text: "Neutral mixing (Q(l|k) = l·pₗ/⟨k⟩) is the special case r = 0 of the assortative family
below; no category of mixing matrices, and so no terminal object, is defined."

The assortative family is `Q(l|k) = r·δₗₖ + (1 − r)·qₗ` with the excess-degree probabilities
`qₗ` (`MixingPullbackData.q1`, `q2`); see the matrix `C` of DegreeCorrelation Result 82,
`C = [[k₁(r + (1−r)q₁), k₁(1−r)q₂], [k₂(1−r)q₁, k₂(r + (1−r)q₂)]]`. The neutral matrix is
written in primitive terms, `l·pₗ/⟨k⟩` with `⟨k⟩ = p₁k₁ + p₂k₂`. The remark that no category or
terminal object is defined is not formalised. -/
namespace Alignment.Shadows.CategoricalComposition.R102_terminal

/-- Mean degree `⟨k⟩ = p₁k₁ + p₂k₂` in primitive terms. -/
def meanK (d : MixingPullbackData) : ℝ := d.p1 * d.k1 + d.p2 * d.k2
/-- Assortative family `Q(1|1) = r + (1 − r)·q₁`. -/
def Q1of1 (d : MixingPullbackData) : ℝ := d.r + (1 - d.r) * d.q1
/-- Assortative family `Q(2|1) = (1 − r)·q₂`. -/
def Q2of1 (d : MixingPullbackData) : ℝ := (1 - d.r) * d.q2
/-- Assortative family `Q(1|2) = (1 − r)·q₁`. -/
def Q1of2 (d : MixingPullbackData) : ℝ := (1 - d.r) * d.q1
/-- Assortative family `Q(2|2) = r + (1 − r)·q₂`. -/
def Q2of2 (d : MixingPullbackData) : ℝ := d.r + (1 - d.r) * d.q2

-- AMBIGUITY: "the assortative family below" is not quoted; read as the standard family
-- r·δ + (1 − r)·q of DegreeCorrelation Result 82.
@[sa_reference "CategoricalComposition.R102.terminal"]
def T : Prop :=
  ∀ d : MixingPullbackData, d.r = 0 →
    Q1of1 d = d.k1 * d.p1 / meanK d ∧ Q2of1 d = d.k2 * d.p2 / meanK d ∧
    Q1of2 d = d.k1 * d.p1 / meanK d ∧ Q2of2 d = d.k2 * d.p2 / meanK d

/-- S1: at r = 0, `Q(1|1) = k₁p₁/⟨k⟩`. -/
@[sa_shadow "CategoricalComposition.R102.terminal" 1]
def S1 : Prop := ∀ d : MixingPullbackData, d.r = 0 → Q1of1 d = d.k1 * d.p1 / meanK d
/-- S2: at r = 0, `Q(2|1) = k₂p₂/⟨k⟩`. -/
@[sa_shadow "CategoricalComposition.R102.terminal" 2]
def S2 : Prop := ∀ d : MixingPullbackData, d.r = 0 → Q2of1 d = d.k2 * d.p2 / meanK d
/-- S3: at r = 0, `Q(1|2) = k₁p₁/⟨k⟩`. -/
@[sa_shadow "CategoricalComposition.R102.terminal" 3]
def S3 : Prop := ∀ d : MixingPullbackData, d.r = 0 → Q1of2 d = d.k1 * d.p1 / meanK d
/-- S4: at r = 0, `Q(2|2) = k₂p₂/⟨k⟩`. -/
@[sa_shadow "CategoricalComposition.R102.terminal" 4]
def S4 : Prop := ∀ d : MixingPullbackData, d.r = 0 → Q2of2 d = d.k2 * d.p2 / meanK d

@[sa_ref_forward "CategoricalComposition.R102.terminal" 1] theorem ref_fwd1 : T → S1 :=
  fun t d h => (t d h).1
@[sa_ref_forward "CategoricalComposition.R102.terminal" 2] theorem ref_fwd2 : T → S2 :=
  fun t d h => (t d h).2.1
@[sa_ref_forward "CategoricalComposition.R102.terminal" 3] theorem ref_fwd3 : T → S3 :=
  fun t d h => (t d h).2.2.1
@[sa_ref_forward "CategoricalComposition.R102.terminal" 4] theorem ref_fwd4 : T → S4 :=
  fun t d h => (t d h).2.2.2
@[sa_complete "CategoricalComposition.R102.terminal"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T :=
  fun d h => ⟨s1 d h, s2 d h, s3 d h, s4 d h⟩

end Alignment.Shadows.CategoricalComposition.R102_terminal

/-! ## `CategoricalComposition.R102a.1` (re-authored blind)

Text: "**Result 102a.** Neutral mixing: when r=0, the mixing matrix Q(l|k) = q_l is independent
of k."

The assortative family is written in primitive terms, `Q(l|k) = r·δₗₖ + (1 − r)·lpₗ/⟨k⟩`; the
claim is that at r = 0 every entry equals the excess-degree probability `q_l`
(`MixingPullbackData.q1`, `q2`), for both source degrees k (hence independent of k). -/
namespace Alignment.Shadows.CategoricalComposition.R102a_1

/-- Mean degree `⟨k⟩ = p₁k₁ + p₂k₂`. -/
def meanK (d : MixingPullbackData) : ℝ := d.p1 * d.k1 + d.p2 * d.k2
/-- `Q(1|1) = r + (1 − r)·k₁p₁/⟨k⟩`. -/
def Q1of1 (d : MixingPullbackData) : ℝ := d.r + (1 - d.r) * (d.k1 * d.p1 / meanK d)
/-- `Q(2|1) = (1 − r)·k₂p₂/⟨k⟩`. -/
def Q2of1 (d : MixingPullbackData) : ℝ := (1 - d.r) * (d.k2 * d.p2 / meanK d)
/-- `Q(1|2) = (1 − r)·k₁p₁/⟨k⟩`. -/
def Q1of2 (d : MixingPullbackData) : ℝ := (1 - d.r) * (d.k1 * d.p1 / meanK d)
/-- `Q(2|2) = r + (1 − r)·k₂p₂/⟨k⟩`. -/
def Q2of2 (d : MixingPullbackData) : ℝ := d.r + (1 - d.r) * (d.k2 * d.p2 / meanK d)

@[sa_reference "CategoricalComposition.R102a.1"]
def T : Prop :=
  ∀ d : MixingPullbackData, d.r = 0 →
    Q1of1 d = d.q1 ∧ Q1of2 d = d.q1 ∧ Q2of1 d = d.q2 ∧ Q2of2 d = d.q2

/-- S1: at r = 0, `Q(1|1) = q₁`. -/
@[sa_shadow "CategoricalComposition.R102a.1" 1]
def S1 : Prop := ∀ d : MixingPullbackData, d.r = 0 → Q1of1 d = d.q1
/-- S2: at r = 0, `Q(1|2) = q₁` (same as from source degree k₁). -/
@[sa_shadow "CategoricalComposition.R102a.1" 2]
def S2 : Prop := ∀ d : MixingPullbackData, d.r = 0 → Q1of2 d = d.q1
/-- S3: at r = 0, `Q(2|1) = q₂`. -/
@[sa_shadow "CategoricalComposition.R102a.1" 3]
def S3 : Prop := ∀ d : MixingPullbackData, d.r = 0 → Q2of1 d = d.q2
/-- S4: at r = 0, `Q(2|2) = q₂` (same as from source degree k₁). -/
@[sa_shadow "CategoricalComposition.R102a.1" 4]
def S4 : Prop := ∀ d : MixingPullbackData, d.r = 0 → Q2of2 d = d.q2

@[sa_ref_forward "CategoricalComposition.R102a.1" 1] theorem ref_fwd1 : T → S1 :=
  fun t d h => (t d h).1
@[sa_ref_forward "CategoricalComposition.R102a.1" 2] theorem ref_fwd2 : T → S2 :=
  fun t d h => (t d h).2.1
@[sa_ref_forward "CategoricalComposition.R102a.1" 3] theorem ref_fwd3 : T → S3 :=
  fun t d h => (t d h).2.2.1
@[sa_ref_forward "CategoricalComposition.R102a.1" 4] theorem ref_fwd4 : T → S4 :=
  fun t d h => (t d h).2.2.2
@[sa_complete "CategoricalComposition.R102a.1"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T :=
  fun d h => ⟨s1 d h, s2 d h, s3 d h, s4 d h⟩

end Alignment.Shadows.CategoricalComposition.R102a_1

/-! ## `CategoricalComposition.R102c.1` (re-authored blind)

Text: "**Result 102c.** The r = 0 specialisation of the assortative mixing matrix."

Read as: at r = 0 the assortative mixing matrix `C_{kl} = k·Q(l|k)` (Result 82 form, written in
primitive terms with `lpₗ/⟨k⟩`) is the neutral matrix `C_{kl} = k·q_l`, with `q_l` the
excess-degree probabilities `MixingPullbackData.q1`, `q2`. -/
namespace Alignment.Shadows.CategoricalComposition.R102c_1

/-- Mean degree `⟨k⟩ = p₁k₁ + p₂k₂`. -/
def meanK (d : MixingPullbackData) : ℝ := d.p1 * d.k1 + d.p2 * d.k2
/-- Assortative mixing matrix `C = [[k₁(r + (1−r)q₁), k₁(1−r)q₂], [k₂(1−r)q₁, k₂(r + (1−r)q₂)]]`
with `q_l = l·p_l/⟨k⟩` in primitive terms. -/
def Cfam (d : MixingPullbackData) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![d.k1 * (d.r + (1 - d.r) * (d.k1 * d.p1 / meanK d)), d.k1 * (1 - d.r) * (d.k2 * d.p2 / meanK d);
     d.k2 * (1 - d.r) * (d.k1 * d.p1 / meanK d), d.k2 * (d.r + (1 - d.r) * (d.k2 * d.p2 / meanK d))]

-- AMBIGUITY: the text is a heading; "the r = 0 specialisation" read as the statement that the
-- r = 0 member of the family is the neutral matrix k·q_l.
@[sa_reference "CategoricalComposition.R102c.1"]
def T : Prop :=
  ∀ d : MixingPullbackData, d.r = 0 →
    Cfam d 0 0 = d.k1 * d.q1 ∧ Cfam d 0 1 = d.k1 * d.q2 ∧
    Cfam d 1 0 = d.k2 * d.q1 ∧ Cfam d 1 1 = d.k2 * d.q2

/-- S1: at r = 0, `C₁₁ = k₁q₁`. -/
@[sa_shadow "CategoricalComposition.R102c.1" 1]
def S1 : Prop := ∀ d : MixingPullbackData, d.r = 0 → Cfam d 0 0 = d.k1 * d.q1
/-- S2: at r = 0, `C₁₂ = k₁q₂`. -/
@[sa_shadow "CategoricalComposition.R102c.1" 2]
def S2 : Prop := ∀ d : MixingPullbackData, d.r = 0 → Cfam d 0 1 = d.k1 * d.q2
/-- S3: at r = 0, `C₂₁ = k₂q₁`. -/
@[sa_shadow "CategoricalComposition.R102c.1" 3]
def S3 : Prop := ∀ d : MixingPullbackData, d.r = 0 → Cfam d 1 0 = d.k2 * d.q1
/-- S4: at r = 0, `C₂₂ = k₂q₂`. -/
@[sa_shadow "CategoricalComposition.R102c.1" 4]
def S4 : Prop := ∀ d : MixingPullbackData, d.r = 0 → Cfam d 1 1 = d.k2 * d.q2

@[sa_ref_forward "CategoricalComposition.R102c.1" 1] theorem ref_fwd1 : T → S1 :=
  fun t d h => (t d h).1
@[sa_ref_forward "CategoricalComposition.R102c.1" 2] theorem ref_fwd2 : T → S2 :=
  fun t d h => (t d h).2.1
@[sa_ref_forward "CategoricalComposition.R102c.1" 3] theorem ref_fwd3 : T → S3 :=
  fun t d h => (t d h).2.2.1
@[sa_ref_forward "CategoricalComposition.R102c.1" 4] theorem ref_fwd4 : T → S4 :=
  fun t d h => (t d h).2.2.2
@[sa_complete "CategoricalComposition.R102c.1"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T :=
  fun d h => ⟨s1 d h, s2 d h, s3 d h, s4 d h⟩

end Alignment.Shadows.CategoricalComposition.R102c_1

/-! ## `CategoricalComposition.R102d.1` (re-authored blind)

Text: "**Result 102d.** The neutral mixing matrix is rank-1 (det = 0): it factors through the
degree distribution."

The neutral mixing matrix is `C_{kl} = k·q_l` with the excess-degree probabilities `q_l`
(`MixingPullbackData.q1`, `q2`). "Factors through the degree distribution" is read as the outer
product `C = (k₁, k₂)ᵀ · (k₁p₁/⟨k⟩, k₂p₂/⟨k⟩)` of the degree vector and the edge-end degree
distribution. -/
namespace Alignment.Shadows.CategoricalComposition.R102d_1

/-- Mean degree `⟨k⟩ = p₁k₁ + p₂k₂`. -/
def meanK (d : MixingPullbackData) : ℝ := d.p1 * d.k1 + d.p2 * d.k2
/-- Neutral mixing matrix `C_{kl} = k·q_l`. -/
def Cneutral (d : MixingPullbackData) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![d.k1 * d.q1, d.k1 * d.q2; d.k2 * d.q1, d.k2 * d.q2]

@[sa_reference "CategoricalComposition.R102d.1"]
def T : Prop :=
  ∀ d : MixingPullbackData,
    (Cneutral d).rank = 1 ∧ (Cneutral d).det = 0 ∧
    Cneutral d = Matrix.vecMulVec ![d.k1, d.k2] ![d.k1 * d.p1 / meanK d, d.k2 * d.p2 / meanK d]

/-- S1: the neutral mixing matrix has rank one. -/
@[sa_shadow "CategoricalComposition.R102d.1" 1]
def S1 : Prop := ∀ d : MixingPullbackData, (Cneutral d).rank = 1
/-- S2: its determinant is zero. -/
@[sa_shadow "CategoricalComposition.R102d.1" 2]
def S2 : Prop := ∀ d : MixingPullbackData, (Cneutral d).det = 0
/-- S3: it is the outer product of the degree vector and the edge-end degree distribution. -/
@[sa_shadow "CategoricalComposition.R102d.1" 3]
def S3 : Prop :=
  ∀ d : MixingPullbackData,
    Cneutral d = Matrix.vecMulVec ![d.k1, d.k2] ![d.k1 * d.p1 / meanK d, d.k2 * d.p2 / meanK d]

@[sa_ref_forward "CategoricalComposition.R102d.1" 1] theorem ref_fwd1 : T → S1 :=
  fun t d => (t d).1
@[sa_ref_forward "CategoricalComposition.R102d.1" 2] theorem ref_fwd2 : T → S2 :=
  fun t d => (t d).2.1
@[sa_ref_forward "CategoricalComposition.R102d.1" 3] theorem ref_fwd3 : T → S3 :=
  fun t d => (t d).2.2
@[sa_complete "CategoricalComposition.R102d.1"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := fun d => ⟨s1 d, s2 d, s3 d⟩

end Alignment.Shadows.CategoricalComposition.R102d_1

/-! ## `CategoricalComposition.R102e.2` (re-authored blind)

Text: "For r=0, the largest eigenvalue of C = k·Q equals ⟨k²⟩/⟨k⟩, which is one more than the
largest eigenvalue ⟨k²-k⟩/⟨k⟩ of the next-generation matrix K = (k-1)·Q; R₀ = T·⟨k²-k⟩/⟨k⟩ is
the standard uncorrelated formula (DegreeCorrelation `neutral_traceK`). The Lean statement below
is the field identity T·a/b = T·(a/b), with a/b = ⟨k²⟩/⟨k⟩."

`C_{kl} = k·Q(l|k)` and `K_{kl} = (k−1)·Q(l|k)`, with the assortative family
`Q(l|k) = r·δₗₖ + (1 − r)·q_l` and the excess-degree probabilities `q_l` (`MixingPullbackData.q1`,
`q2`). Moments of the two-point degree distribution are written in primitive terms. "Largest
eigenvalue" = a real eigenvalue of `Matrix.toLin'` that is ≥ every real eigenvalue. -/
namespace Alignment.Shadows.CategoricalComposition.R102e_2

/-- `⟨k⟩ = p₁k₁ + p₂k₂`. -/
def m1 (d : MixingPullbackData) : ℝ := d.p1 * d.k1 + d.p2 * d.k2
/-- `⟨k²⟩ = p₁k₁² + p₂k₂²`. -/
def m2 (d : MixingPullbackData) : ℝ := d.p1 * d.k1 ^ 2 + d.p2 * d.k2 ^ 2
/-- `⟨k² − k⟩ = p₁k₁(k₁−1) + p₂k₂(k₂−1)`. -/
def mf (d : MixingPullbackData) : ℝ := d.p1 * (d.k1 ^ 2 - d.k1) + d.p2 * (d.k2 ^ 2 - d.k2)

/-- Mixing matrix `C = k·Q` of the assortative family. -/
def Cmat (d : MixingPullbackData) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![d.k1 * (d.r + (1 - d.r) * d.q1), d.k1 * ((1 - d.r) * d.q2);
     d.k2 * ((1 - d.r) * d.q1), d.k2 * (d.r + (1 - d.r) * d.q2)]
/-- Next-generation matrix `K = (k−1)·Q` of the assortative family. -/
def Kmat (d : MixingPullbackData) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(d.k1 - 1) * (d.r + (1 - d.r) * d.q1), (d.k1 - 1) * ((1 - d.r) * d.q2);
     (d.k2 - 1) * ((1 - d.r) * d.q1), (d.k2 - 1) * (d.r + (1 - d.r) * d.q2)]

/-- `μ` is the largest real eigenvalue of `A`. -/
def IsLargestEig (A : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℝ) : Prop :=
  Module.End.HasEigenvalue (Matrix.toLin' A) μ ∧
    ∀ ν : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) ν → ν ≤ μ

-- AMBIGUITY: degrees are read as at least 1 for the statements about K (S2, S3); for degrees in
-- (0, 1) the trace ⟨k²−k⟩/⟨k⟩ of the rank-one K is negative and its largest eigenvalue is 0.
-- AMBIGUITY: "R₀ = T·⟨k²-k⟩/⟨k⟩ is the standard uncorrelated formula" read as: it is the layer
-- R₀ (`EBCMLayer.R0`) of an uncorrelated layer with the same first and second factorial moments
-- (S4). "The Lean statement below is the field identity ..." is kept as S5 with a/b = ⟨k²⟩/⟨k⟩.
@[sa_reference "CategoricalComposition.R102e.2"]
def T : Prop :=
  (∀ d : MixingPullbackData, d.r = 0 → IsLargestEig (Cmat d) (m2 d / m1 d)) ∧
  (∀ d : MixingPullbackData, d.r = 0 → 1 ≤ d.k1 → 1 ≤ d.k2 →
      IsLargestEig (Kmat d) (mf d / m1 d)) ∧
  (∀ (d : MixingPullbackData) (μ ν : ℝ), d.r = 0 → 1 ≤ d.k1 → 1 ≤ d.k2 →
      IsLargestEig (Cmat d) μ → IsLargestEig (Kmat d) ν → μ = ν + 1) ∧
  (∀ (d : MixingPullbackData) (l : EBCMLayer), l.mean = m1 d → l.secondFactorial = mf d →
      l.R0 = l.T * (mf d / m1 d)) ∧
  (∀ (d : MixingPullbackData) (τ : ℝ), τ * m2 d / m1 d = τ * (m2 d / m1 d))

/-- S1: at r = 0 the largest eigenvalue of `C` is `⟨k²⟩/⟨k⟩`. -/
@[sa_shadow "CategoricalComposition.R102e.2" 1]
def S1 : Prop := ∀ d : MixingPullbackData, d.r = 0 → IsLargestEig (Cmat d) (m2 d / m1 d)
/-- S2: at r = 0 the largest eigenvalue of `K` is `⟨k²−k⟩/⟨k⟩`. -/
@[sa_shadow "CategoricalComposition.R102e.2" 2]
def S2 : Prop :=
  ∀ d : MixingPullbackData, d.r = 0 → 1 ≤ d.k1 → 1 ≤ d.k2 → IsLargestEig (Kmat d) (mf d / m1 d)
/-- S3: at r = 0 the largest eigenvalue of `C` is one more than that of `K`. -/
@[sa_shadow "CategoricalComposition.R102e.2" 3]
def S3 : Prop :=
  ∀ (d : MixingPullbackData) (μ ν : ℝ), d.r = 0 → 1 ≤ d.k1 → 1 ≤ d.k2 →
    IsLargestEig (Cmat d) μ → IsLargestEig (Kmat d) ν → μ = ν + 1
/-- S4: `T·⟨k²−k⟩/⟨k⟩` is the layer R₀ of an uncorrelated layer with these moments. -/
@[sa_shadow "CategoricalComposition.R102e.2" 4]
def S4 : Prop :=
  ∀ (d : MixingPullbackData) (l : EBCMLayer), l.mean = m1 d → l.secondFactorial = mf d →
    l.R0 = l.T * (mf d / m1 d)
/-- S5: the field identity `T·a/b = T·(a/b)` with `a/b = ⟨k²⟩/⟨k⟩`. -/
@[sa_shadow "CategoricalComposition.R102e.2" 5]
def S5 : Prop := ∀ (d : MixingPullbackData) (τ : ℝ), τ * m2 d / m1 d = τ * (m2 d / m1 d)

@[sa_ref_forward "CategoricalComposition.R102e.2" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "CategoricalComposition.R102e.2" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "CategoricalComposition.R102e.2" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "CategoricalComposition.R102e.2" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2.1
@[sa_ref_forward "CategoricalComposition.R102e.2" 5] theorem ref_fwd5 : T → S5 :=
  fun t => t.2.2.2.2
@[sa_complete "CategoricalComposition.R102e.2"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.CategoricalComposition.R102e_2

/-! ## `CategoricalComposition.R96b` (re-authored blind)

Text: "**Result 96b.** The product dimension is defined as the sum of the layer dimensions; the
compact multiplex system needs fewer ODEs (one θ-equation per layer plus one recovery equation,
`compactMultiplexDim`)." -/
namespace Alignment.Shadows.CategoricalComposition.R96b

-- AMBIGUITY: "needs fewer ODEs": fewer than the product dimension of two layers whose own
-- systems have at least two equations each (one θ-equation and one recovery equation per layer).
@[sa_reference "CategoricalComposition.R96b"]
def T : Prop :=
  (∀ p : MultiplexProduct, p.dim = p.layer1.dim + p.layer2.dim) ∧
  (∀ n : ℕ, compactMultiplexDim n = n + 1) ∧
  (∀ p : MultiplexProduct, 2 ≤ p.layer1.dim → 2 ≤ p.layer2.dim → compactMultiplexDim 2 < p.dim)

/-- S1: the product dimension is the sum of the layer dimensions. -/
@[sa_shadow "CategoricalComposition.R96b" 1]
def S1 : Prop := ∀ p : MultiplexProduct, p.dim = p.layer1.dim + p.layer2.dim
/-- S2: the compact system has one θ-equation per layer plus one recovery equation. -/
@[sa_shadow "CategoricalComposition.R96b" 2]
def S2 : Prop := ∀ n : ℕ, compactMultiplexDim n = n + 1
/-- S3: the compact two-layer system has fewer equations than the product system. -/
@[sa_shadow "CategoricalComposition.R96b" 3]
def S3 : Prop :=
  ∀ p : MultiplexProduct, 2 ≤ p.layer1.dim → 2 ≤ p.layer2.dim → compactMultiplexDim 2 < p.dim

@[sa_ref_forward "CategoricalComposition.R96b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "CategoricalComposition.R96b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "CategoricalComposition.R96b" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "CategoricalComposition.R96b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.CategoricalComposition.R96b

/-! ## `CategoricalComposition.R96c` (re-authored blind)

Text: "**Result 96c.** The sum T₁e₁ + T₂e₂ of the per-layer R₀ values; it matches the former
compact implementation in `src/multiplex.jl`. It is not the R₀ of independent multiplex layers,
which is ρ(K) with K = [[T₁e₁, T₁⟨k₁⟩], [T₂⟨k₂⟩, T₂e₂]] and eᵢ = ψᵢ''(1)/ψᵢ'(1)
(`MultiplexProduct.K11` …). The sum T₁e₁ + T₂e₂ equals ρ(K) iff det K = 0, i.e. e₁e₂ = ⟨k₁⟩⟨k₂⟩,
for example for two Poisson layers; it underestimates ρ(K) when e₁e₂ < ⟨k₁⟩⟨k₂⟩. Two 3-regular
layers with T = 6/25 give sum 24/25 but ρ(K) = 6/5 (`multiplex_R0_sum_ne_spectral`)."

"The sum" is `MultiplexProduct.R0_sum`. `K` and `eᵢ` are written in primitive terms. ρ(K) is the
largest real eigenvalue (K has positive entries, so this is its spectral radius). A Poisson layer
has `ψ''(1) = ⟨k⟩²`; a 3-regular layer has `⟨k⟩ = 3`, `ψ''(1) = 3·2 = 6`. The match with the Julia
source `src/multiplex.jl` is not formalised. -/
namespace Alignment.Shadows.CategoricalComposition.R96c

/-- `eᵢ = ψᵢ''(1)/ψᵢ'(1)` for a layer, in primitive terms. -/
def e (l : EBCMLayer) : ℝ := l.secondFactorial / l.mean
/-- The multiplex next-generation matrix `K = [[T₁e₁, T₁⟨k₁⟩], [T₂⟨k₂⟩, T₂e₂]]`. -/
def Kmp (p : MultiplexProduct) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.layer1.T * e p.layer1, p.layer1.T * p.layer1.mean;
     p.layer2.T * p.layer2.mean, p.layer2.T * e p.layer2]
/-- `μ` is the largest real eigenvalue of `A` (= ρ(A) for the positive matrices here). -/
def IsRho (A : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℝ) : Prop :=
  Module.End.HasEigenvalue (Matrix.toLin' A) μ ∧
    ∀ ν : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) ν → ν ≤ μ
/-- A 3-regular layer with `T = 6/25`. -/
def threeReg (l : EBCMLayer) : Prop := l.mean = 3 ∧ l.secondFactorial = 6 ∧ l.T = 6 / 25

@[sa_reference "CategoricalComposition.R96c"]
def T : Prop :=
  (∀ p : MultiplexProduct, p.R0_sum = p.layer1.T * e p.layer1 + p.layer2.T * e p.layer2) ∧
  (∀ p : MultiplexProduct, p.R0_sum = p.layer1.R0 + p.layer2.R0) ∧
  (∃ (p : MultiplexProduct) (μ : ℝ), IsRho (Kmp p) μ ∧ p.R0_sum ≠ μ) ∧
  (∀ (p : MultiplexProduct) (μ : ℝ), IsRho (Kmp p) μ → (Kmp p).det = 0 → p.R0_sum = μ) ∧
  (∀ (p : MultiplexProduct) (μ : ℝ), IsRho (Kmp p) μ → p.R0_sum = μ → (Kmp p).det = 0) ∧
  (∀ p : MultiplexProduct, (Kmp p).det = 0 →
      e p.layer1 * e p.layer2 = p.layer1.mean * p.layer2.mean) ∧
  (∀ p : MultiplexProduct, e p.layer1 * e p.layer2 = p.layer1.mean * p.layer2.mean →
      (Kmp p).det = 0) ∧
  (∀ (p : MultiplexProduct) (μ : ℝ), p.layer1.secondFactorial = p.layer1.mean ^ 2 →
      p.layer2.secondFactorial = p.layer2.mean ^ 2 → IsRho (Kmp p) μ → p.R0_sum = μ) ∧
  (∀ (p : MultiplexProduct) (μ : ℝ), e p.layer1 * e p.layer2 < p.layer1.mean * p.layer2.mean →
      IsRho (Kmp p) μ → p.R0_sum < μ) ∧
  (∀ p : MultiplexProduct, threeReg p.layer1 → threeReg p.layer2 → p.R0_sum = 24 / 25) ∧
  (∀ p : MultiplexProduct, threeReg p.layer1 → threeReg p.layer2 → IsRho (Kmp p) (6 / 5))

/-- S1: the sum is `T₁e₁ + T₂e₂`. -/
@[sa_shadow "CategoricalComposition.R96c" 1]
def S1 : Prop :=
  ∀ p : MultiplexProduct, p.R0_sum = p.layer1.T * e p.layer1 + p.layer2.T * e p.layer2
/-- S2: the sum is the sum of the per-layer R₀ values. -/
@[sa_shadow "CategoricalComposition.R96c" 2]
def S2 : Prop := ∀ p : MultiplexProduct, p.R0_sum = p.layer1.R0 + p.layer2.R0
/-- S3: the sum is not, in general, ρ(K). -/
@[sa_shadow "CategoricalComposition.R96c" 3]
def S3 : Prop := ∃ (p : MultiplexProduct) (μ : ℝ), IsRho (Kmp p) μ ∧ p.R0_sum ≠ μ
/-- S4: det K = 0 implies sum = ρ(K). -/
@[sa_shadow "CategoricalComposition.R96c" 4]
def S4 : Prop :=
  ∀ (p : MultiplexProduct) (μ : ℝ), IsRho (Kmp p) μ → (Kmp p).det = 0 → p.R0_sum = μ
/-- S5: sum = ρ(K) implies det K = 0. -/
@[sa_shadow "CategoricalComposition.R96c" 5]
def S5 : Prop :=
  ∀ (p : MultiplexProduct) (μ : ℝ), IsRho (Kmp p) μ → p.R0_sum = μ → (Kmp p).det = 0
/-- S6: det K = 0 implies e₁e₂ = ⟨k₁⟩⟨k₂⟩. -/
@[sa_shadow "CategoricalComposition.R96c" 6]
def S6 : Prop :=
  ∀ p : MultiplexProduct, (Kmp p).det = 0 →
    e p.layer1 * e p.layer2 = p.layer1.mean * p.layer2.mean
/-- S7: e₁e₂ = ⟨k₁⟩⟨k₂⟩ implies det K = 0. -/
@[sa_shadow "CategoricalComposition.R96c" 7]
def S7 : Prop :=
  ∀ p : MultiplexProduct, e p.layer1 * e p.layer2 = p.layer1.mean * p.layer2.mean →
    (Kmp p).det = 0
/-- S8: for two Poisson layers the sum equals ρ(K). -/
@[sa_shadow "CategoricalComposition.R96c" 8]
def S8 : Prop :=
  ∀ (p : MultiplexProduct) (μ : ℝ), p.layer1.secondFactorial = p.layer1.mean ^ 2 →
    p.layer2.secondFactorial = p.layer2.mean ^ 2 → IsRho (Kmp p) μ → p.R0_sum = μ
/-- S9: e₁e₂ < ⟨k₁⟩⟨k₂⟩ implies sum < ρ(K). -/
@[sa_shadow "CategoricalComposition.R96c" 9]
def S9 : Prop :=
  ∀ (p : MultiplexProduct) (μ : ℝ), e p.layer1 * e p.layer2 < p.layer1.mean * p.layer2.mean →
    IsRho (Kmp p) μ → p.R0_sum < μ
/-- S10: two 3-regular layers with T = 6/25 have sum 24/25. -/
@[sa_shadow "CategoricalComposition.R96c" 10]
def S10 : Prop :=
  ∀ p : MultiplexProduct, threeReg p.layer1 → threeReg p.layer2 → p.R0_sum = 24 / 25
/-- S11: two 3-regular layers with T = 6/25 have ρ(K) = 6/5. -/
@[sa_shadow "CategoricalComposition.R96c" 11]
def S11 : Prop :=
  ∀ p : MultiplexProduct, threeReg p.layer1 → threeReg p.layer2 → IsRho (Kmp p) (6 / 5)

@[sa_ref_forward "CategoricalComposition.R96c" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "CategoricalComposition.R96c" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "CategoricalComposition.R96c" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "CategoricalComposition.R96c" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2.1
@[sa_ref_forward "CategoricalComposition.R96c" 5] theorem ref_fwd5 : T → S5 :=
  fun t => t.2.2.2.2.1
@[sa_ref_forward "CategoricalComposition.R96c" 6] theorem ref_fwd6 : T → S6 :=
  fun t => t.2.2.2.2.2.1
@[sa_ref_forward "CategoricalComposition.R96c" 7] theorem ref_fwd7 : T → S7 :=
  fun t => t.2.2.2.2.2.2.1
@[sa_ref_forward "CategoricalComposition.R96c" 8] theorem ref_fwd8 : T → S8 :=
  fun t => t.2.2.2.2.2.2.2.1
@[sa_ref_forward "CategoricalComposition.R96c" 9] theorem ref_fwd9 : T → S9 :=
  fun t => t.2.2.2.2.2.2.2.2.1
@[sa_ref_forward "CategoricalComposition.R96c" 10] theorem ref_fwd10 : T → S10 :=
  fun t => t.2.2.2.2.2.2.2.2.2.1
@[sa_ref_forward "CategoricalComposition.R96c" 11] theorem ref_fwd11 : T → S11 :=
  fun t => t.2.2.2.2.2.2.2.2.2.2
@[sa_complete "CategoricalComposition.R96c"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) (s6 : S6) (s7 : S7) (s8 : S8)
    (s9 : S9) (s10 : S10) (s11 : S11) : T :=
  ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩

end Alignment.Shadows.CategoricalComposition.R96c

/-! ## `CategoricalComposition.R96f` (re-authored blind)

Text: "**Result 96f.** If the summed multiplex contribution is at most one, the sum is at most one.
**Tautological Lean statement:** its hypothesis is its conclusion. The multiplex product itself
need not be subcritical: for two 3-regular layers with T = 6/25 the sum is 24/25 but
R₀ = ρ(K) = 6/5 (`multiplex_R0_sum_ne_spectral`)."

"The summed multiplex contribution" is `T₁e₁ + T₂e₂` in primitive terms, "the sum" is
`MultiplexProduct.R0_sum`, `K = [[T₁e₁, T₁⟨k₁⟩], [T₂⟨k₂⟩, T₂e₂]]` (Result 96c) and ρ(K) its largest
real eigenvalue. The remark about the Lean statement is not formalised. -/
namespace Alignment.Shadows.CategoricalComposition.R96f

/-- `eᵢ = ψᵢ''(1)/ψᵢ'(1)`. -/
def e (l : EBCMLayer) : ℝ := l.secondFactorial / l.mean
/-- The multiplex next-generation matrix. -/
def Kmp (p : MultiplexProduct) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.layer1.T * e p.layer1, p.layer1.T * p.layer1.mean;
     p.layer2.T * p.layer2.mean, p.layer2.T * e p.layer2]
/-- `μ` is the largest real eigenvalue of `A`. -/
def IsRho (A : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℝ) : Prop :=
  Module.End.HasEigenvalue (Matrix.toLin' A) μ ∧
    ∀ ν : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) ν → ν ≤ μ
/-- A 3-regular layer with `T = 6/25`. -/
def threeReg (l : EBCMLayer) : Prop := l.mean = 3 ∧ l.secondFactorial = 6 ∧ l.T = 6 / 25

@[sa_reference "CategoricalComposition.R96f"]
def T : Prop :=
  (∀ p : MultiplexProduct,
      p.layer1.T * e p.layer1 + p.layer2.T * e p.layer2 ≤ 1 → p.R0_sum ≤ 1) ∧
  (∃ (p : MultiplexProduct) (μ : ℝ), p.R0_sum ≤ 1 ∧ IsRho (Kmp p) μ ∧ 1 < μ) ∧
  (∀ p : MultiplexProduct, threeReg p.layer1 → threeReg p.layer2 → p.R0_sum = 24 / 25) ∧
  (∀ p : MultiplexProduct, threeReg p.layer1 → threeReg p.layer2 → IsRho (Kmp p) (6 / 5))

/-- S1: a summed contribution at most one gives a sum at most one. -/
@[sa_shadow "CategoricalComposition.R96f" 1]
def S1 : Prop :=
  ∀ p : MultiplexProduct, p.layer1.T * e p.layer1 + p.layer2.T * e p.layer2 ≤ 1 → p.R0_sum ≤ 1
/-- S2: the multiplex product need not be subcritical when the sum is at most one. -/
@[sa_shadow "CategoricalComposition.R96f" 2]
def S2 : Prop := ∃ (p : MultiplexProduct) (μ : ℝ), p.R0_sum ≤ 1 ∧ IsRho (Kmp p) μ ∧ 1 < μ
/-- S3: the 3-regular example has sum 24/25. -/
@[sa_shadow "CategoricalComposition.R96f" 3]
def S3 : Prop :=
  ∀ p : MultiplexProduct, threeReg p.layer1 → threeReg p.layer2 → p.R0_sum = 24 / 25
/-- S4: the 3-regular example has ρ(K) = 6/5. -/
@[sa_shadow "CategoricalComposition.R96f" 4]
def S4 : Prop :=
  ∀ p : MultiplexProduct, threeReg p.layer1 → threeReg p.layer2 → IsRho (Kmp p) (6 / 5)

@[sa_ref_forward "CategoricalComposition.R96f" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "CategoricalComposition.R96f" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "CategoricalComposition.R96f" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "CategoricalComposition.R96f" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "CategoricalComposition.R96f"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.CategoricalComposition.R96f

/-! ## `CategoricalComposition.R97a.2` (re-authored blind)

Text: "It is a convex combination of the type susceptible fractions, not a coproduct injection."

"It" is the overall susceptible fraction `StratifiedData.S_total` (Result 97a). The negative
remark (not a coproduct injection) refers to categorical structure that is not defined and is not
formalised. -/
namespace Alignment.Shadows.CategoricalComposition.R97a_2

@[sa_reference "CategoricalComposition.R97a.2"]
def T : Prop :=
  ∀ d : StratifiedData, ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧
    ∀ S₁ S₂ : ℝ, d.S_total S₁ S₂ = w * S₁ + (1 - w) * S₂

/-- S1: the overall susceptible fraction is a convex combination of the type fractions. -/
@[sa_shadow "CategoricalComposition.R97a.2" 1]
def S1 : Prop :=
  ∀ d : StratifiedData, ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧
    ∀ S₁ S₂ : ℝ, d.S_total S₁ S₂ = w * S₁ + (1 - w) * S₂

@[sa_ref_forward "CategoricalComposition.R97a.2" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "CategoricalComposition.R97a.2"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R97a_2

/-! ## `CategoricalComposition.R98.keyProperty` (re-authored blind)

Text: "Key property: η_n preserves the PGF and the mean infectious period.
T_n = 1 − (nγ/(β+nγ))^n increases with n towards 1 − exp(−β/γ), so R₀ and the final size change
(`stages_change_transmissibility`)."

`StagesNatTransData` carries β, γ, n and the transmissibilities `T_exp`, `T_erlang` (= T_n). The
n sub-stages have rate nγ each, so the mean infectious period is `n · 1/(nγ)`. "η_n preserves the
PGF" has no counterpart in `StagesNatTransData` (no PGF field) and is not formalised; the change
of the final size needs a final-size solution, which the vocabulary lacks, and is not formalised.
"R₀ changes" is read as `T_exp·e ≠ T_n·e` for every positive excess degree e when n ≥ 2. -/
namespace Alignment.Shadows.CategoricalComposition.R98_keyProperty

open Filter Topology

/-- Stages data with `n + 1` stages (so that `0 < n + 1` holds). -/
def stagesSucc (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ) (n : ℕ) : StagesNatTransData :=
  ⟨β, γ, n + 1, hβ, hγ, Nat.succ_pos n⟩

-- AMBIGUITY: "increases with n" read as strictly increasing in n at fixed β, γ.
@[sa_reference "CategoricalComposition.R98.keyProperty"]
def T : Prop :=
  (∀ d : StagesNatTransData, (d.n : ℝ) * (1 / ((d.n : ℝ) * d.gamma)) = 1 / d.gamma) ∧
  (∀ d : StagesNatTransData,
      d.T_erlang = 1 - ((d.n : ℝ) * d.gamma / (d.beta + (d.n : ℝ) * d.gamma)) ^ d.n) ∧
  (∀ d d' : StagesNatTransData, d.beta = d'.beta → d.gamma = d'.gamma → d.n < d'.n →
      d.T_erlang < d'.T_erlang) ∧
  (∀ (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ),
      Tendsto (fun n : ℕ => (stagesSucc β γ hβ hγ n).T_erlang) atTop
        (𝓝 (1 - Real.exp (-(β / γ))))) ∧
  (∀ (d : StagesNatTransData) (e : ℝ), 0 < e → 2 ≤ d.n → d.T_exp * e ≠ d.T_erlang * e)

/-- S1: n sub-stages of rate nγ keep the mean infectious period 1/γ. -/
@[sa_shadow "CategoricalComposition.R98.keyProperty" 1]
def S1 : Prop := ∀ d : StagesNatTransData, (d.n : ℝ) * (1 / ((d.n : ℝ) * d.gamma)) = 1 / d.gamma
/-- S2: `T_n = 1 − (nγ/(β+nγ))^n`. -/
@[sa_shadow "CategoricalComposition.R98.keyProperty" 2]
def S2 : Prop :=
  ∀ d : StagesNatTransData,
    d.T_erlang = 1 - ((d.n : ℝ) * d.gamma / (d.beta + (d.n : ℝ) * d.gamma)) ^ d.n
/-- S3: `T_n` is strictly increasing in n. -/
@[sa_shadow "CategoricalComposition.R98.keyProperty" 3]
def S3 : Prop :=
  ∀ d d' : StagesNatTransData, d.beta = d'.beta → d.gamma = d'.gamma → d.n < d'.n →
    d.T_erlang < d'.T_erlang
/-- S4: `T_n → 1 − exp(−β/γ)` as n → ∞. -/
@[sa_shadow "CategoricalComposition.R98.keyProperty" 4]
def S4 : Prop :=
  ∀ (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ),
    Tendsto (fun n : ℕ => (stagesSucc β γ hβ hγ n).T_erlang) atTop (𝓝 (1 - Real.exp (-(β / γ))))
/-- S5: with n ≥ 2 stages, R₀ = T·e changes. -/
@[sa_shadow "CategoricalComposition.R98.keyProperty" 5]
def S5 : Prop :=
  ∀ (d : StagesNatTransData) (e : ℝ), 0 < e → 2 ≤ d.n → d.T_exp * e ≠ d.T_erlang * e

@[sa_ref_forward "CategoricalComposition.R98.keyProperty" 1] theorem ref_fwd1 : T → S1 :=
  fun t => t.1
@[sa_ref_forward "CategoricalComposition.R98.keyProperty" 2] theorem ref_fwd2 : T → S2 :=
  fun t => t.2.1
@[sa_ref_forward "CategoricalComposition.R98.keyProperty" 3] theorem ref_fwd3 : T → S3 :=
  fun t => t.2.2.1
@[sa_ref_forward "CategoricalComposition.R98.keyProperty" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2.1
@[sa_ref_forward "CategoricalComposition.R98.keyProperty" 5] theorem ref_fwd5 : T → S5 :=
  fun t => t.2.2.2.2
@[sa_complete "CategoricalComposition.R98.keyProperty"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.CategoricalComposition.R98_keyProperty

/-! ## `CategoricalComposition.R98b.1` (re-authored blind)

Text: "**Result 98b.** Excess-degree preservation: the excess degree ratio is independent of the
number of stages (it depends only on the PGF)."

The stages construction changes the transmissibility `T` (and the ODE dimension) of a layer but
not its PGF. "Depends only on the PGF" is read as: `EBCMLayer.excessDegree` is determined by the
PGF data `mean` (ψ'(1)) and `secondFactorial` (ψ''(1)), whatever `T` and `dim` are. -/
namespace Alignment.Shadows.CategoricalComposition.R98b_1

@[sa_reference "CategoricalComposition.R98b.1"]
def T : Prop :=
  ∀ l₁ l₂ : EBCMLayer, l₁.mean = l₂.mean → l₁.secondFactorial = l₂.secondFactorial →
    l₁.excessDegree = l₂.excessDegree

/-- S1: layers with the same PGF data have the same excess degree. -/
@[sa_shadow "CategoricalComposition.R98b.1" 1]
def S1 : Prop :=
  ∀ l₁ l₂ : EBCMLayer, l₁.mean = l₂.mean → l₁.secondFactorial = l₂.secondFactorial →
    l₁.excessDegree = l₂.excessDegree

@[sa_ref_forward "CategoricalComposition.R98b.1" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "CategoricalComposition.R98b.1"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.R98b_1

/-! ## `CategoricalComposition.R98b.3` (re-authored blind)

Text: "The map η_n sends T_exp to T_n and keeps the PGF."

`T_exp = β/(β+γ)` and `T_n = 1 − (nγ/(β+nγ))^n` in primitive terms; "keeps the PGF" is read as:
the PGF-derived excess degree of a layer does not depend on its transmissibility or dimension. -/
namespace Alignment.Shadows.CategoricalComposition.R98b_3

@[sa_reference "CategoricalComposition.R98b.3"]
def T : Prop :=
  (∀ d : StagesNatTransData, d.T_exp = d.beta / (d.beta + d.gamma)) ∧
  (∀ d : StagesNatTransData,
      d.T_erlang = 1 - ((d.n : ℝ) * d.gamma / (d.beta + (d.n : ℝ) * d.gamma)) ^ d.n) ∧
  (∀ l l' : EBCMLayer, l'.mean = l.mean → l'.secondFactorial = l.secondFactorial →
      l'.excessDegree = l.excessDegree)

/-- S1: the source transmissibility is `T_exp = β/(β+γ)`. -/
@[sa_shadow "CategoricalComposition.R98b.3" 1]
def S1 : Prop := ∀ d : StagesNatTransData, d.T_exp = d.beta / (d.beta + d.gamma)
/-- S2: the target transmissibility is `T_n = 1 − (nγ/(β+nγ))^n`. -/
@[sa_shadow "CategoricalComposition.R98b.3" 2]
def S2 : Prop :=
  ∀ d : StagesNatTransData,
    d.T_erlang = 1 - ((d.n : ℝ) * d.gamma / (d.beta + (d.n : ℝ) * d.gamma)) ^ d.n
/-- S3: the PGF-derived excess degree is unchanged when only T (and dim) change. -/
@[sa_shadow "CategoricalComposition.R98b.3" 3]
def S3 : Prop :=
  ∀ l l' : EBCMLayer, l'.mean = l.mean → l'.secondFactorial = l.secondFactorial →
    l'.excessDegree = l.excessDegree

@[sa_ref_forward "CategoricalComposition.R98b.3" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "CategoricalComposition.R98b.3" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "CategoricalComposition.R98b.3" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "CategoricalComposition.R98b.3"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.CategoricalComposition.R98b_3

/-! ## `CategoricalComposition.R98c.2` (re-authored blind)

Text: "It is the identity that fixes the sub-stage rate nγ."

-- AMBIGUITY: "It" read as the mean-preservation identity of Result 98c, `n·(1/(nγ)) = 1/γ`
(n sub-stages of equal rate have total mean 1/γ); "fixes the sub-stage rate nγ" read as: the rate
nγ satisfies it (S1), and it is the only positive rate that does (S2). -/
namespace Alignment.Shadows.CategoricalComposition.R98c_2

@[sa_reference "CategoricalComposition.R98c.2"]
def T : Prop :=
  (∀ d : StagesNatTransData, (d.n : ℝ) * (1 / ((d.n : ℝ) * d.gamma)) = 1 / d.gamma) ∧
  (∀ (d : StagesNatTransData) (ρ : ℝ), 0 < ρ → (d.n : ℝ) * (1 / ρ) = 1 / d.gamma →
      ρ = (d.n : ℝ) * d.gamma)

/-- S1: the sub-stage rate nγ gives mean infectious period 1/γ. -/
@[sa_shadow "CategoricalComposition.R98c.2" 1]
def S1 : Prop := ∀ d : StagesNatTransData, (d.n : ℝ) * (1 / ((d.n : ℝ) * d.gamma)) = 1 / d.gamma
/-- S2: nγ is the only positive sub-stage rate that does. -/
@[sa_shadow "CategoricalComposition.R98c.2" 2]
def S2 : Prop :=
  ∀ (d : StagesNatTransData) (ρ : ℝ), 0 < ρ → (d.n : ℝ) * (1 / ρ) = 1 / d.gamma →
    ρ = (d.n : ℝ) * d.gamma

@[sa_ref_forward "CategoricalComposition.R98c.2" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "CategoricalComposition.R98c.2" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "CategoricalComposition.R98c.2"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.CategoricalComposition.R98c_2

/-! ## `CategoricalComposition.R99a.2` (re-authored blind)

Text: "So the clustered model with no triangles is the standard model."

Read over the clustered quantities of `ClusteringExtension` (Result 99 refers to it): with
`⟨t⟩ = 0` the triangle stub fraction vanishes, the mean total degree is the single-edge degree,
and the scalar `clustered_R0` reduces to the standard `T·(excess degree)`. -/
namespace Alignment.Shadows.CategoricalComposition.R99a_2

@[sa_reference "CategoricalComposition.R99a.2"]
def T : Prop :=
  (∀ d : ClusteredR0Data, d.mean_triangle = 0 → clustered_R0 d = d.T * d.excess_single) ∧
  (∀ d : ClusteredPGFData, d.mean_triangle = 0 → clustering_coefficient d = 0) ∧
  (∀ d : ClusteredPGFData, d.mean_triangle = 0 → mean_total_degree d = d.mean_single)

/-- S1: with no triangles, `clustered_R0` is the standard `T·(excess degree)`. -/
@[sa_shadow "CategoricalComposition.R99a.2" 1]
def S1 : Prop :=
  ∀ d : ClusteredR0Data, d.mean_triangle = 0 → clustered_R0 d = d.T * d.excess_single
/-- S2: with no triangles, the triangle stub fraction is zero. -/
@[sa_shadow "CategoricalComposition.R99a.2" 2]
def S2 : Prop := ∀ d : ClusteredPGFData, d.mean_triangle = 0 → clustering_coefficient d = 0
/-- S3: with no triangles, the mean degree is the single-edge mean degree. -/
@[sa_shadow "CategoricalComposition.R99a.2" 3]
def S3 : Prop := ∀ d : ClusteredPGFData, d.mean_triangle = 0 → mean_total_degree d = d.mean_single

@[sa_ref_forward "CategoricalComposition.R99a.2" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "CategoricalComposition.R99a.2" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "CategoricalComposition.R99a.2" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "CategoricalComposition.R99a.2"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.CategoricalComposition.R99a_2

/-! ## `CategoricalComposition.R99a.3` (re-authored blind)

Text: "The triangle stub fraction 2⟨t⟩/(2⟨t⟩+⟨s⟩) (called the clustering coefficient in
ClusteringExtension; the clustering coefficient is 2⟨t⟩/⟨k(k−1)⟩) vanishes when ⟨t⟩ = 0."

The triangle stub fraction is the operation `clustering_coefficient` of `ClusteringExtension`
(named there the clustering coefficient). -/
namespace Alignment.Shadows.CategoricalComposition.R99a_3

@[sa_reference "CategoricalComposition.R99a.3"]
def T : Prop :=
  (∀ d : ClusteredPGFData, clustering_coefficient d =
      2 * d.mean_triangle / (2 * d.mean_triangle + d.mean_single)) ∧
  (∀ d : ClusteredPGFData, d.mean_triangle = 0 → clustering_coefficient d = 0)

/-- S1: `clustering_coefficient` is the triangle stub fraction `2⟨t⟩/(2⟨t⟩+⟨s⟩)`. -/
@[sa_shadow "CategoricalComposition.R99a.3" 1]
def S1 : Prop :=
  ∀ d : ClusteredPGFData,
    clustering_coefficient d = 2 * d.mean_triangle / (2 * d.mean_triangle + d.mean_single)
/-- S2: it vanishes when `⟨t⟩ = 0`. -/
@[sa_shadow "CategoricalComposition.R99a.3" 2]
def S2 : Prop := ∀ d : ClusteredPGFData, d.mean_triangle = 0 → clustering_coefficient d = 0

@[sa_ref_forward "CategoricalComposition.R99a.3" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "CategoricalComposition.R99a.3" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "CategoricalComposition.R99a.3"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.CategoricalComposition.R99a_3

/-! ## `CategoricalComposition.R99b.2` (re-authored blind)

Text: "The scalar `clustered_R0` = T·excess_single + T·(2⟨t⟩/(⟨s⟩+2⟨t⟩))·(1+T) is not the R₀ of a
clustered network (ClusteringExtension, Result 72)."

`clustered_R0` is the operation of `ClusteringExtension`. -- AMBIGUITY: "is not the R₀ of a
clustered network": the clustered-network R₀ has no definition in the vocabulary. Read through the
reason given in ClusteringExtension Result 72 ("its triangle term does not scale with the excess
triangle degree"): the triangle term of `clustered_R0` stays below T(1+T) however many triangles a
node has, whereas an R₀ must grow with the number of triangles per node (S2). -/
namespace Alignment.Shadows.CategoricalComposition.R99b_2

@[sa_reference "CategoricalComposition.R99b.2"]
def T : Prop :=
  (∀ d : ClusteredR0Data, clustered_R0 d = d.T * d.excess_single +
      d.T * (2 * d.mean_triangle / (d.mean_single + 2 * d.mean_triangle)) * (1 + d.T)) ∧
  (∀ d : ClusteredR0Data, clustered_R0 d - d.T * d.excess_single ≤ d.T * (1 + d.T))

/-- S1: the formula of the scalar `clustered_R0`. -/
@[sa_shadow "CategoricalComposition.R99b.2" 1]
def S1 : Prop :=
  ∀ d : ClusteredR0Data, clustered_R0 d = d.T * d.excess_single +
    d.T * (2 * d.mean_triangle / (d.mean_single + 2 * d.mean_triangle)) * (1 + d.T)
/-- S2: its triangle term is bounded by T(1+T), independently of the triangle degree. -/
@[sa_shadow "CategoricalComposition.R99b.2" 2]
def S2 : Prop := ∀ d : ClusteredR0Data, clustered_R0 d - d.T * d.excess_single ≤ d.T * (1 + d.T)

@[sa_ref_forward "CategoricalComposition.R99b.2" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "CategoricalComposition.R99b.2" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "CategoricalComposition.R99b.2"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.CategoricalComposition.R99b_2

/-! ## `CategoricalComposition.r0SumEqTrace` (blind)

Text: "The additive rule `R0_sum` is the trace of the multiplex next-generation matrix K."

`K = [[T₁e₁, T₁⟨k₁⟩], [T₂⟨k₂⟩, T₂e₂]]` with `eᵢ = ψᵢ''(1)/ψᵢ'(1)` (Result 96c), in primitive
terms. -/
namespace Alignment.Shadows.CategoricalComposition.r0SumEqTrace

/-- `eᵢ = ψᵢ''(1)/ψᵢ'(1)`. -/
def e (l : EBCMLayer) : ℝ := l.secondFactorial / l.mean
/-- The multiplex next-generation matrix. -/
def Kmp (p : MultiplexProduct) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.layer1.T * e p.layer1, p.layer1.T * p.layer1.mean;
     p.layer2.T * p.layer2.mean, p.layer2.T * e p.layer2]

@[sa_reference "CategoricalComposition.r0SumEqTrace"]
def T : Prop := ∀ p : MultiplexProduct, p.R0_sum = (Kmp p).trace

/-- S1: `R0_sum = tr K`. -/
@[sa_shadow "CategoricalComposition.r0SumEqTrace" 1]
def S1 : Prop := ∀ p : MultiplexProduct, p.R0_sum = (Kmp p).trace

@[sa_ref_forward "CategoricalComposition.r0SumEqTrace" 1] theorem ref_fwd1 : T → S1 := fun t => t
@[sa_complete "CategoricalComposition.r0SumEqTrace"] theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.CategoricalComposition.r0SumEqTrace

/-! ## `CategoricalComposition.multiplexR0SumNeSpectral` (blind)

Text: "**The additive multiplex R₀ is not the spectral radius.** For two 3-regular layers with
T = 6/25, K = [[12/25, 18/25], [18/25, 12/25]] has the eigenvectors (1, 1) with eigenvalue 6/5 and
(1, −1) with eigenvalue −6/25, so ρ(K) = 6/5 > 1, while `R0_sum` = 24/25 < 1."

A 3-regular layer has `⟨k⟩ = 3`, `ψ''(1) = 6`; `K` is the multiplex next-generation matrix of
Result 96c in primitive terms; ρ(K) = the largest real eigenvalue. The arithmetic comparisons
`6/5 > 1` and `24/25 < 1` are closed facts and are not separate shadows. -/
namespace Alignment.Shadows.CategoricalComposition.multiplexR0SumNeSpectral

/-- `eᵢ = ψᵢ''(1)/ψᵢ'(1)`. -/
def e (l : EBCMLayer) : ℝ := l.secondFactorial / l.mean
/-- The multiplex next-generation matrix. -/
def Kmp (p : MultiplexProduct) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.layer1.T * e p.layer1, p.layer1.T * p.layer1.mean;
     p.layer2.T * p.layer2.mean, p.layer2.T * e p.layer2]
/-- `μ` is the largest real eigenvalue of `A`. -/
def IsRho (A : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℝ) : Prop :=
  Module.End.HasEigenvalue (Matrix.toLin' A) μ ∧
    ∀ ν : ℝ, Module.End.HasEigenvalue (Matrix.toLin' A) ν → ν ≤ μ
/-- A 3-regular layer with `T = 6/25`. -/
def threeReg (l : EBCMLayer) : Prop := l.mean = 3 ∧ l.secondFactorial = 6 ∧ l.T = 6 / 25

@[sa_reference "CategoricalComposition.multiplexR0SumNeSpectral"]
def T : Prop :=
  ∀ p : MultiplexProduct, threeReg p.layer1 → threeReg p.layer2 →
    Kmp p = !![12 / 25, 18 / 25; 18 / 25, 12 / 25] ∧
    (Kmp p).mulVec ![1, 1] = (6 / 5 : ℝ) • ![1, 1] ∧
    (Kmp p).mulVec ![1, -1] = (-6 / 25 : ℝ) • ![1, -1] ∧
    IsRho (Kmp p) (6 / 5) ∧ p.R0_sum = 24 / 25

/-- S1: the matrix K of the example. -/
@[sa_shadow "CategoricalComposition.multiplexR0SumNeSpectral" 1]
def S1 : Prop :=
  ∀ p : MultiplexProduct, threeReg p.layer1 → threeReg p.layer2 →
    Kmp p = !![12 / 25, 18 / 25; 18 / 25, 12 / 25]
/-- S2: (1, 1) is an eigenvector with eigenvalue 6/5. -/
@[sa_shadow "CategoricalComposition.multiplexR0SumNeSpectral" 2]
def S2 : Prop :=
  ∀ p : MultiplexProduct, threeReg p.layer1 → threeReg p.layer2 →
    (Kmp p).mulVec ![1, 1] = (6 / 5 : ℝ) • ![1, 1]
/-- S3: (1, −1) is an eigenvector with eigenvalue −6/25. -/
@[sa_shadow "CategoricalComposition.multiplexR0SumNeSpectral" 3]
def S3 : Prop :=
  ∀ p : MultiplexProduct, threeReg p.layer1 → threeReg p.layer2 →
    (Kmp p).mulVec ![1, -1] = (-6 / 25 : ℝ) • ![1, -1]
/-- S4: ρ(K) = 6/5. -/
@[sa_shadow "CategoricalComposition.multiplexR0SumNeSpectral" 4]
def S4 : Prop :=
  ∀ p : MultiplexProduct, threeReg p.layer1 → threeReg p.layer2 → IsRho (Kmp p) (6 / 5)
/-- S5: `R0_sum = 24/25`. -/
@[sa_shadow "CategoricalComposition.multiplexR0SumNeSpectral" 5]
def S5 : Prop :=
  ∀ p : MultiplexProduct, threeReg p.layer1 → threeReg p.layer2 → p.R0_sum = 24 / 25

@[sa_ref_forward "CategoricalComposition.multiplexR0SumNeSpectral" 1] theorem ref_fwd1 :
    T → S1 := fun t p h1 h2 => (t p h1 h2).1
@[sa_ref_forward "CategoricalComposition.multiplexR0SumNeSpectral" 2] theorem ref_fwd2 :
    T → S2 := fun t p h1 h2 => (t p h1 h2).2.1
@[sa_ref_forward "CategoricalComposition.multiplexR0SumNeSpectral" 3] theorem ref_fwd3 :
    T → S3 := fun t p h1 h2 => (t p h1 h2).2.2.1
@[sa_ref_forward "CategoricalComposition.multiplexR0SumNeSpectral" 4] theorem ref_fwd4 :
    T → S4 := fun t p h1 h2 => (t p h1 h2).2.2.2.1
@[sa_ref_forward "CategoricalComposition.multiplexR0SumNeSpectral" 5] theorem ref_fwd5 :
    T → S5 := fun t p h1 h2 => (t p h1 h2).2.2.2.2
@[sa_complete "CategoricalComposition.multiplexR0SumNeSpectral"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T :=
  fun p h1 h2 => ⟨s1 p h1 h2, s2 p h1 h2, s3 p h1 h2, s4 p h1 h2, s5 p h1 h2⟩

end Alignment.Shadows.CategoricalComposition.multiplexR0SumNeSpectral

/-! ## `CategoricalComposition.stagesChangeTransmissibility` (blind)

Text: "Staging changes the transmissibility: with n = 2 stages, T_exp = β/(β+γ) <
T_2 = 1 − (2γ/(β+2γ))², since the difference is β²γ/((β+γ)(β+2γ)²) > 0." -/
namespace Alignment.Shadows.CategoricalComposition.stagesChangeTransmissibility

@[sa_reference "CategoricalComposition.stagesChangeTransmissibility"]
def T : Prop :=
  (∀ d : StagesNatTransData, d.n = 2 → d.T_exp < d.T_erlang) ∧
  (∀ d : StagesNatTransData, d.T_exp = d.beta / (d.beta + d.gamma)) ∧
  (∀ d : StagesNatTransData, d.n = 2 →
      d.T_erlang = 1 - (2 * d.gamma / (d.beta + 2 * d.gamma)) ^ 2) ∧
  (∀ d : StagesNatTransData, d.n = 2 →
      d.T_erlang - d.T_exp =
        d.beta ^ 2 * d.gamma / ((d.beta + d.gamma) * (d.beta + 2 * d.gamma) ^ 2))

/-- S1: with two stages, `T_exp < T_2`. -/
@[sa_shadow "CategoricalComposition.stagesChangeTransmissibility" 1]
def S1 : Prop := ∀ d : StagesNatTransData, d.n = 2 → d.T_exp < d.T_erlang
/-- S2: `T_exp = β/(β+γ)`. -/
@[sa_shadow "CategoricalComposition.stagesChangeTransmissibility" 2]
def S2 : Prop := ∀ d : StagesNatTransData, d.T_exp = d.beta / (d.beta + d.gamma)
/-- S3: `T_2 = 1 − (2γ/(β+2γ))²`. -/
@[sa_shadow "CategoricalComposition.stagesChangeTransmissibility" 3]
def S3 : Prop :=
  ∀ d : StagesNatTransData, d.n = 2 → d.T_erlang = 1 - (2 * d.gamma / (d.beta + 2 * d.gamma)) ^ 2
/-- S4: the difference is `β²γ/((β+γ)(β+2γ)²)`. -/
@[sa_shadow "CategoricalComposition.stagesChangeTransmissibility" 4]
def S4 : Prop :=
  ∀ d : StagesNatTransData, d.n = 2 →
    d.T_erlang - d.T_exp = d.beta ^ 2 * d.gamma / ((d.beta + d.gamma) * (d.beta + 2 * d.gamma) ^ 2)

@[sa_ref_forward "CategoricalComposition.stagesChangeTransmissibility" 1] theorem ref_fwd1 :
    T → S1 := fun t => t.1
@[sa_ref_forward "CategoricalComposition.stagesChangeTransmissibility" 2] theorem ref_fwd2 :
    T → S2 := fun t => t.2.1
@[sa_ref_forward "CategoricalComposition.stagesChangeTransmissibility" 3] theorem ref_fwd3 :
    T → S3 := fun t => t.2.2.1
@[sa_ref_forward "CategoricalComposition.stagesChangeTransmissibility" 4] theorem ref_fwd4 :
    T → S4 := fun t => t.2.2.2
@[sa_complete "CategoricalComposition.stagesChangeTransmissibility"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.CategoricalComposition.stagesChangeTransmissibility

end
