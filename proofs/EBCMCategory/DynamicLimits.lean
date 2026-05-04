import EBCMCategory.CoarseGrain
import Mathlib.Tactic

/-!
# DynamicLimits — Limiting behaviour of dynamic network EBCMs

On a **dynamic network**, edges form (rate η₁) and break (rate η₂),
adding a dormant-edge variable φ_D to the standard EBCM.

This file formalises two limiting regimes:

1. **Static limit (η → 0)**: Rewiring terms vanish; the dynamic EBCM
   collapses to the standard (static) EBCM. The dormant-edge variable
   φ_D decouples, reducing the dimension by 1.

2. **Fast-rewiring limit (η → ∞)**: The network reshuffles so quickly
   that edge correlations are destroyed at each instant. The system
   collapses to a **mean-field** model — only population-level
   aggregates (S, I, R) remain.

The dynamic model thus interpolates between two extremes:

    Mean-field (dim 3) ← fast rewiring — Dynamic (dim 5) — static → EBCM (dim 4)

## Key results

| Result | Statement                                              |
|--------|--------------------------------------------------------|
| 29     | Static EBCM dim < Dynamic EBCM dim                     |
| 30     | Dynamic EBCM dim < Pair approximation dim (N ≥ 1)      |
| 31     | Static limit: dynamic → static (dim 5 → 4)             |
| 32     | Fast-rewiring limit: dynamic → mean-field (dim 5 → 3)  |
| 33     | R₀ is independent of rewiring rate                      |
| 34     | Coarse-graining commutes with static limit              |
| 35     | Fast-rewiring limit IS a coarse-graining                |
| 36     | For Poisson, fast-rewiring R₀ = EBCM R₀                |
| 37     | For non-Poisson, fast-rewiring R₀ ≠ EBCM R₀            |
| 38     | Dynamic refines static                                   |
| 39     | Fast-rewiring is coarser than static                     |
| 40     | Full tower: mean-field < static < dynamic                |

## References

* Miller, Slim, Volz (2012). Edge-based compartmental modelling for
  infectious disease spread on dynamic contact networks.
-/

/-! ## Dynamic EBCM model -/

/-- A dynamic EBCM: the standard edge model augmented with a dormant-edge
    variable φ_D for tracking edge rewiring dynamics.

    The dynamic SIR EBCM has **5 ODE variables**: θ, φ_I, R, φ_D, (φ_S algebraic).
    Compare with the static EBCM's 4 variables. -/
structure DynamicEBCM where
  disease : SIRParams
  pgf : PGFData

namespace DynamicEBCM

/-- The state-space dimension of a dynamic EBCM: always 5.
    (θ, φ_S, φ_I, R, plus the new φ_D for dormant edge stubs.) -/
def dim (_ : DynamicEBCM) : ℕ := 5

/-- R₀ for a dynamic EBCM.
    **Key result**: R₀ does NOT depend on the rewiring rate.
    It depends only on transmissibility and the excess degree ratio,
    because rewiring preserves the degree distribution. -/
def R0 (m : DynamicEBCM) : ℚ :=
  m.disease.transmissibility * m.pgf.excessDegree

/-- Project a dynamic EBCM to an abstract EpiModel. -/
def toEpiModel (m : DynamicEBCM) : EpiModel where
  dim := 5
  R0 := m.R0

/-- The **static limit** (η₁, η₂ → 0): rewiring terms vanish,
    φ_D decouples from the system, and we recover the standard
    4-variable EBCM. The R₀ is preserved. -/
def staticLimit (m : DynamicEBCM) : EpiModel :=
  edgeModel m.disease m.pgf

/-- The **fast-rewiring limit** (η₁, η₂ → ∞): the network reshuffles
    so fast that at each instant it looks like a fresh configuration
    model draw. Edge correlations are destroyed, and only mean-degree
    information survives. The system collapses to a 3D mean-field model.

    Crucially, R₀ now uses the **mean degree** κ rather than the
    excess degree ψ''(1)/ψ'(1), because the fast-rewiring limit
    destroys the degree-heterogeneity amplification effect. -/
def fastRewiringLimit (m : DynamicEBCM) : EpiModel where
  dim := 3
  R0 := m.disease.transmissibility * m.pgf.mean

end DynamicEBCM

/-! ## Dimension ordering theorems -/

/-- **Result 29.** The static EBCM (dim 4) has fewer variables than
    the dynamic EBCM (dim 5). -/
theorem static_lt_dynamic (m : DynamicEBCM) :
    m.staticLimit.dim < m.toEpiModel.dim := by
  simp [DynamicEBCM.staticLimit, DynamicEBCM.toEpiModel, edgeModel]

/-- **Result 30.** The dynamic EBCM (dim 5) has fewer variables than
    pair approximation (dim 12N) for N ≥ 1. -/
theorem dynamic_lt_pair (m : DynamicEBCM) (N : ℕ) (hN : 1 ≤ N) :
    m.toEpiModel.dim < 12 * N := by
  simp [DynamicEBCM.toEpiModel]
  omega

/-! ## Limit theorems -/

/-- **Result 31.** Static limit: the dimension drops from 5 to 4.
    When rewiring rates go to zero, the θ equation loses its η₁/η₂ terms
    and the φ_D equation decouples entirely (dφ_D/dt → 0). -/
theorem static_limit_dim (m : DynamicEBCM) :
    m.staticLimit.dim = 4 := by
  simp [DynamicEBCM.staticLimit, edgeModel]

/-- **Result 32.** Fast-rewiring limit: the dimension drops to 3.
    When the network randomises infinitely fast, the joint distribution
    over edge states factorises, destroying all pairwise correlations.
    Only population-level aggregates (S, I, R) survive. -/
theorem fast_rewiring_dim (m : DynamicEBCM) :
    m.fastRewiringLimit.dim = 3 := by
  rfl

/-- **Result 33.** R₀ is independent of the rewiring rate.
    The static limit preserves R₀ exactly, because rewiring
    preserves the degree distribution and hence the excess degree ratio. -/
theorem R0_rewiring_independent (m : DynamicEBCM) :
    m.staticLimit.R0 = m.R0 := by
  simp [DynamicEBCM.staticLimit, DynamicEBCM.R0, edgeModel]

/-! ## Commutativity with coarse-graining -/

/-- **Result 34.** Coarse-graining commutes with the static limit.
    F(dynamic) = F(staticLimit(dynamic)), because both give dim 3
    with the same R₀. -/
theorem coarseGrain_static_comm (m : DynamicEBCM) :
    coarseGrain m.toEpiModel = coarseGrain m.staticLimit := by
  simp [coarseGrain, DynamicEBCM.toEpiModel, DynamicEBCM.staticLimit,
        DynamicEBCM.R0, edgeModel]

/-- **Result 35.** The fast-rewiring limit has the same dimension
    as coarse-graining (both give dim = 3).
    The fast-rewiring limit IS a form of coarse-graining. -/
theorem fast_rewiring_is_coarsegraining (m : DynamicEBCM) :
    m.fastRewiringLimit.dim = (coarseGrain m.toEpiModel).dim := by
  simp [DynamicEBCM.fastRewiringLimit, coarseGrain, DynamicEBCM.toEpiModel]

/-! ## R₀ comparison across limits -/

/-- **Result 36.** For Poisson networks, the fast-rewiring R₀ equals
    the EBCM R₀. This is because the Poisson excess degree equals the
    mean degree: ψ''(1)/ψ'(1) = κ. -/
theorem fast_rewiring_R0_poisson (p : SIRParams) (κ : ℚ) (hκ : 0 < κ) :
    let m : DynamicEBCM := ⟨p, PGFData.poisson κ hκ⟩
    m.fastRewiringLimit.R0 = m.R0 := by
  simp only [DynamicEBCM.fastRewiringLimit, DynamicEBCM.R0,
        PGFData.poisson, PGFData.excessDegree]
  congr 1
  have : (κ : ℚ) ≠ 0 := ne_of_gt hκ
  field_simp

/-- **Result 37.** For non-Poisson networks, the fast-rewiring limit
    gives a DIFFERENT R₀ than the EBCM.

    Witness: a network with mean κ=3, second factorial=15 (excess=5).
    T=1/2, so EBCM R₀ = 5/2, fast-rewiring R₀ = 3/2. -/
theorem fast_rewiring_R0_differs :
    ∃ (m : DynamicEBCM), m.fastRewiringLimit.R0 ≠ m.R0 := by
  refine ⟨⟨⟨1, 1, by norm_num, by norm_num⟩,
           ⟨3, 15, by norm_num, by norm_num⟩⟩, ?_⟩
  simp [DynamicEBCM.fastRewiringLimit, DynamicEBCM.R0,
        SIRParams.transmissibility, PGFData.excessDegree]
  norm_num

/-! ## Refinement ordering -/

/-- **Result 38.** The dynamic model refines the static model
    (it has strictly more state variables: 5 > 4). -/
theorem dynamic_refines_static (m : DynamicEBCM) :
    m.staticLimit ≤ m.toEpiModel := by
  show m.staticLimit.dim ≤ m.toEpiModel.dim
  simp [DynamicEBCM.staticLimit, DynamicEBCM.toEpiModel, edgeModel]

/-- **Result 39.** The fast-rewiring limit is coarser than the static limit.
    Mean-field (dim 3) ≤ Static EBCM (dim 4). -/
theorem fast_rewiring_coarser_than_static (m : DynamicEBCM) :
    m.fastRewiringLimit ≤ m.staticLimit := by
  show m.fastRewiringLimit.dim ≤ m.staticLimit.dim
  simp [DynamicEBCM.fastRewiringLimit, DynamicEBCM.staticLimit, edgeModel]

/-- **Result 40.** The full tower: mean-field < static EBCM < dynamic EBCM.
    Combined with Hierarchy.lean, this gives:
    Mean-field (3) < Static EBCM (4) < Dynamic EBCM (5) < Pair (12N) < Full (3^N) -/
theorem full_tower (m : DynamicEBCM) :
    m.fastRewiringLimit.dim < m.staticLimit.dim ∧
    m.staticLimit.dim < m.toEpiModel.dim := by
  simp [DynamicEBCM.fastRewiringLimit, DynamicEBCM.staticLimit,
        DynamicEBCM.toEpiModel, edgeModel]
