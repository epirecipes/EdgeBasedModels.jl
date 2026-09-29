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
   that partnerships are fleeting. The system approaches the mean-field
   social-heterogeneity (MFSH) model of Miller, Slim & Volz (2012): nodes
   keep their degrees, so degree heterogeneity survives, and R₀ tends to
   (β/γ)⟨K²⟩/⟨K⟩.

The dynamic model thus interpolates between two extremes:

    MFSH (dim 3 as recorded) ← fast rewiring — Dynamic (dim 5) — static → EBCM (dim 4)

In the edge-swapping (dynamic fixed-degree) EBCM of Miller, Slim & Volz
(2012, §3.2.1), R₀ depends on the rewiring rate η:
R₀(η) = β/(β+η+γ) · ((η+γ)/γ · ⟨K²−K⟩/⟨K⟩ + η/γ) (`DynamicEBCM.R0_edgeSwap`).
It equals T⟨K²−K⟩/⟨K⟩ at η = 0 and tends to the MFSH value (β/γ)⟨K²⟩/⟨K⟩ as
η → ∞ (`R0_edgeSwap_zero`, `R0_edgeSwap_tendsto_mfsh`). The records here
store only the static-limit R₀ (`DynamicEBCM.R0`) and, for
`fastRewiringLimit`, the value T·κ, which is neither limit.

## Key results

| Result | Statement                                              |
|--------|--------------------------------------------------------|
| 29     | Static EBCM dim < Dynamic EBCM dim                     |
| 30     | Dynamic EBCM dim < Pair approximation dim (N ≥ 1)      |
| 31     | Static limit: dynamic → static (dim 5 → 4)             |
| 32     | Fast-rewiring limit record: dim 5 → 3                   |
| 33     | `DynamicEBCM.R0` stores the static-limit R₀ only        |
| 34     | Coarse-graining commutes with static limit              |
| 35     | Fast-rewiring record has the dimension of a coarse-graining |
| 36     | For Poisson, the stored T·κ equals the static R₀        |
| 37     | Some record has T·κ ≠ static R₀; MFSH R₀ > static R₀   |
| 38     | Dynamic refines static                                   |
| 39     | Fast-rewiring is coarser than static                     |
| 40     | Full tower: mean-field < static < dynamic                |

## References

* Miller, Slim, Volz (2012). Edge-based compartmental modelling for
  infectious disease spread. J. R. Soc. Interface 9, 890–906
  (arXiv:1106.6320: §3.1 MFSH, §3.2 dynamic fixed-degree, App. D.1.2–D.1.3).
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

/-- The static-limit R₀ T·ψ''(1)/ψ'(1) stored for a dynamic EBCM.
    `DynamicEBCM` records no rewiring rate, so this is not the R₀ of the
    dynamic model.
    In the edge-swapping EBCM, R₀ depends on η (Miller, Slim & Volz 2012,
    §3.2.1; `R0_edgeSwap`). -/
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

/-- The **fast-rewiring limit** record (η₁, η₂ → ∞): the network
    reshuffles so fast that partnerships are fleeting. The limit is the
    MFSH model, in which nodes keep their degrees.

    Its R₀ is (β/γ)⟨K²⟩/⟨K⟩ = (β/γ)(ψ''(1)/ψ'(1) + 1) (`R0_mfsh`), which
    keeps degree heterogeneity. The R₀ stored here, T·ψ'(1) = βκ/(β+γ), is
    not that limit; it is kept for compatibility (Results 36, 37). -/
def fastRewiringLimit (m : DynamicEBCM) : EpiModel where
  dim := 3
  R0 := m.disease.transmissibility * m.pgf.mean

/-- R₀ of the edge-swapping (dynamic fixed-degree) EBCM with rewiring rate
    η (Miller, Slim & Volz 2012, §3.2.1):
    R₀(η) = β/(β+η+γ) · ((η+γ)/γ · ψ''(1)/ψ'(1) + η/γ),
    with ⟨K²−K⟩/⟨K⟩ = ψ''(1)/ψ'(1). -/
def R0_edgeSwap (m : DynamicEBCM) (η : ℚ) : ℚ :=
  m.disease.β / (m.disease.β + η + m.disease.γ) *
    ((η + m.disease.γ) / m.disease.γ * m.pgf.excessDegree + η / m.disease.γ)

/-- R₀ of the mean-field social-heterogeneity (MFSH) model, the fast-rewiring
    limit of the edge-swapping EBCM (Miller, Slim & Volz 2012, App. D.1.2):
    (β/γ)⟨K²⟩/⟨K⟩ = (β/γ)(ψ''(1)/ψ'(1) + 1). -/
def R0_mfsh (m : DynamicEBCM) : ℚ :=
  m.disease.β / m.disease.γ * (m.pgf.excessDegree + 1)

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
    When the network randomises infinitely fast, partnerships become
    fleeting and the model approaches MFSH (θ and R, with S = ψ(θ) and
    I = 1 − S − R), in which degree heterogeneity survives through ψ. -/
theorem fast_rewiring_dim (m : DynamicEBCM) :
    m.fastRewiringLimit.dim = 3 := by
  rfl

/-- **Result 33.** `DynamicEBCM` stores only the static-limit R₀:
    `DynamicEBCM.R0` is T·ψ''(1)/ψ'(1).
    The static limit preserves R₀ exactly, by definition.
    In the edge-swapping EBCM, R₀ depends on the rewiring rate η
    (Miller, Slim & Volz 2012, §3.2.1; see `R0_edgeSwap`). -/
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
    It is not a coarse-graining of the same model: the MFSH R₀ differs
    from the static R₀ (`R0_static_lt_mfsh`). -/
theorem fast_rewiring_is_coarsegraining (m : DynamicEBCM) :
    m.fastRewiringLimit.dim = (coarseGrain m.toEpiModel).dim := by
  simp [DynamicEBCM.fastRewiringLimit, coarseGrain, DynamicEBCM.toEpiModel]

/-! ## R₀ comparison across limits -/

/-- **Result 36.** For Poisson networks, the value T·κ stored by
    `fastRewiringLimit` equals the static EBCM R₀. This is because the Poisson excess degree equals the
    mean degree: ψ''(1)/ψ'(1) = κ.
    It is not the fast-rewiring R₀: for Poisson degrees the MFSH R₀ is
    (β/γ)(κ+1), which differs from βκ/(β+γ) (`R0_mfsh_poisson`,
    `R0_static_lt_mfsh`). -/
theorem fast_rewiring_R0_poisson (p : SIRParams) (κ : ℚ) (hκ : 0 < κ) :
    let m : DynamicEBCM := ⟨p, PGFData.poisson κ hκ⟩
    m.fastRewiringLimit.R0 = m.R0 := by
  simp only [DynamicEBCM.fastRewiringLimit, DynamicEBCM.R0,
        PGFData.poisson, PGFData.excessDegree]
  congr 1
  have : (κ : ℚ) ≠ 0 := ne_of_gt hκ
  field_simp

/-- **Result 37.** Some degree record has a stored fast-rewiring value
    T·κ different from the static EBCM R₀. The genuine fast-rewiring (MFSH)
    R₀ exceeds the static R₀ for every degree law (`R0_static_lt_mfsh`).

    Witness: a network with mean κ=3, second factorial=15 (excess=5).
    T=1/2, so EBCM R₀ = 5/2 and T·κ = 3/2; with β = γ = 1 the MFSH R₀ is
    5 + 1 = 6. -/
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
    Combined with Hierarchy.lean, this gives, for N ≥ 4:
    Mean-field (3) < Static EBCM (4) < Dynamic EBCM (5) < Pair (12N) < Full (3^N);
    the last inequality fails for N ≤ 3. -/
theorem full_tower (m : DynamicEBCM) :
    m.fastRewiringLimit.dim < m.staticLimit.dim ∧
    m.staticLimit.dim < m.toEpiModel.dim := by
  simp [DynamicEBCM.fastRewiringLimit, DynamicEBCM.staticLimit,
        DynamicEBCM.toEpiModel, edgeModel]

/-! ## R₀ of the edge-swapping EBCM (corrections to Results 33, 36, 37) -/

namespace DynamicEBCM

/-- At rewiring rate η = 0 the edge-swapping R₀ is the static-limit R₀
    T·ψ''(1)/ψ'(1). -/
theorem R0_edgeSwap_zero (m : DynamicEBCM) : m.R0_edgeSwap 0 = m.R0 := by
  have hγ : m.disease.γ ≠ 0 := m.disease.γ_pos.ne'
  simp only [R0_edgeSwap, R0, SIRParams.transmissibility, add_zero, zero_add,
    zero_div, div_self hγ, one_mul]

/-- As the rewiring rate η → ∞, the edge-swapping R₀ tends to the MFSH R₀
    (β/γ)(ψ''(1)/ψ'(1) + 1). Together with `R0_edgeSwap_zero` and
    `R0_static_lt_mfsh`, R₀ depends on η. -/
theorem R0_edgeSwap_tendsto_mfsh (m : DynamicEBCM) :
    Filter.Tendsto m.R0_edgeSwap Filter.atTop (nhds m.R0_mfsh) := by
  obtain ⟨⟨β, γ, hβ, hγ⟩, ψ⟩ := m
  have hγ' : γ ≠ 0 := hγ.ne'
  have key : ∀ η : ℚ, 0 ≤ η →
      R0_edgeSwap ⟨⟨β, γ, hβ, hγ⟩, ψ⟩ η =
        β / γ * (ψ.excessDegree + 1) +
          β / γ * (γ * ψ.excessDegree - (ψ.excessDegree + 1) * (β + γ)) / (η + (β + γ)) := by
    intro η hη
    have h1 : β + η + γ ≠ 0 := by linarith
    have h2 : η + (β + γ) ≠ 0 := by linarith
    simp only [R0_edgeSwap]
    field_simp
    ring
  have hlim : Filter.Tendsto (fun η : ℚ => β / γ * (ψ.excessDegree + 1) +
      β / γ * (γ * ψ.excessDegree - (ψ.excessDegree + 1) * (β + γ)) / (η + (β + γ)))
      Filter.atTop (nhds (β / γ * (ψ.excessDegree + 1) + 0)) := by
    refine Filter.Tendsto.add tendsto_const_nhds ?_
    refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
    exact Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 0] with η hη
  exact (key η hη).symm

/-- The MFSH (fast-rewiring) R₀ exceeds the static-limit R₀ for every
    degree record: (β/γ)(ψ''(1)/ψ'(1) + 1) > β/(β+γ) · ψ''(1)/ψ'(1). -/
theorem R0_static_lt_mfsh (m : DynamicEBCM) : m.R0 < m.R0_mfsh := by
  obtain ⟨⟨β, γ, hβ, hγ⟩, ψ⟩ := m
  simp only [R0, R0_mfsh, SIRParams.transmissibility]
  have he : 0 ≤ ψ.excessDegree :=
    div_nonneg ψ.secondFactorial_nonneg ψ.mean_pos.le
  have hT : β / (β + γ) < β / γ := div_lt_div_of_pos_left hβ hγ (by linarith)
  have hpos : 0 < β / γ := div_pos hβ hγ
  nlinarith [mul_le_mul_of_nonneg_right hT.le he]

/-- For Poisson degrees the MFSH (fast-rewiring) R₀ is (β/γ)(κ + 1). -/
theorem R0_mfsh_poisson (p : SIRParams) (κ : ℚ) (hκ : 0 < κ) :
    (⟨p, PGFData.poisson κ hκ⟩ : DynamicEBCM).R0_mfsh = p.β / p.γ * (κ + 1) := by
  simp only [R0_mfsh, PGFData.poisson_excess_eq_mean]

end DynamicEBCM
