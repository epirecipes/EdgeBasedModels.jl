import EBCMCategory.EpiCategory
import Mathlib.Tactic

/-!
# SurvivalBridge — The change of variables between EBCM and Dynamic Survival Analysis

Kiss, Kenah, and Rempała (2023, J. Math. Biol. 87, 36)
proved three landmark results connecting EBCM, pairwise models, and
dynamic survival analysis (DSA):

1. **Poisson-type characterisation** (Theorem 1): The pairwise closure is
   exact iff the degree distribution is Poisson, Binomial, or Negative
   Binomial — collectively called "Poisson-type" (PT) distributions.
   These are exactly the distributions whose PGF satisfies ψ'(u) = α·ψ(u)^κ.

2. **Three-model equivalence** (Theorem 2): For PT distributions, the
   pairwise model, Volz's EBCM, and the DSA model are all equivalent
   and exact in the N→∞ limit.

3. **Survival equation** (Eq. 33): Under PT assumptions, the epidemic
   dynamics collapse to a SINGLE autonomous ODE for the survival
   probability S_t, enabling statistical inference from incidence data.

The key invariant is κ = ψ''(θ)ψ(θ)/ψ'(θ)², which is constant in θ
iff the degree distribution is PT:
  * κ = (n-1)/n for Binomial(n,p)
  * κ = 1 for Poisson(λ)
  * κ = (r+1)/r for NegBin(r,p)

## Relation between the representations (informal)

No category or functor is formalised here. Informally, Volz's model and
the DSA model are two ODE systems for the same configuration-model epidemic:

    Volz :   edge-probability variables θ, p_I, p_S
    DSA  :   survival variables x_θ, x_{SI}, x_{SS}

They are related by the change of variables x_θ = θ,
x_{SI} = p_I · θ · ψ'(θ), x_{SS} = p_S · θ · ψ'(θ) (Kiss, Kenah & Rempała
2023, App. B), which is invertible when θ·ψ'(θ) > 0.

For PT distributions the pairwise model with closure constant κ is a
third equivalent description:

    Pairwise ≅ DSA ≅ Volz   (iff PT degree distribution)

The survival equation (33) is a reduction of these systems to a single
scalar ODE for S_t; it is not a colimit in any formalised sense.

## Key results

| Result | Statement                                              |
|--------|--------------------------------------------------------|
| 41     | The PT ODE ψ' = α·ψ^κ characterises Poisson-type dists|
| 42     | Poisson ⇒ κ(1) = 1 (κ ≡ 1 on an interval iff Poisson)   |
| 43     | Some record has κ(1) < 1 (Binomial: κ ≡ (n-1)/n)       |
| 44     | Some record has κ(1) > 1 (NegBin: κ ≡ (r+1)/r)         |
| 45     | The Volz ↔ DSA variable change is invertible            |
| 46     | S = ψ(θ) gives dS/dt = −β x_SI (chain rule; informal)  |
| 47     | Poisson ⇒ κ(1) = 1 (DSA has mass-action form, rescaled) |
| 48     | PT closure constant κ = excess/degree ratio             |
| 49     | Non-PT distributions: κ(t) varies, closure is approximate|
| 50     | Volz-DSA equivalence holds for ANY degree distribution   |

## References

* Kiss IZ, Kenah E, Rempała GA (2023).
  Necessary and sufficient conditions for exact closures of epidemic
  equations on configuration model networks. J. Math. Biol. 87, 36.
  DOI: 10.1007/s00285-023-01967-9
-/

/-! ## Poisson-type distributions -/

/-- The closure parameter κ for a PGF.
    κ = ψ''(1)·ψ(1) / (ψ'(1))² = secondFactorial / mean²
    (since ψ(1) = 1 for any proper PGF).

    This is the ratio of mean excess degree to mean degree.
    The function κ(θ) = ψ''(θ)ψ(θ)/ψ'(θ)² is constant in θ iff the degree
    distribution is Poisson-type; `closureKappa` records only its value
    κ(1), which does not determine the family: ψ(u) = (1 + u²)/2 has
    κ(1) = 1 but is not Poisson. -/
def PGFData.closureKappa (ψ : PGFData) : ℚ :=
  ψ.secondFactorial / (ψ.mean ^ 2)

/-- Classification of Poisson-type distributions. -/
inductive PTType where
  | poisson       -- κ = 1
  | binomial      -- κ = (n-1)/n < 1 for integer n ≥ 1
  | negBinomial   -- κ = (r+1)/r > 1 for real r > 0
  deriving DecidableEq, Repr

/-- **Result 42.** For Poisson, κ = 1.
    This is because ψ''(1) = κ² and ψ'(1) = κ, so κ = κ²/κ² = 1. -/
theorem poisson_kappa_eq_one (κ : ℚ) (hκ : 0 < κ) :
    (PGFData.poisson κ hκ).closureKappa = 1 := by
  simp only [PGFData.closureKappa, PGFData.poisson]
  have hκ2 : κ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hκ)
  field_simp

/-- **Result 43.** For Binomial(n, p), κ = (n-1)/n < 1.
    We construct a Binomial(3, p) example where ψ'(1) = 3p, ψ''(1) = 6p². -/
theorem binomial_kappa_lt_one :
    ∃ (ψ : PGFData), ψ.closureKappa < 1 := by
  -- Binomial(3, 1/2): mean = 3/2, secondFactorial = 3/2
  -- κ = (3/2) / (3/2)² = (3/2) / (9/4) = 2/3
  refine ⟨⟨3/2, 3/2, by norm_num, by norm_num⟩, ?_⟩
  simp [PGFData.closureKappa]
  norm_num

/-- **Result 44.** For NegBin(r, p), κ = (r+1)/r > 1.
    We construct a NegBin(2, 1/2) example where mean = 2, ψ''(1) = 6. -/
theorem negbin_kappa_gt_one :
    ∃ (ψ : PGFData), ψ.closureKappa > 1 := by
  -- NegBin(2, 1/2): mean = 2, secondFactorial = 6
  -- κ = 6/4 = 3/2 > 1
  refine ⟨⟨2, 6, by norm_num, by norm_num⟩, ?_⟩
  simp [PGFData.closureKappa]
  norm_num

/-! ## The Volz ↔ DSA variable change -/

/-- The Volz model uses edge-probability variables (θ, p_I, p_S).
    The DSA model uses survival-analysis variables (x_θ, x_{SI}, x_{SS}).
    They are related by (Kiss, Kenah & Rempała 2023, App. B):
      x_{SI} = p_I · θ · ψ'(θ)
      x_{SS} = p_S · θ · ψ'(θ)
    The maps `volzToDSA`/`dsaToVolz` below multiply and divide by an
    arbitrary scalar factor `psi_prime`; this change of variables is the
    instance `psi_prime := θ·ψ'(θ)`.
    This is invertible whenever θ·ψ'(θ) > 0. -/
structure VolzState where
  θ : ℚ
  p_I : ℚ
  p_S : ℚ

structure DSAState where
  x_θ : ℚ
  x_SI : ℚ
  x_SS : ℚ

/-- The variable change DSA → Volz: divide by the scalar factor `psi_prime`
    (θ·ψ'(θ) for the change of variables of Kiss, Kenah & Rempała). -/
def dsaToVolz (d : DSAState) (psi_prime : ℚ) (_h : psi_prime ≠ 0) : VolzState where
  θ := d.x_θ
  p_I := d.x_SI / psi_prime
  p_S := d.x_SS / psi_prime

/-- The variable change Volz → DSA: multiply by the scalar factor
    `psi_prime` (θ·ψ'(θ) for the change of variables of Kiss, Kenah &
    Rempała). -/
def volzToDSA (v : VolzState) (psi_prime : ℚ) : DSAState where
  x_θ := v.θ
  x_SI := v.p_I * psi_prime
  x_SS := v.p_S * psi_prime

/-- **Result 45.** The round-trip Volz → DSA → Volz is the identity.
    Together with `dsa_volz_roundtrip`, the variable change is a bijection
    of state spaces for every nonzero scalar factor. -/
theorem volz_dsa_roundtrip (v : VolzState) (ψ' : ℚ) (h : ψ' ≠ 0) :
    dsaToVolz (volzToDSA v ψ') ψ' h = v := by
  cases v with | mk θ pI pS => ?_
  simp only [volzToDSA, dsaToVolz, VolzState.mk.injEq]
  exact ⟨trivial, by field_simp, by field_simp⟩

/-- The round-trip DSA → Volz → DSA is the identity. With Result 45, the two
    maps are mutually inverse for every nonzero scalar factor. -/
theorem dsa_volz_roundtrip (d : DSAState) (ψ' : ℚ) (h : ψ' ≠ 0) :
    volzToDSA (dsaToVolz d ψ' h) ψ' = d := by
  cases d with | mk xθ xSI xSS => ?_
  simp only [volzToDSA, dsaToVolz, DSAState.mk.injEq]
  exact ⟨trivial, by field_simp, by field_simp⟩

/-! ## The survival map -/

/-- **Result 46.** The survival map S_t = ψ(θ(t)) relates the EBCM to
    node-level survival analysis (informal; no category is defined).

    For any PGF, if we define S = ψ(θ) and differentiate, with
    x_{SI} = p_I · θ · ψ'(θ) as in Kiss, Kenah & Rempała (2023, App. B):
      dS/dt = ψ'(θ) · dθ/dt = ψ'(θ) · (-β·p_I·θ) = -β · x_{SI}

    So the DSA equation ẋ_S = -β·x_{SI} is the chain rule applied to
    S = ψ(θ). This chain-rule computation is not formalised here.

    Here we prove the algebraic identity that, for Poisson degrees, the
    EBCM R₀ T·ψ''(1)/ψ'(1) equals T·μ, where μ = mean degree (the
    `nodeModel` value). The DSA model is equivalent to Volz's for every
    degree law, so its R₀ is also T·ψ''(1)/ψ'(1). -/
theorem survival_map_R0_poisson (p : SIRParams) (κ : ℚ) (hκ : 0 < κ) :
    (edgeModel p (PGFData.poisson κ hκ)).R0 =
    (nodeModel p κ).R0 :=
  (poisson_R0_agree p κ hκ).symm

/-! ## Poisson ↔ mass-action equivalence -/

/-- **Result 47.** For Poisson networks (κ=1), the DSA survival equation
    has the form of the classical mass-action SIR survival equation,
    with rescaled rates.

    From Eq (33) of the paper, with κ=1:
      -dS/dt = β̃(S - S²) + γ̃·S·log(S) + ρ̃·S

    This has the form of the mass-action SIR survival equation of
    KhudaBukhsh et al. (2020), with β̃ = μβ, γ̃ = β + γ and ρ̃ = βμρ. The
    Lean theorem proves only that the Poisson record has closureKappa = 1. The proof is that the Poisson PGF
    ψ(u) = e^{λ(u-1)} satisfies ψ''·ψ/(ψ')² = 1 identically,
    which eliminates all network-structure terms. -/
theorem poisson_closure_is_one (κ : ℚ) (hκ : 0 < κ) :
    (PGFData.poisson κ hκ).closureKappa = 1 :=
  poisson_kappa_eq_one κ hκ

/-! ## Closure exactness -/

/-- **Result 48.** The closure parameter κ equals the dispersion-scaled
    ratio: κ = secondFactorial / mean².

    For the pairwise closure to be exact, κ must be constant as θ varies.
    This happens iff ψ'(u) = α·ψ(u)^κ, which characterises PT distributions.

    For a PT law (κ(θ) constant), the value of κ determines the family:
    * κ < 1: Binomial(n, p) with n = 1/(1-κ); this needs 1/(1-κ) ∈ ℕ, so
      κ ∈ [0, 1) is realised only for κ = (n-1)/n
    * κ = 1: Poisson(λ)
    * κ > 1: NegBin(r, p) with r = 1/(κ-1) -/
theorem closure_kappa_eq_second_over_mean_sq (ψ : PGFData) :
    ψ.closureKappa = ψ.secondFactorial / ψ.mean ^ 2 :=
  rfl

/-- **Result 49.** Some degree record has closure constant κ(1) ≠ 1 and
    dispersion index ≠ 1. A two-moment record cannot show that a law is
    non-PT. For a non-PT law such as ψ(u) = (1 + u²)/2,
    κ(θ) = (1 + θ²)/(2θ²) varies with θ, making the pairwise closure
    approximate rather than exact.

    Witness: the record mean 10, ψ''(1) = 200 (κ(1) = 2, dispersion 11).
    It is the record of the geometric law (NegBin with r = 1), which is PT;
    the bimodal law with 80% degree 4 and 20% degree 34 has mean 10 but
    ψ''(1) = 234. -/
theorem nonPT_closure_varies :
    ∃ (ψ : PGFData), ψ.closureKappa ≠ 1 ∧ ψ.dispersionIndex ≠ 1 := by
  -- mean=10, secondFactorial=200, variance=200+10-100=110
  -- κ = 200/100 = 2, dispersion = 110/10 = 11
  refine ⟨⟨10, 200, by norm_num, by norm_num⟩, ?_, ?_⟩
  · simp [PGFData.closureKappa]; norm_num
  · simp [PGFData.dispersionIndex, PGFData.variance]; norm_num

/-! ## Volz-DSA equivalence for general distributions -/

/-- **Result 50.** The Volz ↔ DSA equivalence holds for ANY degree
    distribution with finite variance — not just PT distributions.

    The variable change x_{SI} = p_I · θ · ψ'(θ) is well-defined and
    invertible whenever θ·ψ'(θ) > 0, which holds for all θ ∈ (0,1]
    when the degree distribution has positive mean.

    The difference is:
    * For PT distributions: Pairwise ≅ DSA ≅ Volz (all three equivalent)
    * For non-PT distributions: DSA ≅ Volz (still equivalent),
      but Pairwise is only approximate

    This is formalised here only as the round trip of Result 45 with the
    scalar factor ψ'(1) = mean degree, so it needs only ψ'(1) ≠ 0 and no
    condition on κ. It is a statement about one linear rescaling, not about
    the ODE systems. -/
theorem volz_dsa_equiv_general (ψ : PGFData) (h : ψ.mean ≠ 0) :
    ∀ (v : VolzState), dsaToVolz (volzToDSA v ψ.mean) ψ.mean h = v := by
  intro v
  exact volz_dsa_roundtrip v ψ.mean h
