import Alignment.Registry
import Alignment.Shadows.EpiCategory

/-!
# Checkers: group `EpiCategory`

Checker author (SA-PASS role 3, non-blind). For every claim of `EBCMCategory/EpiCategory.lean`
with `status: implemented` this file holds the `sa_claim` registration (verbatim registry text,
registry `impl` list in registry order), the forward checkers `sa_impl% → Sᵢ` and the backward
checker `S₁ → … → Sₙ → sa_impl%`.

No bridges are declared. The blind shadows state every claim with the trusted operations
themselves (`PGFData.excessDegree`, `PGFData.variance`, `PGFData.poisson`,
`SIRParams.transmissibility`, `nodeModel`, `edgeModel` and the `Preorder EpiModel` instance), so
no trusted definition has to be identified with a differently-phrased notion. Every check below
needs only the hypothesis, application and definitional unfolding:

* `(PGFData.poisson κ hκ).mean` reduces to `κ` (structure-literal projection), which covers the
  S2 readings of R1, R2 and R4;
* `nodeModel p κ ≤ edgeModel p ψ` unfolds to `(nodeModel p κ).dim ≤ (edgeModel p ψ).dim`, i.e.
  `3 ≤ 4`, for every `κ`. So R3's S2 (any `κ`) is definitionally the implementation's statement
  at `κ = ψ.mean`.

No failures are recorded. The definitions themselves are not checked by these shadows (the
shadow author says so). The registry's `impl_note`s record the remaining semantic caveats: R3's
refinement is only `3 ≤ 4` on the dimension proxy, and R4's agreement holds by construction of
`nodeModel.R0 := T·κ`.
-/

/-! ## `EpiCategory.R1` -/

namespace Alignment.Shadows.EpiCategory.R1

sa_claim "EpiCategory.R1" group "EpiCategory" required
  text "**Result 1.** For Poisson, the excess degree equals the mean degree."
  impl PGFData.poisson_excess_eq_mean

/-- S1 is the implementation's statement. -/
@[sa_forward "EpiCategory.R1" 1]
theorem fwd1 (h : sa_impl% "EpiCategory.R1") : S1 :=
  fun κ hκ => h κ hκ

/-- `(PGFData.poisson κ hκ).mean` reduces to `κ`, so the same term proves S2. -/
@[sa_forward "EpiCategory.R1" 2]
theorem fwd2 (h : sa_impl% "EpiCategory.R1") : S2 :=
  fun κ hκ => h κ hκ

@[sa_backward "EpiCategory.R1"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "EpiCategory.R1" :=
  fun κ hκ => s1 κ hκ

end Alignment.Shadows.EpiCategory.R1

/-! ## `EpiCategory.R2` -/

namespace Alignment.Shadows.EpiCategory.R2

sa_claim "EpiCategory.R2" group "EpiCategory" required
  text "**Result 2.** For Poisson, the variance equals the mean (equidispersion)."
  impl PGFData.poisson_variance_eq_mean

/-- S1 is the implementation's statement. -/
@[sa_forward "EpiCategory.R2" 1]
theorem fwd1 (h : sa_impl% "EpiCategory.R2") : S1 :=
  fun κ hκ => h κ hκ

/-- `(PGFData.poisson κ hκ).mean` reduces to `κ`, so the same term proves S2. -/
@[sa_forward "EpiCategory.R2" 2]
theorem fwd2 (h : sa_impl% "EpiCategory.R2") : S2 :=
  fun κ hκ => h κ hκ

@[sa_backward "EpiCategory.R2"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "EpiCategory.R2" :=
  fun κ hκ => s1 κ hκ

end Alignment.Shadows.EpiCategory.R2

/-! ## `EpiCategory.transmissibilityPos` -/

namespace Alignment.Shadows.EpiCategory.transmissibilityPos

sa_claim "EpiCategory.transmissibilityPos" group "EpiCategory" required
  text "Transmissibility is positive."
  impl SIRParams.transmissibility_pos

@[sa_forward "EpiCategory.transmissibilityPos" 1]
theorem fwd1 (h : sa_impl% "EpiCategory.transmissibilityPos") : S1 :=
  fun p => h p

@[sa_backward "EpiCategory.transmissibilityPos"]
theorem bwd (s1 : S1) : sa_impl% "EpiCategory.transmissibilityPos" :=
  fun p => s1 p

end Alignment.Shadows.EpiCategory.transmissibilityPos

/-! ## `EpiCategory.transmissibilityLtOne` -/

namespace Alignment.Shadows.EpiCategory.transmissibilityLtOne

sa_claim "EpiCategory.transmissibilityLtOne" group "EpiCategory" required
  text "Transmissibility is less than 1."
  impl SIRParams.transmissibility_lt_one

@[sa_forward "EpiCategory.transmissibilityLtOne" 1]
theorem fwd1 (h : sa_impl% "EpiCategory.transmissibilityLtOne") : S1 :=
  fun p => h p

@[sa_backward "EpiCategory.transmissibilityLtOne"]
theorem bwd (s1 : S1) : sa_impl% "EpiCategory.transmissibilityLtOne" :=
  fun p => s1 p

end Alignment.Shadows.EpiCategory.transmissibilityLtOne

/-! ## `EpiCategory.R3` -/

namespace Alignment.Shadows.EpiCategory.R3

sa_claim "EpiCategory.R3" group "EpiCategory" required
  text "**Result 3.** The edge model always refines the node model."
  impl edge_refines_node

/-- S1 is the implementation's statement. -/
@[sa_forward "EpiCategory.R3" 1]
theorem fwd1 (h : sa_impl% "EpiCategory.R3") : S1 :=
  fun p ψ => h p ψ

/-- `nodeModel p κ ≤ edgeModel p ψ` unfolds to `(nodeModel p κ).dim ≤ (edgeModel p ψ).dim`, and
`(nodeModel p κ).dim` reduces to `3` for every `κ`. So the goal at an arbitrary `κ` is
definitionally the implementation's statement at `κ = ψ.mean`, and `h p ψ` proves it. -/
@[sa_forward "EpiCategory.R3" 2]
theorem fwd2 (h : sa_impl% "EpiCategory.R3") : S2 :=
  fun p _κ ψ => h p ψ

@[sa_backward "EpiCategory.R3"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "EpiCategory.R3" :=
  fun p ψ => s1 p ψ

end Alignment.Shadows.EpiCategory.R3

/-! ## `EpiCategory.R4` -/

namespace Alignment.Shadows.EpiCategory.R4

sa_claim "EpiCategory.R4" group "EpiCategory" required
  text "**Result 4.** For Poisson networks, both models compute the same R₀."
  impl poisson_R0_agree

/-- S1 is the implementation's statement. -/
@[sa_forward "EpiCategory.R4" 1]
theorem fwd1 (h : sa_impl% "EpiCategory.R4") : S1 :=
  fun p κ hκ => h p κ hκ

/-- `(PGFData.poisson κ hκ).mean` reduces to `κ`, so
`nodeModel p (PGFData.poisson κ hκ).mean` is definitionally `nodeModel p κ`. -/
@[sa_forward "EpiCategory.R4" 2]
theorem fwd2 (h : sa_impl% "EpiCategory.R4") : S2 :=
  fun p κ hκ => h p κ hκ

@[sa_backward "EpiCategory.R4"]
theorem bwd (s1 : S1) (_s2 : S2) : sa_impl% "EpiCategory.R4" :=
  fun p κ hκ => s1 p κ hκ

end Alignment.Shadows.EpiCategory.R4

/-! ## dispersionIndexEqOneIff

S3 is the projection `secondFactorial` of the equation given by `(h ψ).mp`. For S4 the goal is
rewritten with `ψ''(1) = ψ'(1)²`, which turns it into the dispersion index of the Poisson record
of mean `ψ'(1)`; that record has dispersion index 1 by `(h (poisson …)).mpr rfl`. -/
namespace Alignment.Shadows.EpiCategory.dispersionIndexEqOneIff

sa_claim "EpiCategory.dispersionIndexEqOneIff" group "EpiCategory" required
  text "A `PGFData` record has dispersion index 1 iff it is the Poisson record of its own mean, i.e. iff ψ''(1) = ψ'(1)²."
  impl PGFData.dispersionIndex_eq_one_iff

@[sa_forward "EpiCategory.dispersionIndexEqOneIff" 1]
theorem fwd1 (h : sa_impl% "EpiCategory.dispersionIndexEqOneIff") : S1 := fun ψ => (h ψ).mp

@[sa_forward "EpiCategory.dispersionIndexEqOneIff" 2]
theorem fwd2 (h : sa_impl% "EpiCategory.dispersionIndexEqOneIff") : S2 := fun ψ => (h ψ).mpr

@[sa_forward "EpiCategory.dispersionIndexEqOneIff" 3]
theorem fwd3 (h : sa_impl% "EpiCategory.dispersionIndexEqOneIff") : S3 :=
  fun ψ hd => congrArg PGFData.secondFactorial ((h ψ).mp hd)

@[sa_forward "EpiCategory.dispersionIndexEqOneIff" 4]
theorem fwd4 (h : sa_impl% "EpiCategory.dispersionIndexEqOneIff") : S4 := by
  intro ψ hsf
  unfold PGFData.dispersionIndex PGFData.variance
  rw [hsf]
  exact (h (PGFData.poisson ψ.mean ψ.mean_pos)).mpr rfl

@[sa_backward "EpiCategory.dispersionIndexEqOneIff"]
theorem bwd (s1 : S1) (s2 : S2) (_s3 : S3) (_s4 : S4) :
    sa_impl% "EpiCategory.dispersionIndexEqOneIff" :=
  fun ψ => ⟨s1 ψ, s2 ψ⟩

end Alignment.Shadows.EpiCategory.dispersionIndexEqOneIff

/-! ## `EpiCategory.dispersionIndexOneIffPoisson` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.EpiCategory.dispersionIndexOneIffPoisson

sa_claim "EpiCategory.dispersionIndexOneIffPoisson" group "EpiCategory"
  text "Index of dispersion: σ²/κ. Poisson ⇒ dispersion index 1 (`poisson_dispersion_eq_one`). The converse is false for degree distributions: the law with P(0) = P(2) = 1/2, ψ(u) = (1 + u²)/2, has mean 1 and variance 1 but is not Poisson."
  impl

end Alignment.Shadows.EpiCategory.dispersionIndexOneIffPoisson

/-! ## `EpiCategory.header.refinementPreorder` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.EpiCategory.header_refinementPreorder

sa_claim "EpiCategory.header.refinementPreorder" group "EpiCategory"
  text "The only order is the preorder `M₁ ≤ M₂ iff M₁.dim ≤ M₂.dim`; \"refinement\" below means \"has at least as many state variables\" and nothing more."
  impl

end Alignment.Shadows.EpiCategory.header_refinementPreorder
