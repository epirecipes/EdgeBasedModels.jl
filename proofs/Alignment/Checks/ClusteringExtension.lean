import Alignment.Registry
import Alignment.Shadows.ClusteringExtension

/-!
# Checkers: group `ClusteringExtension`

Checker author (SA-PASS role 3, non-blind). For every claim of `EBCMCategory/ClusteringExtension.lean`
with `status: implemented`, this file holds:

* the `sa_claim` registration (the registry text verbatim, and the registry `impl` list in
  registry order);
* the forward checkers `sa_impl% → Sᵢ` and the backward checker `S₁ → … → Sₙ → sa_impl%`;
* an `sa_fail_*` record wherever a check cannot be proved structurally because the
  implementation says something different from the shadow.

**No bridges are declared.** The blind author asked for bridges from `clustering_coefficient` to
`clusterC` and from `mean_total_degree` to `meanDeg`. Neither is needed, because the shadow
helpers have exactly the trusted bodies:

* `clusterC d := 2 * d.mean_triangle / (2 * d.mean_triangle + d.mean_single)`, the same term as
  the body of `clustering_coefficient d`;
* `meanDeg d := d.mean_single + 2 * d.mean_triangle`, the same term as the body of
  `mean_total_degree d`.

Both are therefore identified by definitional unfolding, which the proofs below use.

The proofs use only: hypotheses; projections of `∧` and `↔`; `Eq.symm`; `show`; `rw [hyp]`
(`Eq.mpr`/`congrArg`); and definitional unfolding of trusted definitions and alignment helpers.
-/

/-! ## clusteringInUnitInterval -/
namespace Alignment.Shadows.ClusteringExtension.clusteringInUnitInterval

sa_claim "ClusteringExtension.clusteringInUnitInterval" group "ClusteringExtension" required
  text "The triangle stub fraction lies in [0,1]."
  impl clustering_in_unit_interval

@[sa_forward "ClusteringExtension.clusteringInUnitInterval" 1]
theorem fwd1 (h : sa_impl% "ClusteringExtension.clusteringInUnitInterval") : S1 :=
  fun d => (h d).1

@[sa_forward "ClusteringExtension.clusteringInUnitInterval" 2]
theorem fwd2 (h : sa_impl% "ClusteringExtension.clusteringInUnitInterval") : S2 :=
  fun d => (h d).2

@[sa_backward "ClusteringExtension.clusteringInUnitInterval"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "ClusteringExtension.clusteringInUnitInterval" :=
  fun d => ⟨s1 d, s2 d⟩

end Alignment.Shadows.ClusteringExtension.clusteringInUnitInterval

/-! ## `ClusteringExtension.R70` -/

namespace Alignment.Shadows.ClusteringExtension.R70

sa_claim "ClusteringExtension.R70" group "ClusteringExtension" required
  text "**Result 70.** Clustering is zero iff there are no triangle edges."
  impl zero_clustering_iff_no_triangles

@[sa_forward "ClusteringExtension.R70" 1]
theorem fwd1 (h : sa_impl% "ClusteringExtension.R70") : S1 :=
  fun d => (h d).mp

@[sa_forward "ClusteringExtension.R70" 2]
theorem fwd2 (h : sa_impl% "ClusteringExtension.R70") : S2 :=
  fun d => (h d).mpr

@[sa_backward "ClusteringExtension.R70"]
theorem bwd (s1 : S1) (s2 : S2) : sa_impl% "ClusteringExtension.R70" :=
  fun d => ⟨s1 d, s2 d⟩

end Alignment.Shadows.ClusteringExtension.R70

/-! ## R71-sec-a -/
namespace Alignment.Shadows.ClusteringExtension.R71_sec_a

sa_claim "ClusteringExtension.R71-sec-a" group "ClusteringExtension" required
  text "Within a triangle, a susceptible node can be infected directly (prob T) or indirectly via the third node. The total probability of infection through a triangle pair is 1 - (1-T)(1-T²) = T + T² - T³ (independent edges)."
  impl triangle_pair_transmission

sa_fail_forward "ClusteringExtension.R71-sec-a" 1 "impl triangle_pair_transmission is only the ring identity 1 - (1-T)(1-T²) = T + T² - T³. It says nothing about the probability that the node is infected through the triangle pair (S1: the sum over the eight transmission outcomes of the direct edge and the two-edge path equals 1 - (1-T)(1-T²)), so impl is weaker than S1."

@[sa_forward "ClusteringExtension.R71-sec-a" 2]
theorem fwd2 (h : sa_impl% "ClusteringExtension.R71-sec-a") : S2 := fun T _ _ => h T

sa_fail_backward "ClusteringExtension.R71-sec-a" "impl states the ring identity for every rational T; S2 states it only for 0 ≤ T ≤ 1 (and S1 is about the outcome sum pTri, which does not give the identity outside [0,1] either). So impl is stronger than the shadows on the domain, and there is no structural route from them to impl at T < 0 or T > 1."

end Alignment.Shadows.ClusteringExtension.R71_sec_a

/-! ## R71-sec-b -/
namespace Alignment.Shadows.ClusteringExtension.R71_sec_b

sa_claim "ClusteringExtension.R71-sec-b" group "ClusteringExtension" required
  text "This is not T(2-T) = 1 - (1-T)², the probability that at least one of two independent edges transmits."
  impl triangle_per_partner

sa_fail_forward "ClusteringExtension.R71-sec-b" 1 "impl triangle_per_partner states T(2 - T) = 2T - T². S1 states T(2 - T) = 1 - (1 - T)². The right-hand sides agree only by ring arithmetic (1 - (1-T)² = 2T - T²), which is not definitional in ℚ for a variable T, so S1 does not follow structurally from h."

sa_fail_forward "ClusteringExtension.R71-sec-b" 2 "impl is a ring identity about T(2 - T). It says nothing about the probability that at least one of two independent edges transmits (S2: the sum over the four outcomes equals 1 - (1-T)²)."

sa_fail_forward "ClusteringExtension.R71-sec-b" 3 "impl states only T(2 - T) = 2T - T². It does not say that the triangle-pair probability 1 - (1-T)(1-T²) differs from T(2 - T) at some T ∈ [0,1] (S3); impl is weaker."

sa_fail_backward "ClusteringExtension.R71-sec-b" "impl (T(2 - T) = 2T - T² for every rational T) does not follow structurally from the shadows. S1 gives T(2 - T) = 1 - (1-T)², and turning 1 - (1-T)² into 2T - T² needs ring. The registered impl is the ring identity of Result 71b, not the text's negative statement (that the triangle probability is not T(2 - T))."

end Alignment.Shadows.ClusteringExtension.R71_sec_b

/-! ## `ClusteringExtension.R71a` -/

namespace Alignment.Shadows.ClusteringExtension.R71a

sa_claim "ClusteringExtension.R71a" group "ClusteringExtension" required
  text "**Result 71a.** Pair transmission through a triangle."
  impl triangle_pair_transmission

@[sa_forward "ClusteringExtension.R71a" 1]
theorem fwd1 (h : sa_impl% "ClusteringExtension.R71a") : S1 :=
  fun x _ _ => h x

sa_fail_backward "ClusteringExtension.R71a" "impl (triangle_pair_transmission) is stronger than the shadow: it states 1 - (1-T)(1-T^2) = T + T^2 - T^3 for every T : ℚ, while S1 (a pair transmission probability, T a probability as in the docstring 'directly (prob T)') states it only for 0 ≤ T ≤ 1. The impl at T outside [0,1] cannot be obtained from S1 structurally: the hypotheses 0 ≤ T and T ≤ 1 are unavailable, and re-proving the identity needs ring."

end Alignment.Shadows.ClusteringExtension.R71a

/-! ## R71b -/
namespace Alignment.Shadows.ClusteringExtension.R71b

sa_claim "ClusteringExtension.R71b" group "ClusteringExtension" required
  text "**Result 71b.** The ring identity T(2 − T) = 2T − T². It is not the per-partner transmissibility in a triangle, which is T + T² − T³ (Result 71a); at T = 1/2 the two are 3/4 and 5/8."
  impl triangle_per_partner

@[sa_forward "ClusteringExtension.R71b" 1]
theorem fwd1 (h : sa_impl% "ClusteringExtension.R71b") : S1 := fun T => h T

sa_fail_forward "ClusteringExtension.R71b" 2 "impl triangle_per_partner is only the ring identity T(2 - T) = 2T - T². It says nothing about the per-partner transmissibility in a triangle (S2: the outcome sum pTri T equals T + T² - T³ on [0,1]), so impl is weaker."

sa_fail_forward "ClusteringExtension.R71b" 3 "impl states only T(2 - T) = 2T - T². It does not say that T(2 - T) differs from the per-partner transmissibility pTri T at some T ∈ [0,1] (the text's 3/4 against 5/8 at T = 1/2); impl is weaker than S3."

@[sa_backward "ClusteringExtension.R71b"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) : sa_impl% "ClusteringExtension.R71b" := fun T => s1 T

end Alignment.Shadows.ClusteringExtension.R71b

/-! ## R73-sec-b -/
namespace Alignment.Shadows.ClusteringExtension.R73_sec_b

sa_claim "ClusteringExtension.R73-sec-b" group "ClusteringExtension" required
  text "The key inequality: for 0 < T ≤ 1, T(1+T)/2 ≤ T, since T(1+T)/2 ≤ T ↔ (1+T)/2 ≤ 1 ↔ T ≤ 1. The per-stub value T(1+T)/2 comes from `clustered_R0` and is not sourced."
  impl triangle_per_edge_le_single

@[sa_forward "ClusteringExtension.R73-sec-b" 1]
theorem fwd1 (h : sa_impl% "ClusteringExtension.R73-sec-b") : S1 :=
  fun T h0 h1 => h T h0 h1

sa_fail_forward "ClusteringExtension.R73-sec-b" 2 "impl triangle_per_edge_le_single states only the implication 0 < T → T ≤ 1 → T(1+T)/2 ≤ T. S2 (0 < T → T(1+T)/2 ≤ T → (1+T)/2 ≤ 1) is the forward direction of the text's first equivalence, which impl does not state; deriving it needs division by T > 0 (ordered-field lemmas)."

sa_fail_forward "ClusteringExtension.R73-sec-b" 3 "S3 (0 < T → (1+T)/2 ≤ 1 → T(1+T)/2 ≤ T) has the hypothesis (1+T)/2 ≤ 1 instead of impl's T ≤ 1. Using impl needs T ≤ 1 from (1+T)/2 ≤ 1, which is ordered-field arithmetic (not structural); the equivalence is not stated by impl."

sa_fail_forward "ClusteringExtension.R73-sec-b" 4 "S4 ((1+T)/2 ≤ 1 → T ≤ 1) is a step of the text's chain of equivalences. impl states only the final implication T ≤ 1 → T(1+T)/2 ≤ T, not this equivalence."

sa_fail_forward "ClusteringExtension.R73-sec-b" 5 "S5 (T ≤ 1 → (1+T)/2 ≤ 1) is a step of the text's chain of equivalences. impl states only T ≤ 1 → T(1+T)/2 ≤ T; the intermediate inequality (1+T)/2 ≤ 1 is not in impl's statement."

@[sa_backward "ClusteringExtension.R73-sec-b"]
theorem bwd (s1 : S1) (_s2 : S2) (_s3 : S3) (_s4 : S4) (_s5 : S5) :
    sa_impl% "ClusteringExtension.R73-sec-b" :=
  fun T h0 h1 => s1 T h0 h1

end Alignment.Shadows.ClusteringExtension.R73_sec_b

/-! ## `ClusteringExtension.R73` -/

namespace Alignment.Shadows.ClusteringExtension.R73

sa_claim "ClusteringExtension.R73" group "ClusteringExtension" required
  text "**Result 73.** Triangle edges contribute less per edge than single edges to R₀."
  impl triangle_per_edge_le_single

@[sa_forward "ClusteringExtension.R73" 1]
theorem fwd1 (h : sa_impl% "ClusteringExtension.R73") : S1 :=
  fun x h0 h1 => h x h0 h1

@[sa_backward "ClusteringExtension.R73"]
theorem bwd (s1 : S1) : sa_impl% "ClusteringExtension.R73" :=
  fun x h0 h1 => s1 x h0 h1

end Alignment.Shadows.ClusteringExtension.R73

/-! ## `ClusteringExtension.meanDegreePositive` -/

namespace Alignment.Shadows.ClusteringExtension.meanDegreePositive

sa_claim "ClusteringExtension.meanDegreePositive" group "ClusteringExtension" required
  text "Mean total degree is positive."
  impl mean_degree_positive

/-- `meanDeg d` is definitionally `mean_total_degree d` (identical bodies). -/
@[sa_forward "ClusteringExtension.meanDegreePositive" 1]
theorem fwd1 (h : sa_impl% "ClusteringExtension.meanDegreePositive") : S1 :=
  fun d => h d

@[sa_backward "ClusteringExtension.meanDegreePositive"]
theorem bwd (s1 : S1) : sa_impl% "ClusteringExtension.meanDegreePositive" :=
  fun d => s1 d

end Alignment.Shadows.ClusteringExtension.meanDegreePositive

/-! ## R75-sec -/
namespace Alignment.Shadows.ClusteringExtension.R75_sec

sa_claim "ClusteringExtension.R75-sec" group "ClusteringExtension" required
  text "For independent Poisson single/triangle edges with means κ_s, κ_t: g(x,y) = exp(κ_s(x-1) + κ_t(y-1)). The triangle stub fraction equals 2κ_t/(2κ_t + κ_s); the clustering coefficient is 2⟨t⟩/⟨k(k−1)⟩ = 2κ_t/((κ_s + 2κ_t)² + 2κ_t)."
  impl poisson_clustering

sa_fail_forward "ClusteringExtension.R75-sec" 1 "impl poisson_clustering is a rational identity about clustering_coefficient. It says nothing about the real PGF g(x,y) = exp(κs(x-1) + κt(y-1)) or its partial derivative g_x(1,1) = κs (S1)."

sa_fail_forward "ClusteringExtension.R75-sec" 2 "impl poisson_clustering says nothing about the real PGF g or its partial derivative g_y(1,1) = κt (S2)."

sa_fail_forward "ClusteringExtension.R75-sec" 3 "S3 holds by unfolding clustering_coefficient on poisNet κs κt (rfl). Using impl instead needs 0 ≤ κt from the shadow's 0 < κt (le_of_lt), which is not structural; a proof without h would be vacuous."

sa_fail_forward "ClusteringExtension.R75-sec" 4 "impl gives only the triangle stub fraction. The clustering coefficient 2⟨t⟩/⟨k(k−1)⟩ = 2κt/((κs + 2κt)² + 2κt) of the Poisson PGF (S4, via derivatives of g) is not in impl's statement."

sa_fail_backward "ClusteringExtension.R75-sec" "impl holds under 0 ≤ κt (including κt = 0), while the shadows' stub-fraction statement S3 assumes 0 < κt. At κt = 0 impl does not follow, so impl is stronger than the shadow set on its domain."

end Alignment.Shadows.ClusteringExtension.R75_sec

/-! ## R75 -/
namespace Alignment.Shadows.ClusteringExtension.R75

sa_claim "ClusteringExtension.R75" group "ClusteringExtension" required
  text "**Result 75.** A Poisson clustered network has triangle stub fraction 2κ_t/(2κ_t+κ_s). Its clustering coefficient is 2κ_t/((κ_s + 2κ_t)² + 2κ_t)."
  impl poisson_clustering

sa_fail_forward "ClusteringExtension.R75" 1 "S1 holds by unfolding clustering_coefficient (it reads only mean_single and mean_triangle, so its value on poisNet κs κt is 2κt/(2κt + κs) by rfl). impl poisson_clustering states the same unfolding for the record ⟨κs, κt, κs⟩ under 0 ≤ κt. A checker that uses h must pass 0 ≤ κt from the shadow's 0 < κt (le_of_lt), which is not structural; without h the proof is vacuous."

sa_fail_forward "ClusteringExtension.R75" 2 "impl is the definitional value of the triangle stub fraction clustering_coefficient. It says nothing about the clustering coefficient 2⟨t⟩/⟨k(k−1)⟩ of the bivariate Poisson PGF (S2, computed from derivatives of exp(κs(x-1) + κt(y-1))). The docstring states this value, but impl's statement does not."

sa_fail_backward "ClusteringExtension.R75" "impl holds under 0 ≤ κt (it includes the triangle-free case κt = 0), while S1 covers only 0 < κt. At κt = 0 impl does not follow from the shadows, so impl is stronger than the shadow set on its domain."

end Alignment.Shadows.ClusteringExtension.R75

/-! ## `ClusteringExtension.R76-sec` -/

namespace Alignment.Shadows.ClusteringExtension.R76_sec

sa_claim "ClusteringExtension.R76-sec" group "ClusteringExtension" required
  text "Replacing 1 triangle with 2 single edges: ⟨s'⟩ = ⟨s⟩+2, ⟨t'⟩ = ⟨t⟩-1 preserves mean total degree."
  impl degree_conversion_preserves_mean

/-- `meanDeg d'` unfolds to `d'.mean_single + 2 * d'.mean_triangle`. Rewriting with the two
replacement hypotheses gives the impl's left-hand side at `s = ⟨s⟩`, `t = ⟨t⟩`. -/
@[sa_forward "ClusteringExtension.R76-sec" 1]
theorem fwd1 (h : sa_impl% "ClusteringExtension.R76-sec") : S1 := by
  intro d d' hs ht
  show d'.mean_single + 2 * d'.mean_triangle = d.mean_single + 2 * d.mean_triangle
  rw [hs, ht]
  exact h d.mean_single d.mean_triangle

sa_fail_backward "ClusteringExtension.R76-sec" "free-scalar abstraction: impl (degree_conversion_preserves_mean) is (s+2) + 2(t-1) = s + 2t for arbitrary s t : ℚ. It does not mention mean_total_degree or ClusteredPGFData. S1 only speaks about pairs d, d' : ClusteredPGFData, which force s = d.mean_single > 0, t = d.mean_triangle ≥ 0 and t - 1 = d'.mean_triangle ≥ 0. So the impl at, e.g., s = -5 or t = 0 cannot be obtained by instantiating S1: no such data exists, and building data from arbitrary s, t needs positivity proofs. Re-proving the identity needs ring."

end Alignment.Shadows.ClusteringExtension.R76_sec

/-! ## `ClusteringExtension.R76` -/

namespace Alignment.Shadows.ClusteringExtension.R76

sa_claim "ClusteringExtension.R76" group "ClusteringExtension" required
  text "**Result 76.** Triangle-to-single conversion preserves mean degree."
  impl degree_conversion_preserves_mean

@[sa_forward "ClusteringExtension.R76" 1]
theorem fwd1 (h : sa_impl% "ClusteringExtension.R76") : S1 := by
  intro d d' hs ht
  show d'.mean_single + 2 * d'.mean_triangle = d.mean_single + 2 * d.mean_triangle
  rw [hs, ht]
  exact h d.mean_single d.mean_triangle

sa_fail_backward "ClusteringExtension.R76" "free-scalar abstraction: impl (degree_conversion_preserves_mean) is the ring identity (s+2) + 2(t-1) = s + 2t for arbitrary s t : ℚ, not a statement about mean_total_degree or a conversion of ClusteredPGFData. S1 quantifies only over data pairs d, d' (⟨s⟩ > 0, ⟨t⟩ ≥ 1 forced by d' being valid). So the impl for s ≤ 0 or t < 1 cannot be obtained by instantiating S1, and building a ClusteredPGFData from arbitrary s, t needs positivity proofs that are unavailable."

end Alignment.Shadows.ClusteringExtension.R76

/-! ## `ClusteringExtension.R69` (registry status `informal`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.ClusteringExtension.R69

sa_claim "ClusteringExtension.R69" group "ClusteringExtension"
  text "**Result 69.** The triangle stub fraction 2⟨t⟩/(2⟨t⟩+⟨s⟩): the fraction of stubs that are triangle stubs (named `clustering_coefficient` for compatibility). It is not the clustering coefficient, which is C = 2⟨t⟩/⟨k(k−1)⟩ with k = s + 2t (the fraction of connected triples that are closed); for independent Poisson single and triangle degrees with means κ_s, κ_t, C = 2κ_t/((κ_s + 2κ_t)² + 2κ_t)."
  impl

end Alignment.Shadows.ClusteringExtension.R69

/-! ## `ClusteringExtension.R72` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.ClusteringExtension.R72

sa_claim "ClusteringExtension.R72" group "ClusteringExtension"
  text "**Result 72.** The scalar `clustered_R0` = T·(⟨s(s-1)⟩/⟨s+2t⟩) + T·(2⟨t⟩/⟨s+2t⟩)·(1+T), kept for compatibility. It is not the R₀ of a clustered network: its triangle term does not scale with the excess triangle degree. For triangle-clustered configuration models, R₀ is the spectral radius of the next-generation matrix over single-edge and triangle-edge infection types (Miller 2009); it is not formalised here."
  impl

end Alignment.Shadows.ClusteringExtension.R72

/-! ## `ClusteringExtension.R73-sec-a` (registry status `missing`: no implementation theorem, so the audit
reports `gap`; registered so that the blind shadow set is attached to its claim) -/
namespace Alignment.Shadows.ClusteringExtension.R73_sec_a

sa_claim "ClusteringExtension.R73-sec-a" group "ClusteringExtension"
  text "Converting a triangle (⟨t⟩→⟨t⟩-1) to two single edges (⟨s⟩→⟨s⟩+2) preserves mean degree ⟨k⟩ = ⟨s⟩+2⟨t⟩. In the scalar formula `clustered_R0`, a triangle's two stubs contribute T·(1+T) in total, i.e. T(1+T)/2 per stub, which is at most the contribution T of a single-edge stub. This is a statement about that formula, not a derivation of R₀ for clustered networks."
  impl

end Alignment.Shadows.ClusteringExtension.R73_sec_a
