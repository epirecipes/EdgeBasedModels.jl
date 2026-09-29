import Alignment.Registry
import EBCMCategory.ClusteringExtension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.BigOperators.Fin

/-!
# Blind shadow sets: group `ClusteringExtension`

Written blind: the author read only the claims' entries in `claims_blind.yaml`,
`Alignment/DataTypes/ClusteringExtension.md`, `Alignment/README.md`, `SA-PASS_SKILL.md`,
`Example/ExampleShadows.lean` and background papers. No theorem statement or definition body of
`EBCMCategory.*` was read.

Conventions used throughout (from the DataTypes file):

* A clustered network is a `ClusteredPGFData` (docstring: "Data for a clustered network with
  bivariate PGF g(x,y)"), with `mean_single = ⟨s⟩ = g_x(1,1)`, `mean_triangle = ⟨t⟩ = g_y(1,1)`
  and `excess_single = ⟨s(s-1)⟩/⟨s+2t⟩`.
* Following the DataTypes note ("the intended meaning of such a name comes from the
  text/literature, not from the opaque operation"), named quantities are written in primitive
  terms from the module's own intent text:
  - clustering coefficient (text of Result 69): `C = 2⟨t⟩/(2⟨t⟩+⟨s⟩)` (`clusterC`);
  - mean total degree (text of Result 74): `⟨k⟩ = ⟨s⟩ + 2⟨t⟩` (`meanDeg`).
  The checker needs (reviewed) bridges from `clustering_coefficient` / `mean_total_degree` to
  these. The one exception is Result 75 (see there): a primitive statement at the level of
  `ClusteredPGFData` would hold by substitution (vacuous), so the data-level reading uses the
  module operation `clustering_coefficient`, and the text's notion is additionally stated at the
  level of the Poisson bivariate PGF.
* Transmissibility `T` and means are rationals, as in the library.

-- AMBIGUITY (group-wide): "clustering coefficient" is read as the module's Result 69 notion
-- C = 2⟨t⟩/(2⟨t⟩+⟨s⟩) (the fraction of edge ends that lie in triangles). The literature
-- notion C = 3·#triangles/#connected triples = 2⟨t⟩/⟨k(k-1)⟩ is NOT used.
-- VOCAB-GAP: the literature clustering coefficient needs ⟨k(k-1)⟩ of the joint distribution,
-- which `ClusteredPGFData` does not carry.

Re-authored blind (second pass, from the current claim texts only): the blocks marked
"(re-authored blind)" near the end of the file (`R69`, `R71-sec-a`, `R71-sec-b`, `R71b`, `R72`,
`R73-sec-a`, `R73-sec-b`, `R75`, `R75-sec`, `clusteringInUnitInterval`). The current texts call
`clustering_coefficient` the *triangle stub fraction* 2⟨t⟩/(2⟨t⟩+⟨s⟩) and state that it is not the
clustering coefficient 2⟨t⟩/⟨k(k−1)⟩; those blocks use the operation for the former and compute
the latter from the bivariate PGF, so the group-wide AMBIGUITY above does not apply to them.
-/

namespace Alignment.Shadows.ClusteringExtension

/-- Clustering coefficient in primitive terms (module text, Result 69):
`C = 2⟨t⟩/(2⟨t⟩+⟨s⟩)`. -/
def clusterC (d : ClusteredPGFData) : ℚ :=
  2 * d.mean_triangle / (2 * d.mean_triangle + d.mean_single)

/-- Mean total degree in primitive terms (module text, Result 74): `⟨k⟩ = ⟨s⟩ + 2⟨t⟩`. -/
def meanDeg (d : ClusteredPGFData) : ℚ :=
  d.mean_single + 2 * d.mean_triangle

/-- The Poisson clustered network with means `κs`, `κt`, as moment data: `⟨s⟩ = κs`,
`⟨t⟩ = κt`, and `excess_single = ⟨s(s-1)⟩/⟨s+2t⟩ = κs²/(κs+2κt)` (for s ~ Poisson(κs),
⟨s(s-1)⟩ = κs²; ⟨s+2t⟩ = κs + 2κt). -/
def poissonNet (κs κt : ℚ) (hs : 0 < κs) (ht : 0 ≤ κt) : ClusteredPGFData :=
  ⟨κs, κt, κs ^ 2 / (κs + 2 * κt), hs, ht⟩

/-- The text's Poisson bivariate PGF `g(x,y) = exp(κ_s(x-1) + κ_t(y-1))`. -/
noncomputable def poissonPGF (κs κt : ℚ) (x y : ℝ) : ℝ :=
  Real.exp ((κs : ℝ) * (x - 1) + (κt : ℝ) * (y - 1))

/-- Mean number of single edges read off a bivariate PGF: `⟨s⟩ = g_x(1,1)`. -/
noncomputable def pgfMeanSingle (g : ℝ → ℝ → ℝ) : ℝ := deriv (fun x => g x 1) 1

/-- Mean number of triangles read off a bivariate PGF: `⟨t⟩ = g_y(1,1)`. -/
noncomputable def pgfMeanTriangle (g : ℝ → ℝ → ℝ) : ℝ := deriv (fun y => g 1 y) 1

/-- The text's clustering coefficient (Result 69 formula) computed from a bivariate PGF:
`C = 2 g_y(1,1) / (2 g_y(1,1) + g_x(1,1))`. -/
noncomputable def pgfClusterC (g : ℝ → ℝ → ℝ) : ℝ :=
  2 * pgfMeanTriangle g / (2 * pgfMeanTriangle g + pgfMeanSingle g)

end Alignment.Shadows.ClusteringExtension

/-! ## `ClusteringExtension.R70`

Blind text: "**Result 70.** Clustering is zero iff there are no triangle edges."

-- AMBIGUITY: "Clustering is zero" read as C = 0 (clustering coefficient); "no triangle edges"
-- read as ⟨t⟩ = 0 (mean number of triangles per node is zero; since t ≥ 0 this is "no node has a
-- triangle"). Both directions of the iff are required. -/
namespace Alignment.Shadows.ClusteringExtension.R70
open Alignment.Shadows.ClusteringExtension

/-- Intended statement: for every clustered network, `C = 0 ↔ ⟨t⟩ = 0`. -/
@[sa_reference "ClusteringExtension.R70"]
def T : Prop := ∀ d : ClusteredPGFData, clusterC d = 0 ↔ d.mean_triangle = 0

/-- S1 (→): zero clustering implies no triangle edges. -/
@[sa_shadow "ClusteringExtension.R70" 1]
def S1 : Prop := ∀ d : ClusteredPGFData, clusterC d = 0 → d.mean_triangle = 0

/-- S2 (←): no triangle edges implies zero clustering. -/
@[sa_shadow "ClusteringExtension.R70" 2]
def S2 : Prop := ∀ d : ClusteredPGFData, d.mean_triangle = 0 → clusterC d = 0

@[sa_ref_forward "ClusteringExtension.R70" 1]
theorem ref_fwd1 : T → S1 := fun t d => (t d).1

@[sa_ref_forward "ClusteringExtension.R70" 2]
theorem ref_fwd2 : T → S2 := fun t d => (t d).2

@[sa_complete "ClusteringExtension.R70"]
theorem complete (s1 : S1) (s2 : S2) : T := fun d => ⟨s1 d, s2 d⟩

end Alignment.Shadows.ClusteringExtension.R70

/-! ## `ClusteringExtension.R71a`

Blind text: "**Result 71a.** Pair transmission through a triangle."

The text is a title only. Minimal honest statement: the result it names, i.e. the pair
transmission probability through a triangle as given in the same docstring (claim R71-sec-a):
`1 - (1-T)(1-T²) = T + T² - T³` for a probability T.
-- AMBIGUITY: title only; content taken from the docstring's preceding sentence. Domain T ∈ [0,1]
-- as in R71-sec-a. -/
namespace Alignment.Shadows.ClusteringExtension.R71a

/-- Intended statement: pair transmission through a triangle is `T + T² - T³`. -/
@[sa_reference "ClusteringExtension.R71a"]
def T : Prop :=
  ∀ T : ℚ, 0 ≤ T → T ≤ 1 → 1 - (1 - T) * (1 - T ^ 2) = T + T ^ 2 - T ^ 3

/-- S1: the pair transmission identity. -/
@[sa_shadow "ClusteringExtension.R71a" 1]
def S1 : Prop :=
  ∀ T : ℚ, 0 ≤ T → T ≤ 1 → 1 - (1 - T) * (1 - T ^ 2) = T + T ^ 2 - T ^ 3

@[sa_ref_forward "ClusteringExtension.R71a" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ClusteringExtension.R71a"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ClusteringExtension.R71a

/-! ## `ClusteringExtension.R73`

Blind text: "**Result 73.** Triangle edges contribute less per edge than single edges to R₀."

-- VOCAB-GAP: "per-edge contribution to R₀" is not an operation; the docstring's values
-- (R73-sec-b) are used: T(1+T)/2 per triangle edge, T per single edge, for 0 < T ≤ 1.
-- AMBIGUITY: "less" read as ≤ (the docstring's own key inequality; the two are equal at T = 1,
-- so a strict reading on 0 < T ≤ 1 would contradict the docstring and is not used). -/
namespace Alignment.Shadows.ClusteringExtension.R73

/-- Intended statement: for every transmissibility 0 < T ≤ 1, `T(1+T)/2 ≤ T`. -/
@[sa_reference "ClusteringExtension.R73"]
def T : Prop := ∀ T : ℚ, 0 < T → T ≤ 1 → T * (1 + T) / 2 ≤ T

/-- S1: per-edge triangle contribution ≤ per-edge single contribution. -/
@[sa_shadow "ClusteringExtension.R73" 1]
def S1 : Prop := ∀ T : ℚ, 0 < T → T ≤ 1 → T * (1 + T) / 2 ≤ T

@[sa_ref_forward "ClusteringExtension.R73" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ClusteringExtension.R73"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ClusteringExtension.R73

/-! ## `ClusteringExtension.meanDegreePositive`

Blind text: "Mean total degree is positive." -/
namespace Alignment.Shadows.ClusteringExtension.meanDegreePositive
open Alignment.Shadows.ClusteringExtension

/-- Intended statement: for every clustered network, `0 < ⟨s⟩ + 2⟨t⟩`. -/
@[sa_reference "ClusteringExtension.meanDegreePositive"]
def T : Prop := ∀ d : ClusteredPGFData, 0 < meanDeg d

/-- S1: the mean total degree is positive (single atomic requirement). -/
@[sa_shadow "ClusteringExtension.meanDegreePositive" 1]
def S1 : Prop := ∀ d : ClusteredPGFData, 0 < meanDeg d

@[sa_ref_forward "ClusteringExtension.meanDegreePositive" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ClusteringExtension.meanDegreePositive"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ClusteringExtension.meanDegreePositive

/-! ## `ClusteringExtension.R76-sec`

Blind text: "Replacing 1 triangle with 2 single edges: ⟨s'⟩ = ⟨s⟩+2, ⟨t'⟩ = ⟨t⟩-1 preserves mean
total degree."

Any clustered network `d'` whose means are obtained from those of `d` by the replacement has the
same mean total degree `⟨k⟩ = ⟨s⟩ + 2⟨t⟩` (Result 74 text). The text says nothing about the
excess degree of `d'`, so it is left arbitrary; `⟨t'⟩ ≥ 0` (hence `⟨t⟩ ≥ 1`) is implied by `d'`
being a clustered network. -/
namespace Alignment.Shadows.ClusteringExtension.R76_sec
open Alignment.Shadows.ClusteringExtension

/-- Intended statement: `⟨s'⟩ = ⟨s⟩+2 ∧ ⟨t'⟩ = ⟨t⟩-1 → ⟨k'⟩ = ⟨k⟩`. -/
@[sa_reference "ClusteringExtension.R76-sec"]
def T : Prop :=
  ∀ d d' : ClusteredPGFData,
    d'.mean_single = d.mean_single + 2 → d'.mean_triangle = d.mean_triangle - 1 →
      meanDeg d' = meanDeg d

/-- S1: the replacement preserves the mean total degree (single atomic requirement). -/
@[sa_shadow "ClusteringExtension.R76-sec" 1]
def S1 : Prop :=
  ∀ d d' : ClusteredPGFData,
    d'.mean_single = d.mean_single + 2 → d'.mean_triangle = d.mean_triangle - 1 →
      meanDeg d' = meanDeg d

@[sa_ref_forward "ClusteringExtension.R76-sec" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ClusteringExtension.R76-sec"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ClusteringExtension.R76_sec

/-! ## `ClusteringExtension.R76`

Blind text: "**Result 76.** Triangle-to-single conversion preserves mean degree."

-- AMBIGUITY: "triangle-to-single conversion" read as the replacement of R76-sec (1 triangle by 2
-- single edges: ⟨s'⟩ = ⟨s⟩+2, ⟨t'⟩ = ⟨t⟩-1); "mean degree" read as the mean total degree
-- ⟨k⟩ = ⟨s⟩ + 2⟨t⟩ (Result 74). -/
namespace Alignment.Shadows.ClusteringExtension.R76
open Alignment.Shadows.ClusteringExtension

/-- Intended statement: triangle-to-single conversion preserves `⟨s⟩ + 2⟨t⟩`. -/
@[sa_reference "ClusteringExtension.R76"]
def T : Prop :=
  ∀ d d' : ClusteredPGFData,
    d'.mean_single = d.mean_single + 2 → d'.mean_triangle = d.mean_triangle - 1 →
      meanDeg d' = meanDeg d

/-- S1: the conversion preserves the mean degree. -/
@[sa_shadow "ClusteringExtension.R76" 1]
def S1 : Prop :=
  ∀ d d' : ClusteredPGFData,
    d'.mean_single = d.mean_single + 2 → d'.mean_triangle = d.mean_triangle - 1 →
      meanDeg d' = meanDeg d

@[sa_ref_forward "ClusteringExtension.R76" 1]
theorem ref_fwd1 : T → S1 := fun t => t

@[sa_complete "ClusteringExtension.R76"]
theorem complete (s1 : S1) : T := s1

end Alignment.Shadows.ClusteringExtension.R76

noncomputable section

/-! ## `ClusteringExtension.R69` (re-authored blind)

Text: "**Result 69.** The triangle stub fraction 2⟨t⟩/(2⟨t⟩+⟨s⟩): the fraction of stubs that are
triangle stubs (named `clustering_coefficient` for compatibility). It is not the clustering
coefficient, which is C = 2⟨t⟩/⟨k(k−1)⟩ with k = s + 2t (the fraction of connected triples that are
closed); for independent Poisson single and triangle degrees with means κ_s, κ_t,
C = 2κ_t/((κ_s + 2κ_t)² + 2κ_t)."

The triangle stub fraction is the operation `clustering_coefficient`. A node with s single edges
and t triangles has k = s + 2t stubs, 2t of them in triangles; the mean stub count is
`mean_total_degree`. For independent Poisson degrees the bivariate PGF is
`g(x,y) = exp(κ_s(x−1) + κ_t(y−1))`; ⟨t⟩ = g_y(1,1) and ⟨k(k−1)⟩ = G''(1) for G(z) = g(z, z²), the
PGF of k = s + 2t. "It is not the clustering coefficient" is read as: in the Poisson case the
triangle stub fraction differs from C for some means (S4). -/
namespace Alignment.Shadows.ClusteringExtension.R69

/-- Poisson clustered network data: `⟨s⟩ = κs`, `⟨t⟩ = κt`, `⟨s(s−1)⟩/⟨s+2t⟩ = κs²/(κs+2κt)`. -/
def poisNet (κs κt : ℚ) (hs : 0 < κs) (ht : 0 < κt) : ClusteredPGFData :=
  ⟨κs, κt, κs ^ 2 / (κs + 2 * κt), hs, ht.le⟩
/-- Bivariate Poisson PGF `g(x,y) = exp(κs(x−1) + κt(y−1))`. -/
def gPois (κs κt : ℚ) (x y : ℝ) : ℝ := Real.exp ((κs : ℝ) * (x - 1) + (κt : ℝ) * (y - 1))
/-- The clustering coefficient `C = 2⟨t⟩/⟨k(k−1)⟩` of a bivariate PGF `g`, with k = s + 2t. -/
def clusteringC (g : ℝ → ℝ → ℝ) : ℝ :=
  2 * deriv (fun y => g 1 y) 1 / iteratedDeriv 2 (fun z => g z (z ^ 2)) 1

@[sa_reference "ClusteringExtension.R69"]
def T : Prop :=
  (∀ d : ClusteredPGFData, clustering_coefficient d =
      2 * d.mean_triangle / (2 * d.mean_triangle + d.mean_single)) ∧
  (∀ d : ClusteredPGFData, clustering_coefficient d = 2 * d.mean_triangle / mean_total_degree d) ∧
  (∀ κs κt : ℚ, 0 < κs → 0 < κt →
      clusteringC (gPois κs κt) = 2 * (κt : ℝ) / (((κs : ℝ) + 2 * κt) ^ 2 + 2 * κt)) ∧
  (∃ (κs κt : ℚ) (hs : 0 < κs) (ht : 0 < κt),
      (clustering_coefficient (poisNet κs κt hs ht) : ℝ) ≠ clusteringC (gPois κs κt))

/-- S1: `clustering_coefficient` is `2⟨t⟩/(2⟨t⟩+⟨s⟩)`. -/
@[sa_shadow "ClusteringExtension.R69" 1]
def S1 : Prop :=
  ∀ d : ClusteredPGFData,
    clustering_coefficient d = 2 * d.mean_triangle / (2 * d.mean_triangle + d.mean_single)
/-- S2: it is the fraction of stubs that are triangle stubs, `2⟨t⟩/⟨k⟩`. -/
@[sa_shadow "ClusteringExtension.R69" 2]
def S2 : Prop :=
  ∀ d : ClusteredPGFData, clustering_coefficient d = 2 * d.mean_triangle / mean_total_degree d
/-- S3: for independent Poisson degrees, `C = 2κt/((κs + 2κt)² + 2κt)`. -/
@[sa_shadow "ClusteringExtension.R69" 3]
def S3 : Prop :=
  ∀ κs κt : ℚ, 0 < κs → 0 < κt →
    clusteringC (gPois κs κt) = 2 * (κt : ℝ) / (((κs : ℝ) + 2 * κt) ^ 2 + 2 * κt)
/-- S4: the triangle stub fraction is not the clustering coefficient. -/
@[sa_shadow "ClusteringExtension.R69" 4]
def S4 : Prop :=
  ∃ (κs κt : ℚ) (hs : 0 < κs) (ht : 0 < κt),
    (clustering_coefficient (poisNet κs κt hs ht) : ℝ) ≠ clusteringC (gPois κs κt)

@[sa_ref_forward "ClusteringExtension.R69" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClusteringExtension.R69" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "ClusteringExtension.R69" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "ClusteringExtension.R69" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "ClusteringExtension.R69"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.ClusteringExtension.R69

/-! ## `ClusteringExtension.R71-sec-a` (re-authored blind)

Text: "Within a triangle, a susceptible node can be infected directly (prob T) or indirectly via the
third node. The total probability of infection through a triangle pair is
1 - (1-T)(1-T²) = T + T² - T³ (independent edges)."

The three edges of the triangle transmit independently with probability T each. The node is
infected iff the direct edge transmits, or both edges of the path through the third node do; the
probability is the sum over the 2³ edge outcomes (DataTypes: products/complements of reals, no
probability space). -/
namespace Alignment.Shadows.ClusteringExtension.R71_sec_a

/-- Probability of an edge outcome: `T` if it transmits, `1 − T` otherwise. -/
def w (T : ℚ) (b : Bool) : ℚ := if b then T else 1 - T
/-- Probability that the node is infected through the triangle pair (direct edge `a`, path
edges `b`, `c`). -/
def pTri (T : ℚ) : ℚ :=
  ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, if (a || (b && c)) = true then w T a * w T b * w T c else 0

@[sa_reference "ClusteringExtension.R71-sec-a"]
def T : Prop :=
  (∀ T : ℚ, 0 ≤ T → T ≤ 1 → pTri T = 1 - (1 - T) * (1 - T ^ 2)) ∧
  (∀ T : ℚ, 0 ≤ T → T ≤ 1 → 1 - (1 - T) * (1 - T ^ 2) = T + T ^ 2 - T ^ 3)

/-- S1: the infection probability through a triangle pair is `1 − (1−T)(1−T²)`. -/
@[sa_shadow "ClusteringExtension.R71-sec-a" 1]
def S1 : Prop := ∀ T : ℚ, 0 ≤ T → T ≤ 1 → pTri T = 1 - (1 - T) * (1 - T ^ 2)
/-- S2: `1 − (1−T)(1−T²) = T + T² − T³`. -/
@[sa_shadow "ClusteringExtension.R71-sec-a" 2]
def S2 : Prop := ∀ T : ℚ, 0 ≤ T → T ≤ 1 → 1 - (1 - T) * (1 - T ^ 2) = T + T ^ 2 - T ^ 3

@[sa_ref_forward "ClusteringExtension.R71-sec-a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClusteringExtension.R71-sec-a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClusteringExtension.R71-sec-a"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClusteringExtension.R71_sec_a

/-! ## `ClusteringExtension.R71-sec-b` (re-authored blind)

Text: "This is not T(2-T) = 1 - (1-T)², the probability that at least one of two independent edges
transmits."

"This" is the triangle-pair infection probability `1 − (1−T)(1−T²)` of the preceding sentence
(R71-sec-a). -/
namespace Alignment.Shadows.ClusteringExtension.R71_sec_b

/-- Probability of an edge outcome. -/
def w (T : ℚ) (b : Bool) : ℚ := if b then T else 1 - T
/-- Probability that at least one of two independent edges transmits. -/
def pTwo (T : ℚ) : ℚ := ∑ a : Bool, ∑ b : Bool, if (a || b) = true then w T a * w T b else 0

@[sa_reference "ClusteringExtension.R71-sec-b"]
def T : Prop :=
  (∀ T : ℚ, T * (2 - T) = 1 - (1 - T) ^ 2) ∧
  (∀ T : ℚ, 0 ≤ T → T ≤ 1 → pTwo T = 1 - (1 - T) ^ 2) ∧
  (∃ T : ℚ, 0 ≤ T ∧ T ≤ 1 ∧ 1 - (1 - T) * (1 - T ^ 2) ≠ T * (2 - T))

/-- S1: `T(2−T) = 1 − (1−T)²`. -/
@[sa_shadow "ClusteringExtension.R71-sec-b" 1]
def S1 : Prop := ∀ T : ℚ, T * (2 - T) = 1 - (1 - T) ^ 2
/-- S2: `1 − (1−T)²` is the probability that at least one of two independent edges transmits. -/
@[sa_shadow "ClusteringExtension.R71-sec-b" 2]
def S2 : Prop := ∀ T : ℚ, 0 ≤ T → T ≤ 1 → pTwo T = 1 - (1 - T) ^ 2
/-- S3: the triangle-pair probability is not `T(2−T)`. -/
@[sa_shadow "ClusteringExtension.R71-sec-b" 3]
def S3 : Prop := ∃ T : ℚ, 0 ≤ T ∧ T ≤ 1 ∧ 1 - (1 - T) * (1 - T ^ 2) ≠ T * (2 - T)

@[sa_ref_forward "ClusteringExtension.R71-sec-b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClusteringExtension.R71-sec-b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "ClusteringExtension.R71-sec-b" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "ClusteringExtension.R71-sec-b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.ClusteringExtension.R71_sec_b

/-! ## `ClusteringExtension.R71b` (re-authored blind)

Text: "**Result 71b.** The ring identity T(2 − T) = 2T − T². It is not the per-partner
transmissibility in a triangle, which is T + T² − T³ (Result 71a); at T = 1/2 the two are 3/4 and
5/8."

The per-partner transmissibility in a triangle is the probability that a partner in a triangle is
infected, directly or through the third node, with independent edges (as in R71-sec-a). The
closed values at T = 1/2 (3/4 and 5/8) are an illustration; the requirement they support is S3. -/
namespace Alignment.Shadows.ClusteringExtension.R71b

/-- Probability of an edge outcome. -/
def w (T : ℚ) (b : Bool) : ℚ := if b then T else 1 - T
/-- Per-partner transmissibility in a triangle (direct edge `a`, path edges `b`, `c`). -/
def pTri (T : ℚ) : ℚ :=
  ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, if (a || (b && c)) = true then w T a * w T b * w T c else 0

@[sa_reference "ClusteringExtension.R71b"]
def T : Prop :=
  (∀ T : ℚ, T * (2 - T) = 2 * T - T ^ 2) ∧
  (∀ T : ℚ, 0 ≤ T → T ≤ 1 → pTri T = T + T ^ 2 - T ^ 3) ∧
  (∃ T : ℚ, 0 ≤ T ∧ T ≤ 1 ∧ T * (2 - T) ≠ pTri T)

/-- S1: the ring identity `T(2 − T) = 2T − T²`. -/
@[sa_shadow "ClusteringExtension.R71b" 1]
def S1 : Prop := ∀ T : ℚ, T * (2 - T) = 2 * T - T ^ 2
/-- S2: the per-partner transmissibility in a triangle is `T + T² − T³`. -/
@[sa_shadow "ClusteringExtension.R71b" 2]
def S2 : Prop := ∀ T : ℚ, 0 ≤ T → T ≤ 1 → pTri T = T + T ^ 2 - T ^ 3
/-- S3: `T(2 − T)` is not the per-partner transmissibility. -/
@[sa_shadow "ClusteringExtension.R71b" 3]
def S3 : Prop := ∃ T : ℚ, 0 ≤ T ∧ T ≤ 1 ∧ T * (2 - T) ≠ pTri T

@[sa_ref_forward "ClusteringExtension.R71b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClusteringExtension.R71b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "ClusteringExtension.R71b" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "ClusteringExtension.R71b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.ClusteringExtension.R71b

/-! ## `ClusteringExtension.R72` (re-authored blind)

Text: "**Result 72.** The scalar `clustered_R0` = T·(⟨s(s-1)⟩/⟨s+2t⟩) + T·(2⟨t⟩/⟨s+2t⟩)·(1+T), kept
for compatibility. It is not the R₀ of a clustered network: its triangle term does not scale with
the excess triangle degree. For triangle-clustered configuration models, R₀ is the spectral radius
of the next-generation matrix over single-edge and triangle-edge infection types (Miller 2009); it
is not formalised here."

`⟨s(s−1)⟩/⟨s+2t⟩` is the field `excess_single`; `⟨s+2t⟩ = ⟨s⟩ + 2⟨t⟩`. "Does not scale with the
excess triangle degree" is read as: the triangle term stays at most T(1+T), however many triangles
a node has (S2). The spectral-radius R₀ is, by the text, not formalised. -/
namespace Alignment.Shadows.ClusteringExtension.R72

@[sa_reference "ClusteringExtension.R72"]
def T : Prop :=
  (∀ d : ClusteredR0Data, clustered_R0 d = d.T * d.excess_single +
      d.T * (2 * d.mean_triangle / (d.mean_single + 2 * d.mean_triangle)) * (1 + d.T)) ∧
  (∀ d : ClusteredR0Data, clustered_R0 d - d.T * d.excess_single ≤ d.T * (1 + d.T))

/-- S1: the formula of `clustered_R0`. -/
@[sa_shadow "ClusteringExtension.R72" 1]
def S1 : Prop :=
  ∀ d : ClusteredR0Data, clustered_R0 d = d.T * d.excess_single +
    d.T * (2 * d.mean_triangle / (d.mean_single + 2 * d.mean_triangle)) * (1 + d.T)
/-- S2: its triangle term is bounded by T(1+T), whatever the triangle degrees. -/
@[sa_shadow "ClusteringExtension.R72" 2]
def S2 : Prop := ∀ d : ClusteredR0Data, clustered_R0 d - d.T * d.excess_single ≤ d.T * (1 + d.T)

@[sa_ref_forward "ClusteringExtension.R72" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClusteringExtension.R72" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClusteringExtension.R72"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClusteringExtension.R72

/-! ## `ClusteringExtension.R73-sec-a` (re-authored blind)

Text: "Converting a triangle (⟨t⟩→⟨t⟩-1) to two single edges (⟨s⟩→⟨s⟩+2) preserves mean degree
⟨k⟩ = ⟨s⟩+2⟨t⟩. In the scalar formula `clustered_R0`, a triangle's two stubs contribute T·(1+T) in
total, i.e. T(1+T)/2 per stub, which is at most the contribution T of a single-edge stub. This is a
statement about that formula, not a derivation of R₀ for clustered networks."

Mean degree is `mean_total_degree`. The per-stub comparison is the inequality
`T(1+T)/2 ≤ T` for a transmissibility `0 < T ≤ 1`. -/
namespace Alignment.Shadows.ClusteringExtension.R73_sec_a

@[sa_reference "ClusteringExtension.R73-sec-a"]
def T : Prop :=
  (∀ d d' : ClusteredPGFData, d'.mean_triangle = d.mean_triangle - 1 →
      d'.mean_single = d.mean_single + 2 → mean_total_degree d' = mean_total_degree d) ∧
  (∀ d : ClusteredPGFData, mean_total_degree d = d.mean_single + 2 * d.mean_triangle) ∧
  (∀ T : ℚ, 0 < T → T ≤ 1 → T * (1 + T) / 2 ≤ T)

/-- S1: converting a triangle into two single edges preserves the mean degree. -/
@[sa_shadow "ClusteringExtension.R73-sec-a" 1]
def S1 : Prop :=
  ∀ d d' : ClusteredPGFData, d'.mean_triangle = d.mean_triangle - 1 →
    d'.mean_single = d.mean_single + 2 → mean_total_degree d' = mean_total_degree d
/-- S2: the mean degree is `⟨s⟩ + 2⟨t⟩`. -/
@[sa_shadow "ClusteringExtension.R73-sec-a" 2]
def S2 : Prop := ∀ d : ClusteredPGFData, mean_total_degree d = d.mean_single + 2 * d.mean_triangle
/-- S3: the per-stub triangle contribution `T(1+T)/2` is at most the single-edge `T`. -/
@[sa_shadow "ClusteringExtension.R73-sec-a" 3]
def S3 : Prop := ∀ T : ℚ, 0 < T → T ≤ 1 → T * (1 + T) / 2 ≤ T

@[sa_ref_forward "ClusteringExtension.R73-sec-a" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClusteringExtension.R73-sec-a" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "ClusteringExtension.R73-sec-a" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2
@[sa_complete "ClusteringExtension.R73-sec-a"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) : T := ⟨s1, s2, s3⟩

end Alignment.Shadows.ClusteringExtension.R73_sec_a

/-! ## `ClusteringExtension.R73-sec-b` (re-authored blind)

Text: "The key inequality: for 0 < T ≤ 1, T(1+T)/2 ≤ T, since T(1+T)/2 ≤ T ↔ (1+T)/2 ≤ 1 ↔ T ≤ 1.
The per-stub value T(1+T)/2 comes from `clustered_R0` and is not sourced."

The chain of equivalences is read for T > 0 (the range of the inequality). The last sentence is a
remark on provenance and is not formalised. -/
namespace Alignment.Shadows.ClusteringExtension.R73_sec_b

@[sa_reference "ClusteringExtension.R73-sec-b"]
def T : Prop :=
  (∀ T : ℚ, 0 < T → T ≤ 1 → T * (1 + T) / 2 ≤ T) ∧
  (∀ T : ℚ, 0 < T → T * (1 + T) / 2 ≤ T → (1 + T) / 2 ≤ 1) ∧
  (∀ T : ℚ, 0 < T → (1 + T) / 2 ≤ 1 → T * (1 + T) / 2 ≤ T) ∧
  (∀ T : ℚ, 0 < T → (1 + T) / 2 ≤ 1 → T ≤ 1) ∧
  (∀ T : ℚ, 0 < T → T ≤ 1 → (1 + T) / 2 ≤ 1)

/-- S1: the key inequality. -/
@[sa_shadow "ClusteringExtension.R73-sec-b" 1]
def S1 : Prop := ∀ T : ℚ, 0 < T → T ≤ 1 → T * (1 + T) / 2 ≤ T
/-- S2: first equivalence, (→). -/
@[sa_shadow "ClusteringExtension.R73-sec-b" 2]
def S2 : Prop := ∀ T : ℚ, 0 < T → T * (1 + T) / 2 ≤ T → (1 + T) / 2 ≤ 1
/-- S3: first equivalence, (←). -/
@[sa_shadow "ClusteringExtension.R73-sec-b" 3]
def S3 : Prop := ∀ T : ℚ, 0 < T → (1 + T) / 2 ≤ 1 → T * (1 + T) / 2 ≤ T
/-- S4: second equivalence, (→). -/
@[sa_shadow "ClusteringExtension.R73-sec-b" 4]
def S4 : Prop := ∀ T : ℚ, 0 < T → (1 + T) / 2 ≤ 1 → T ≤ 1
/-- S5: second equivalence, (←). -/
@[sa_shadow "ClusteringExtension.R73-sec-b" 5]
def S5 : Prop := ∀ T : ℚ, 0 < T → T ≤ 1 → (1 + T) / 2 ≤ 1

@[sa_ref_forward "ClusteringExtension.R73-sec-b" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClusteringExtension.R73-sec-b" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "ClusteringExtension.R73-sec-b" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "ClusteringExtension.R73-sec-b" 4] theorem ref_fwd4 : T → S4 :=
  fun t => t.2.2.2.1
@[sa_ref_forward "ClusteringExtension.R73-sec-b" 5] theorem ref_fwd5 : T → S5 :=
  fun t => t.2.2.2.2
@[sa_complete "ClusteringExtension.R73-sec-b"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) (s5 : S5) : T := ⟨s1, s2, s3, s4, s5⟩

end Alignment.Shadows.ClusteringExtension.R73_sec_b

/-! ## `ClusteringExtension.R75` (re-authored blind)

Text: "**Result 75.** A Poisson clustered network has triangle stub fraction 2κ_t/(2κ_t+κ_s). Its
clustering coefficient is 2κ_t/((κ_s + 2κ_t)² + 2κ_t)."

A Poisson clustered network with means κ_s, κ_t has moment data `⟨s⟩ = κ_s`, `⟨t⟩ = κ_t`,
`⟨s(s−1)⟩/⟨s+2t⟩ = κ_s²/(κ_s+2κ_t)`; its triangle stub fraction is `clustering_coefficient`. Its
clustering coefficient is `2⟨t⟩/⟨k(k−1)⟩` (Result 69) read off the bivariate PGF
`g(x,y) = exp(κ_s(x−1) + κ_t(y−1))`, with ⟨k(k−1)⟩ = G''(1), G(z) = g(z, z²). -/
namespace Alignment.Shadows.ClusteringExtension.R75

/-- Poisson clustered network data. -/
def poisNet (κs κt : ℚ) (hs : 0 < κs) (ht : 0 < κt) : ClusteredPGFData :=
  ⟨κs, κt, κs ^ 2 / (κs + 2 * κt), hs, ht.le⟩
/-- Bivariate Poisson PGF. -/
def gPois (κs κt : ℚ) (x y : ℝ) : ℝ := Real.exp ((κs : ℝ) * (x - 1) + (κt : ℝ) * (y - 1))
/-- Clustering coefficient `2⟨t⟩/⟨k(k−1)⟩` of a bivariate PGF. -/
def clusteringC (g : ℝ → ℝ → ℝ) : ℝ :=
  2 * deriv (fun y => g 1 y) 1 / iteratedDeriv 2 (fun z => g z (z ^ 2)) 1

@[sa_reference "ClusteringExtension.R75"]
def T : Prop :=
  (∀ (κs κt : ℚ) (hs : 0 < κs) (ht : 0 < κt),
      clustering_coefficient (poisNet κs κt hs ht) = 2 * κt / (2 * κt + κs)) ∧
  (∀ κs κt : ℚ, 0 < κs → 0 < κt →
      clusteringC (gPois κs κt) = 2 * (κt : ℝ) / (((κs : ℝ) + 2 * κt) ^ 2 + 2 * κt))

/-- S1: the Poisson network's triangle stub fraction is `2κt/(2κt+κs)`. -/
@[sa_shadow "ClusteringExtension.R75" 1]
def S1 : Prop :=
  ∀ (κs κt : ℚ) (hs : 0 < κs) (ht : 0 < κt),
    clustering_coefficient (poisNet κs κt hs ht) = 2 * κt / (2 * κt + κs)
/-- S2: its clustering coefficient is `2κt/((κs+2κt)² + 2κt)`. -/
@[sa_shadow "ClusteringExtension.R75" 2]
def S2 : Prop :=
  ∀ κs κt : ℚ, 0 < κs → 0 < κt →
    clusteringC (gPois κs κt) = 2 * (κt : ℝ) / (((κs : ℝ) + 2 * κt) ^ 2 + 2 * κt)

@[sa_ref_forward "ClusteringExtension.R75" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClusteringExtension.R75" 2] theorem ref_fwd2 : T → S2 := fun t => t.2
@[sa_complete "ClusteringExtension.R75"]
theorem complete (s1 : S1) (s2 : S2) : T := ⟨s1, s2⟩

end Alignment.Shadows.ClusteringExtension.R75

/-! ## `ClusteringExtension.R75-sec` (re-authored blind)

Text: "For independent Poisson single/triangle edges with means κ_s, κ_t:
g(x,y) = exp(κ_s(x-1) + κ_t(y-1)). The triangle stub fraction equals 2κ_t/(2κ_t + κ_s); the
clustering coefficient is 2⟨t⟩/⟨k(k−1)⟩ = 2κ_t/((κ_s + 2κ_t)² + 2κ_t)."

The means read off g are ⟨s⟩ = g_x(1,1), ⟨t⟩ = g_y(1,1) (S1, S2); the triangle stub fraction of
the network with these means is `clustering_coefficient` (S3); the clustering coefficient
2⟨t⟩/⟨k(k−1)⟩ with ⟨k(k−1)⟩ = G''(1), G(z) = g(z, z²) (S4). -/
namespace Alignment.Shadows.ClusteringExtension.R75_sec

/-- Poisson clustered network data. -/
def poisNet (κs κt : ℚ) (hs : 0 < κs) (ht : 0 < κt) : ClusteredPGFData :=
  ⟨κs, κt, κs ^ 2 / (κs + 2 * κt), hs, ht.le⟩
/-- Bivariate Poisson PGF. -/
def gPois (κs κt : ℚ) (x y : ℝ) : ℝ := Real.exp ((κs : ℝ) * (x - 1) + (κt : ℝ) * (y - 1))
/-- Clustering coefficient `2⟨t⟩/⟨k(k−1)⟩` of a bivariate PGF. -/
def clusteringC (g : ℝ → ℝ → ℝ) : ℝ :=
  2 * deriv (fun y => g 1 y) 1 / iteratedDeriv 2 (fun z => g z (z ^ 2)) 1

@[sa_reference "ClusteringExtension.R75-sec"]
def T : Prop :=
  (∀ κs κt : ℚ, deriv (fun x => gPois κs κt x 1) 1 = κs) ∧
  (∀ κs κt : ℚ, deriv (fun y => gPois κs κt 1 y) 1 = κt) ∧
  (∀ (κs κt : ℚ) (hs : 0 < κs) (ht : 0 < κt),
      clustering_coefficient (poisNet κs κt hs ht) = 2 * κt / (2 * κt + κs)) ∧
  (∀ κs κt : ℚ, 0 < κs → 0 < κt →
      clusteringC (gPois κs κt) = 2 * (κt : ℝ) / (((κs : ℝ) + 2 * κt) ^ 2 + 2 * κt))

/-- S1: `⟨s⟩ = g_x(1,1) = κs`. -/
@[sa_shadow "ClusteringExtension.R75-sec" 1]
def S1 : Prop := ∀ κs κt : ℚ, deriv (fun x => gPois κs κt x 1) 1 = κs
/-- S2: `⟨t⟩ = g_y(1,1) = κt`. -/
@[sa_shadow "ClusteringExtension.R75-sec" 2]
def S2 : Prop := ∀ κs κt : ℚ, deriv (fun y => gPois κs κt 1 y) 1 = κt
/-- S3: the triangle stub fraction is `2κt/(2κt+κs)`. -/
@[sa_shadow "ClusteringExtension.R75-sec" 3]
def S3 : Prop :=
  ∀ (κs κt : ℚ) (hs : 0 < κs) (ht : 0 < κt),
    clustering_coefficient (poisNet κs κt hs ht) = 2 * κt / (2 * κt + κs)
/-- S4: the clustering coefficient is `2κt/((κs+2κt)² + 2κt)`. -/
@[sa_shadow "ClusteringExtension.R75-sec" 4]
def S4 : Prop :=
  ∀ κs κt : ℚ, 0 < κs → 0 < κt →
    clusteringC (gPois κs κt) = 2 * (κt : ℝ) / (((κs : ℝ) + 2 * κt) ^ 2 + 2 * κt)

@[sa_ref_forward "ClusteringExtension.R75-sec" 1] theorem ref_fwd1 : T → S1 := fun t => t.1
@[sa_ref_forward "ClusteringExtension.R75-sec" 2] theorem ref_fwd2 : T → S2 := fun t => t.2.1
@[sa_ref_forward "ClusteringExtension.R75-sec" 3] theorem ref_fwd3 : T → S3 := fun t => t.2.2.1
@[sa_ref_forward "ClusteringExtension.R75-sec" 4] theorem ref_fwd4 : T → S4 := fun t => t.2.2.2
@[sa_complete "ClusteringExtension.R75-sec"]
theorem complete (s1 : S1) (s2 : S2) (s3 : S3) (s4 : S4) : T := ⟨s1, s2, s3, s4⟩

end Alignment.Shadows.ClusteringExtension.R75_sec

/-! ## `ClusteringExtension.clusteringInUnitInterval` (re-authored blind)

Text: "The triangle stub fraction lies in [0,1]."

The triangle stub fraction is the operation `clustering_coefficient`. -/
namespace Alignment.Shadows.ClusteringExtension.clusteringInUnitInterval

@[sa_reference "ClusteringExtension.clusteringInUnitInterval"]
def T : Prop :=
  ∀ d : ClusteredPGFData, 0 ≤ clustering_coefficient d ∧ clustering_coefficient d ≤ 1

/-- S1: the triangle stub fraction is nonnegative. -/
@[sa_shadow "ClusteringExtension.clusteringInUnitInterval" 1]
def S1 : Prop := ∀ d : ClusteredPGFData, 0 ≤ clustering_coefficient d
/-- S2: the triangle stub fraction is at most one. -/
@[sa_shadow "ClusteringExtension.clusteringInUnitInterval" 2]
def S2 : Prop := ∀ d : ClusteredPGFData, clustering_coefficient d ≤ 1

@[sa_ref_forward "ClusteringExtension.clusteringInUnitInterval" 1] theorem ref_fwd1 : T → S1 :=
  fun t d => (t d).1
@[sa_ref_forward "ClusteringExtension.clusteringInUnitInterval" 2] theorem ref_fwd2 : T → S2 :=
  fun t d => (t d).2
@[sa_complete "ClusteringExtension.clusteringInUnitInterval"]
theorem complete (s1 : S1) (s2 : S2) : T := fun d => ⟨s1 d, s2 d⟩

end Alignment.Shadows.ClusteringExtension.clusteringInUnitInterval

end
