# DataTypes — DegreeCorrelation

Blind-safe vocabulary for shadow authors of group `DegreeCorrelation` (SA-PASS). This file lists the Lean
imports, the shared data types (structures/inductives with their fields) and the operations under
test as **opaque signatures with their docstrings only**. It deliberately contains no theorem
statements, no proofs, no definition bodies and no instance bodies. Where a docstring spells out a
formula, that formula is the author's *intent text*, not a guarantee about the body.

Number types: all quantities are reals (`ℝ`). The module is `noncomputable` and opens `Real`. (Unlike `PGFData` in `EpiCategory`, which is over `ℚ`.)

## (a) Imports

```lean
import EBCMCategory.DegreeCorrelation
import Mathlib.Tactic
```

## (b) Shared data types

Module context (header text): "Formalizes degree-correlated networks where the conditional degree
distribution Q(l|k) = P(neighbor has degree l | ego has degree k) captures assortative or
disassortative mixing. The standard (uncorrelated) configuration model has Q(l|k) = l·p_l/⟨k⟩,
independent of k (neutral mixing)." No object Q is defined in Lean.

### `DegreeMomentData`

```lean
structure DegreeMomentData where
  mean : ℝ             -- ⟨k⟩ = ψ'(1)
  secondMoment : ℝ     -- ⟨k²⟩
  mean_pos : 0 < mean
  secondMoment_pos : 0 < secondMoment
```
Docstring: "Data for a degree distribution with first and second factorial moments."

### `TwoDegreeData`

```lean
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
```
(no docstring on the structure; the section text calls it "Data for a 2×2 assortative mixing matrix")

## (c) Operations under test (opaque signatures + docstrings)

* `DegreeMomentData.secondFactorial : DegreeMomentData → ℝ` — "Second factorial moment ⟨k(k-1)⟩ = ⟨k²⟩ - ⟨k⟩."
* `DegreeMomentData.excessDegree : DegreeMomentData → ℝ` — "Excess degree ⟨k²-k⟩/⟨k⟩ = ψ''(1)/ψ'(1)."
* `uncorrelated_R0 : ℝ → DegreeMomentData → ℝ` — "**Result 80.** R₀ for an uncorrelated network equals
  T times the excess degree." (first argument: the transmissibility T)
* `TwoDegreeData.meanDeg : TwoDegreeData → ℝ` — "Mean degree ⟨k⟩ = k₁·p₁ + k₂·p₂."
* `TwoDegreeData.q1 : TwoDegreeData → ℝ` — "Excess-degree probability q₁ = k₁·p₁/⟨k⟩."
* `TwoDegreeData.q2 : TwoDegreeData → ℝ` — "Excess-degree probability q₂ = k₂·p₂/⟨k⟩."
* `TwoDegreeData.C11 : TwoDegreeData → ℝ` — "**Result 82.** The four entries of the 2×2 mixing matrix."
* `TwoDegreeData.C12 : TwoDegreeData → ℝ`, `TwoDegreeData.C21 : TwoDegreeData → ℝ`,
  `TwoDegreeData.C22 : TwoDegreeData → ℝ` — (no docstrings; the other three entries)
  Section text for the matrix: "C = [[k₁·(r + (1-r)·q₁), k₁·(1-r)·q₂], [k₂·(1-r)·q₁, k₂·(r + (1-r)·q₂)]]
  where q_i = k_i·p_i/⟨k⟩ are the excess-degree probabilities."
* `TwoDegreeData.trC : TwoDegreeData → ℝ` — "Trace of the 2×2 mixing matrix."
* `TwoDegreeData.detC : TwoDegreeData → ℝ` — "Determinant of the 2×2 mixing matrix."
* `TwoDegreeData.secondMom : TwoDegreeData → ℝ` — "Second moment of the two-degree distribution."

## (d) Mathlib notions a faithful formalisation may need

* Real arithmetic (field operations, `^`, `<`, `≤`, `≠`).
* `Matrix (Fin 2) (Fin 2) ℝ`, `!![a, b; c, d]`, `Matrix.trace`, `Matrix.det`, `Matrix.charpoly`,
  `Polynomial.eval`, `Polynomial.roots`, `Matrix.rank`.
* Eigenvalues/spectral radius: `Module.End.HasEigenvalue (Matrix.toLin' M) μ`, `spectrum ℝ M`,
  `spectralRadius ℝ M`.
* `Finset.sum` over degree classes, `PMF ℕ` for general degree distributions.
