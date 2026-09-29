# DataTypes — ClusteringExtension

Blind-safe vocabulary for shadow authors of group `ClusteringExtension` (SA-PASS). This file lists the Lean
imports, the shared data types (structures/inductives with their fields) and the operations under
test as **opaque signatures with their docstrings only**. It deliberately contains no theorem
statements, no proofs, no definition bodies and no instance bodies. Where a docstring spells out a
formula, that formula is the author's *intent text*, not a guarantee about the body.

Number types: all quantities are rationals (`ℚ`).

## (a) Imports

```lean
import EBCMCategory.ClusteringExtension
import Mathlib.Tactic
```

## (b) Shared data types

Module context (header text): "A clustered network is described by g(x,y) = Σ p_{s,t} x^s y^t where s
counts single-edge stubs and t counts triangle-edge stubs."

### `ClusteredPGFData`

```lean
structure ClusteredPGFData where
  mean_single : ℚ      -- ⟨s⟩ = g_x(1,1)
  mean_triangle : ℚ     -- ⟨t⟩ = g_y(1,1)
  excess_single : ℚ     -- ⟨s(s-1)⟩/⟨s+2t⟩ (excess degree through single edges)
  single_pos : 0 < mean_single
  triangle_nonneg : 0 ≤ mean_triangle
```
Docstring: "Data for a clustered network with bivariate PGF g(x,y)." Anonymous-constructor order is
`⟨mean_single, mean_triangle, excess_single, single_pos, triangle_nonneg⟩`. The three numbers are
independent fields (no constraint links `excess_single` to the means).

### `ClusteredR0Data`

```lean
structure ClusteredR0Data extends ClusteredPGFData where
  T : ℚ                -- edge transmissibility
  T_pos : 0 < T
  T_le_one : T ≤ 1
```
Docstring: "Data for R₀ computation in a clustered network."

## (c) Operations under test (opaque signatures + docstrings)

* `clustering_coefficient : ClusteredPGFData → ℚ` — "**Result 69.** Clustering coefficient C = 2⟨t⟩/(2⟨t⟩+⟨s⟩)."
* `clustered_R0 : ClusteredR0Data → ℚ` — "**Result 72.** R₀ for a clustered network:
  R₀ = T·(⟨s(s-1)⟩/⟨s+2t⟩) + T·(2⟨t⟩/⟨s+2t⟩)·(1+T)."
* `mean_total_degree : ClusteredPGFData → ℚ` — "**Result 74.** Mean total degree ⟨k⟩ = ⟨s⟩ + 2⟨t⟩."

## (d) Mathlib notions a faithful formalisation may need

* Arithmetic over `ℚ` (field operations, `^`, `<`, `≤`, `≠`), `Nat.cast`.

* Bivariate PGFs as functions `g : ℝ → ℝ → ℝ`, partial derivatives via `deriv (fun x => g x y)`,
  `Real.exp` for the Poisson case g(x,y) = exp(κ_s(x−1) + κ_t(y−1)).
* Probabilities of transmission events: products/complements of reals in [0,1] (no probability
  space is defined in the library).

## Notes for shadow authors

* Several texts quote a formula for a named network quantity (clustering coefficient, R₀). The
  intended meaning of such a name comes from the text/literature, not from the opaque operation.
