# EBCMCategory (legacy Lean 4 library)

**Status: legacy; not cited.** This tree is frozen: no new results are added here, and
vignettes, READMEs and papers must not cite its results (older citations are being removed).
See `NetworkEpiCore.jl/proofs` for the genuine
library (Lean project `NetworkEpi`, namespace `NEP`): a category of dynamical systems, typed
reaction networks and the lift laws. Cite only the names listed in its `CITABLE.txt`.

## What is here

Lean 4 statements about the model algebra of edge-based compartmental models: moment
identities, sign conditions of the EBCM right-hand side, R₀ and threshold algebra,
pairwise-closure weight lemmas, and general lemmas on marginalisation of flows (T1, T4, T5, T7).
They are not theorems about solutions of the ODEs that EdgeBasedModels.jl integrates. Most
statements are about free scalars (a PGF is a record of numbers, a vector field a scalar
expression), and no category or functor is defined.

`Alignment/` is the SA-PASS audit of whether each Lean statement says what its docstring says.
Its results, including an adversarial spot check of the passes, are in `Alignment/SUMMARY.md`,
and the per-claim triage and remediation plan are in `Alignment/TRIAGE.md`.

## Soundness

* The library declares no `axiom`. The former `tree_pair_exactness` (ConvergenceTheorems) was
  inconsistent: it was stated over two unconstrained type classes, so the instances `⟨True⟩`
  and `⟨1⟩` on `Unit` proved `(1 : ℝ) = 0`. Five further axioms were content-free
  (`ebcm_functor_identity`, `ebcm_functor_composition`, `clustering_naturality`,
  `correlated_R0_spectral`, `final_size_CLT`). All six were deleted. The results they named
  are now cited prose with corrected citations and statements.
* `MarginalisationDynamicalGap.no_flow_F3Kℝ` proves that the order-3 Kirkwood witness field has
  no global flow. Hence `trajectoryGap_rate_two_at_witness` holds vacuously.
* `bash scripts/axiom_gate.sh` fails if an `axiom` declaration appears in `EBCMCategory/`, or if
  any declaration of the library (theorems, definitions and auxiliary declarations) depends on
  an axiom other than `propext`, `Quot.sound` and `Classical.choice`. That excludes `sorry` and
  `native_decide`. CI runs it from the repository root (`../.github/workflows/lean.yml`),
  together with the SA-PASS self-test.

## Commands

Run these from this directory. Wrap long commands in `perl -e 'alarm 590; exec @ARGV'`.

```sh
lake build                           # the trusted library EBCMCategory
bash scripts/axiom_gate.sh           # build, then the axiom gate
bash scripts/sa_pass.sh              # SA-PASS report (Alignment/report/sa_pass_report.md)
bash scripts/sa_pass.sh --self-test  # the audit must catch every deliberately misaligned mock
python scripts/sa_reanchor.py        # after a docstring edit: re-anchor claim source lines
```

The generated files `EBCMCategory.md`, `EBCMCategory.html`, `EBCMCategory.pdf` and `build.log`
are stale snapshots from March–April 2026. They cover only 9 of the 21 modules (EpiCategory,
CoarseGrain, GaloisPair, Obstructions, Hierarchy, DynamicLimits, SurvivalBridge, ClosureTheorem,
MessagePassingBridge), and they predate the docstring corrections of WP4b (see below).
Regenerate them with `make mdgen html`, or ignore them.

## Corrected docstrings (WP4b)

Many docstrings, module headers, `categorical_foundations.md` and
`EBCMCategory/MARGINALISATION_SPEC.md` were corrected against the literature (TRIAGE.md P1.4 and
P2): the R₀ of the edge-swapping EBCM depends on the rewiring rate, the multiplex R₀ is a
spectral radius and not a sum, the degree-correlated next-generation matrix is (k − 1)·Q, Erlang
staging changes T, the φ_I equation uses ψ″(θ), the Volz ↔ DSA change of variables carries a
factor θ, `clustering_coefficient` is a triangle stub fraction, and no category, functor or
Galois connection is formalised. Theorems whose statements are tautological or vacuous are
labelled as such in their docstrings; none was deleted or weakened. New theorems state the
corrections where they are cheap to prove, among them local-solution forms of T1, T5 and T7
(`rhs_commute_of_local_traj_commute`, `localGap_hasDerivAt_zero`, `witness_localGap_ge`), which
are not vacuous at the Kirkwood witness, unlike their global-flow forms. The changed claims
need blind re-shadowing before the SA-PASS numbers in `Alignment/SUMMARY.md` apply to them.
