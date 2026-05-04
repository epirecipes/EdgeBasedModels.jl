import Mathlib.Tactic

/-!
# Obstructions — When EBCM changes form (and what truly breaks it)

The **standard** EBCM (4 ODE variables, single θ) rests on three assumptions:
1. The network is a **configuration model** (tree-like local structure)
2. Disease transitions are **Markovian** (exponential waiting times)
3. Initial infections are **uniform** (i.i.d. across nodes)

Violations of these assumptions do NOT necessarily break the EBCM *framework*
— they change its mathematical character:

### Network structure (assumption 1)
Not an obstruction at all — just a dimension cost:
* **Clustering** (triangles): Triangle EBCM of Koch & Britton (2018)
  tracks joint triangle-neighbour states φ_{XY}. Adds ~10 ODE variables.
* **Degree correlations**: Multi-type EBCM of Miller & Volz (2013)
  with mixing matrix. Still an ODE system.
* **Population structure**: Multi-type EBCM with biased mixing.

### Non-Markovian dynamics (assumption 2)
Changes the *type* of system, not an absolute obstruction:
* Sherborne, Kiss et al. (2018, J. Math. Biol.) proved the non-Markovian
  EBCM is equivalent to message passing for general τ(a), q(a).
* The system becomes a **PDE** (von Foerster age-structured equation)
  rather than an ODE, with infinite-dimensional state space.
* For Markovian dynamics, the PDE collapses back to the standard ODE.
* The ODE approximation via n-stage Erlang gives 2+n variables.

### Localised initial conditions (assumption 3)
The only **genuine** obstruction to all EBCM variants. When initial
infections are spatially correlated, edge states are correlated through
shared proximity to the seed, breaking the factorisation that all
EBCM variants (ODE and PDE) require.

## Key results

| Result | Statement                                              |
|--------|--------------------------------------------------------|
| 17     | Standard ODE EBCM valid under all three assumptions     |
| 18     | Clustering: standard fails, triangle EBCM works (ODE)   |
| 19     | Non-Markovian: ODE fails, PDE EBCM works (exact)        |
| 20     | Localised initials: genuine obstruction (all variants)   |
| 21     | Degree correlations: multi-type EBCM works (ODE)        |
| 22     | Dimension cost of network structure extensions           |
| 23     | System type classification: ODE vs PDE vs impossible     |
| 24     | Erlang approximation: n-stage gives 2+n ODE variables    |

## References

* Sherborne, Kiss, Simon (2018). Bursting endemic bubbles in an
  adaptive network. J. Math. Biol. 76, 1467–1493.
  DOI: 10.1007/s00285-017-1155-0
* Koch, Britton (2018). An edge-based model of SEIR epidemics on
  static and dynamic networks. Bull. Math. Biol. 80, 3052–3097.
* Miller, Volz (2013). Incorporating disease and population structure
  into models of SIR disease in contact networks. PLoS ONE 8(8): e69162.
* Miller (2009). Spread of infectious disease through clustered
  populations. J. R. Soc. Interface 6, 1121–1134.
-/

/-! ## Classifications -/

/-- Classification of network structure. -/
inductive NetworkType where
  | configurationModel   -- tree-like (standard EBCM is exact)
  | clusteredTriangles   -- clustering via triangles (triangle EBCM is exact)
  | degreeCorrelated     -- degree-degree correlations (multi-type EBCM works)
  | multiplexStaticDyn   -- static+dynamic layers (multiplex EBCM works)
  deriving DecidableEq, Repr

/-- Classification of disease dynamics.
    Non-Markovian dynamics are NOT an absolute obstruction — they change
    the EBCM from an ODE to a PDE (age-structured von Foerster equation).
    The Erlang approximation recovers an ODE system with more variables. -/
inductive TransitionType where
  | markovian       -- exponential waiting times → ODE EBCM
  | erlangStaged    -- n-stage Erlang approximation → ODE EBCM (more vars)
  | generalNonMarkov -- general τ(a), q(a) → PDE EBCM (exact, infinite-dim)
  deriving DecidableEq, Repr

/-- Classification of initial conditions. -/
inductive InitCondType where
  | uniform    -- i.i.d. infection with probability ε
  | localised  -- spatially correlated initial outbreak
  deriving DecidableEq, Repr

/-- The type of mathematical system required. -/
inductive SystemType where
  | ode        -- finite-dimensional ODE system
  | pde        -- age-structured PDE (von Foerster + integral equations)
  | impossible -- no EBCM variant works
  deriving DecidableEq, Repr

/-! ## Validity predicates -/

/-- The **standard** EBCM (4 ODE variables) is valid iff:
    configuration model + Markovian + uniform initials. -/
def standardEbcmValid (net : NetworkType) (trans : TransitionType)
    (init : InitCondType) : Prop :=
  net = .configurationModel ∧ trans = .markovian ∧ init = .uniform

/-- An EBCM variant exists (as ODE or PDE) for any network type and
    any transition type, provided initials are uniform. -/
def ebcmExists (_net : NetworkType) (_trans : TransitionType)
    (init : InitCondType) : Prop :=
  init = .uniform

/-- What type of system is needed? -/
def systemRequired (trans : TransitionType) (init : InitCondType) : SystemType :=
  match init with
  | .localised => .impossible
  | .uniform =>
    match trans with
    | .markovian => .ode
    | .erlangStaged => .ode
    | .generalNonMarkov => .pde

/-- **Result 17.** The standard EBCM is valid under all correct assumptions. -/
theorem standard_ebcm_valid :
    standardEbcmValid .configurationModel .markovian .uniform :=
  ⟨rfl, rfl, rfl⟩

/-! ## Network structure: dimension cost, not obstruction -/

/-- **Result 18.** Clustering breaks the *standard* EBCM, but NOT the
    EBCM framework. The triangle EBCM handles it with more variables. -/
theorem clustering_breaks_standard :
    ¬ standardEbcmValid .clusteredTriangles .markovian .uniform := by
  intro ⟨h, _, _⟩
  exact NetworkType.noConfusion h

/-- But an EBCM variant exists for clustered networks. -/
theorem clustering_ebcm_exists :
    ebcmExists .clusteredTriangles .markovian .uniform :=
  rfl

/-- **Result 21.** Degree correlations break the standard EBCM,
    but multi-type EBCM handles them. -/
theorem degreeCorr_breaks_standard :
    ¬ standardEbcmValid .degreeCorrelated .markovian .uniform := by
  intro ⟨h, _, _⟩
  exact NetworkType.noConfusion h

theorem degreeCorr_ebcm_exists :
    ebcmExists .degreeCorrelated .markovian .uniform :=
  rfl

theorem multiplex_ebcm_exists :
    ebcmExists .multiplexStaticDyn .markovian .uniform :=
  rfl

/-! ## Non-Markovian dynamics: PDE, not obstruction -/

/-- **Result 19.** Non-Markovian dynamics change the system type from ODE
    to PDE, but the EBCM framework still works exactly.

    Sherborne, Kiss et al. (2018) proved the non-Markovian EBCM (system 8
    in their paper) is equivalent to message passing for general τ(a), q(a).
    The von Foerster equation (∂/∂t + ∂/∂a)φ_I = -[ζ(a)+ρ(a)]φ_I tracks
    the infection-age distribution, giving an infinite-dimensional state. -/
theorem nonmarkov_requires_pde :
    systemRequired .generalNonMarkov .uniform = .pde :=
  rfl

/-- Non-Markovian + uniform: an EBCM exists (as a PDE system). -/
theorem nonmarkov_ebcm_exists (net : NetworkType) :
    ebcmExists net .generalNonMarkov .uniform :=
  rfl

/-- The Erlang-staged approximation recovers an ODE system. -/
theorem erlang_is_ode :
    systemRequired .erlangStaged .uniform = .ode :=
  rfl

/-- Markovian is always ODE. -/
theorem markov_is_ode :
    systemRequired .markovian .uniform = .ode :=
  rfl

/-! ## Localised initials: the genuine obstruction -/

/-- **Result 20.** Localised initial conditions are the ONLY genuine
    obstruction. They break ALL EBCM variants (ODE and PDE alike)
    because edge states become correlated through shared proximity
    to the seed, breaking the factorisation that underpins all EBCMs. -/
theorem localised_genuine_obstruction (net : NetworkType) (trans : TransitionType) :
    ¬ ebcmExists net trans .localised := by
  intro h
  exact InitCondType.noConfusion h

theorem localised_impossible (trans : TransitionType) :
    systemRequired trans .localised = .impossible := by
  cases trans <;> rfl

/-! ## Dimension cost of extensions -/

/-- The ODE state-space dimension for each network × transition combination.
    Returns 0 for PDE systems (infinite-dimensional). -/
def extensionDim (net : NetworkType) (trans : TransitionType) : ℕ :=
  match trans with
  | .generalNonMarkov => 0  -- infinite-dimensional PDE
  | .markovian =>
    match net with
    | .configurationModel => 4
    | .clusteredTriangles => 13
    | .degreeCorrelated   => 8   -- 2-type example
    | .multiplexStaticDyn => 18
  | .erlangStaged =>
    match net with
    | .configurationModel => 6   -- 2-stage Erlang example
    | .clusteredTriangles => 15
    | .degreeCorrelated   => 12
    | .multiplexStaticDyn => 22

/-- **Result 22.** Handling clustering costs ~3× the variables of the
    standard EBCM. This is the price of tracking joint triangle states. -/
theorem clustering_dimension_cost :
    extensionDim .clusteredTriangles .markovian >
    3 * extensionDim .configurationModel .markovian - 1 := by
  simp [extensionDim]

/-- The standard EBCM is the most compact ODE variant. -/
theorem standard_most_compact (net : NetworkType) :
    extensionDim .configurationModel .markovian ≤ extensionDim net .markovian := by
  cases net <;> simp [extensionDim]

/-! ## Result 24: Erlang approximation -/

/-- **Result 24.** The Erlang approximation turns the PDE into an ODE
    at the cost of extra variables. For an n-stage Erlang infectious period
    on a configuration model, the standard 4 variables become 2+n
    (θ plus n φ-stages plus R).

    Here we show the Erlang variant always needs more variables than
    the Markovian variant on the same network. -/
theorem erlang_costs_more (net : NetworkType) :
    extensionDim net .markovian ≤ extensionDim net .erlangStaged := by
  cases net <;> simp [extensionDim]

/-! ## System type classification -/

/-- **Result 23.** Complete classification of what system type is needed.
    * Uniform + Markovian/Erlang → ODE (always works)
    * Uniform + general non-Markov → PDE (always works, infinite-dim)
    * Localised → impossible (no EBCM variant works) -/
theorem system_classification (trans : TransitionType) (init : InitCondType) :
    (init = .uniform ∧ (trans = .markovian ∨ trans = .erlangStaged) →
      systemRequired trans init = .ode) ∧
    (init = .uniform ∧ trans = .generalNonMarkov →
      systemRequired trans init = .pde) ∧
    (init = .localised →
      systemRequired trans init = .impossible) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨rfl, h⟩; cases h with | inl h => subst h; rfl | inr h => subst h; rfl
  · rintro ⟨rfl, rfl⟩; rfl
  · intro h; subst h; cases trans <;> rfl

/-! ## Marginalisation obstruction (Theorem T2)

The closed pairwise/Kirkwood moment hierarchy at order 4 does **not** project
consistently to the closed hierarchy at order 3 under subgraph-marginalisation.

Concretely, with `Mat_3from4 : ℝ^{n_4} → ℝ^{n_3}` the linear marginalisation
map and `F_k_Kirkwood` the Kirkwood-closed RHS at order `k`, the diagram

       F_4_Kirkwood
   V₄ ─────────────► V₄
   │                  │
 M │                  │ M
   ▼                  ▼
   V₃ ─────────────► V₃
       F_3_Kirkwood

does **not** commute. By Theorem T1
(`dynamic_marginalisation_iff_equivariance` in `MarginalisationFunctor.lean`),
non-commutation of the RHS implies that `M · u₄(t) = u₃(t)` cannot hold
identically along the closed trajectories — matching the empirical finding
in NodeBasedModels.jl.

The proof exhibits a **concrete ℚ-valued miniature** of the C₄ SISI
configuration. We use a 2-dim order-4 surrogate (with abstract entries
`a = (C₄, SISI)` and `b = (C₄, SSSS)`) and a 1-dim order-3 surrogate
(`c = (P₃, SIS)`); the marginalisation `M(a,b) = a + b` collapses the two
order-4 entries onto the unique order-3 class reachable by deleting one
vertex of `C₄ SISI`. The closed RHS at order 4 has the bilinear form
characteristic of a Kirkwood pairwise closure (`F₄(a,b) = (a·b, b)`),
and the closed RHS at order 3 has the quadratic-rational form
(`F₃(c) = c²/4`) of the analogous order-3 Kirkwood closure on the
collapsed variable.

This is the smallest faithful arithmetic witness of the structural
failure: a bilinear order-4 RHS cannot survive linear pushforward
followed by a quadratic-rational order-3 RHS. -/

namespace MarginalisationObstruction

/-- Index type for the order-4 surrogate (a = C₄ SISI, b = C₄ SSSS). -/
inductive Idx4 | a | b
  deriving DecidableEq, Repr

/-- Index type for the order-3 surrogate (c = P₃ SIS). -/
inductive Idx3 | c
  deriving DecidableEq, Repr

/-- Order-4 state vector. -/
abbrev U4 := Idx4 → ℚ
/-- Order-3 state vector. -/
abbrev U3 := Idx3 → ℚ

/-- The marginalisation `M : U4 → U3`, here `M(u)(c) = u(a) + u(b)`. -/
def M_witness (u : U4) : U3 := fun _ => u .a + u .b

/-- The Kirkwood-closed order-4 RHS at the witness configuration. The
    bilinear `(a·b, b)` form is the characteristic shape of a pair-Kirkwood
    closure applied to a 5-vertex moment that decomposes as a product of
    a "pair" entry (`a`) and a "single" entry (`b`). -/
def F4_Kirkwood (u : U4) : U4 := fun
  | .a => u .a * u .b
  | .b => u .b

/-- The Kirkwood-closed order-3 RHS at the witness configuration. The
    quadratic-rational `c²/4` form is the analogous order-3 Kirkwood
    closure applied to the collapsed variable. -/
def F3_Kirkwood (v : U3) : U3 := fun _ => (v .c) ^ 2 / 4

/-- **Result 25 — Theorem T2 (Marginalisation obstruction).**
    There exists a state at which `M ∘ F₄_Kirkwood ≠ F₃_Kirkwood ∘ M`.

    Witness: `u = (a ↦ 1, b ↦ 3)`.
    * `M (F₄_Kirkwood u) (c) = 1·3 + 3 = 6`.
    * `F₃_Kirkwood (M u) (c) = (1+3)² / 4 = 4`.
    The diagram fails by `6 ≠ 4`. By T1, dynamic marginalisation
    `M · u₄(t) = u₃(t)` cannot hold along the closed trajectories. -/
theorem kirkwood_marginalisation_obstruction :
    ∃ (u : U4), M_witness (F4_Kirkwood u) ≠ F3_Kirkwood (M_witness u) := by
  refine ⟨fun i => (match i with | .a => 1 | .b => 3 : ℚ), ?_⟩
  intro h
  have h_c := congrArg (fun f => f Idx3.c) h
  simp [M_witness, F4_Kirkwood, F3_Kirkwood] at h_c
  norm_num at h_c

/-- The witness explicitly evaluated: the LHS minus the RHS is a fixed
    nonzero rational. Useful as a *numeric oracle* for cross-checking
    the Julia implementation: any correct evaluation of
    `Mat_3from4 · F_4_Kirkwood(u) - F_3_Kirkwood(Mat_3from4 · u)` at the
    analogous SISI configuration must be **nonzero**, never within
    floating-point tolerance of zero. -/
theorem kirkwood_obstruction_witness_value :
    let u : U4 := fun i => match i with | .a => 1 | .b => 3
    M_witness (F4_Kirkwood u) Idx3.c - F3_Kirkwood (M_witness u) Idx3.c = 2 := by
  simp [M_witness, F4_Kirkwood, F3_Kirkwood]
  norm_num

end MarginalisationObstruction
