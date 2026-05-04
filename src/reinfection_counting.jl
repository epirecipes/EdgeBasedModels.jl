#=
reinfection_counting.jl

EBM-side reinfection-counting models.

Implements **Approximation 1** of Keeling, House, Cooper & Pellis (2016)
*Systematic Approximations to SIS Dynamics on Networks*,
PLoS Comp Biol 12(12): e1005296.

In a (non-monotone) SIS dynamic the population of "susceptibles"
recovered_from_infection is structurally distinct from the population that
has never been infected. Here we lift the disease state with an extra
integer index `p ∈ {0, …, L}` counting the times a node has been infected
(saturated at `L`).

Two pieces are provided:

1.  `with_reinfection_counting(prog::DiseaseProgression, L)` — structural
    lift of a `DiseaseProgression` to track infection counts. Mirrors the
    NBM API. Useful for inspection or for forwarding to NBM (which fully
    supports lifted SIS dynamics).

2.  `build_sis_reinfection(pgf, β, γ, L)` — a concrete edge-state closure
    for SIS reinfection counting. It tracks node strata
    `S_0, S_1, …, S_L` and `I_1, I_2, …, I_L` together with unordered
    edge densities such as `edge_S_0_I_1` and `edge_S_1_I_2`.

Unlike plain scalar `build_sis`, the aggregate prevalence is not forced to
follow a single theta equation. Infection of `S_p` is driven by the
history-stratified incident edges `S_p-I_q`, and pair dynamics are closed
using the configuration-model excess-degree factor derived from `pgf`.
=#

# ─── Structural lift of a DiseaseProgression ─────────────────────────────────

"""
    with_reinfection_counting(prog::DiseaseProgression, L::Integer)

Return a `DiseaseProgression` whose state has been lifted with an extra
infection-count index `p ∈ {0, …, L}` (saturated at `L`). The returned
progression has:

- `susceptible = :S_0`
- one non-susceptible "post-recovery susceptible" stage `S_p` for each
  `p ∈ {1, …, L}` (with `transmission_rate = 0`)
- for every infectious stage `X` in `prog`, lifted stages
  `X_1, X_2, …, X_L` carrying the same `transmission_rate` as `X`
- infection: `S_p ⟶ X_{min(p+1, L)}` for the entry stage `X` (rate
  determined by the EBCM hazard at solve time, not stored as a transition
  rate)
- recovery: any spontaneous transition `X ⟶ Y` lifts to `X_p ⟶ Y_p` for
  every `p ∈ {1, …, L}`, including the SIS recovery `I ⟶ S` which lifts
  to `I_p ⟶ S_p`.

`L = 0` collapses to a structure isomorphic to the base progression
(susceptible is `:S_0`, single infectious stage `:I_0`, no reinfection
distinction).

# Compatibility
The lifted progression has multiple "S-like" stages (`S_1, …, S_L` carry
no transmission but can be re-infected). The standard Miller EBCM
formulation in `build_edge_system` only handles a single susceptible state,
so the lifted progression is **not** directly accepted by
`build_edge_system`. Use [`build_sis_reinfection`](@ref) for the EBCM
implementation, or forward the lifted progression to
`NodeBasedModels.jl` which supports it natively in its pair-equation
generator.

The lift is provided here primarily for API symmetry with
`NodeBasedModels.with_reinfection_counting` and for inspection/testing.
"""
function with_reinfection_counting(prog::DiseaseProgression, L::Integer)
    L >= 0 || throw(ArgumentError("L must be non-negative"))

    sus = prog.susceptible
    p_lo_sus = 0
    p_lo_inf = min(1, L)  # at L=0 the only bucket is 0; for L≥1 infectious starts at p=1

    new_stages = DiseaseStage[]

    # Lift each non-susceptible stage to p ∈ {p_lo_inf, …, L}.
    # Add post-recovery-susceptible stages S_p for p ∈ {1, …, L} (only when L ≥ 1).
    # Note: the canonical susceptible :S_0 is *not* a DiseaseStage — it is the
    # implicit susceptible declared via DiseaseProgression(susceptible = :S_0).
    for p in 1:L
        push!(new_stages, DiseaseStage(_lifted_name(sus, p); transmission_rate = 0))
    end
    for stage in prog.stages
        for p in p_lo_inf:L
            push!(new_stages, DiseaseStage(_lifted_name(stage.name, p);
                                           transmission_rate = stage.transmission_rate))
        end
    end

    # Lift each transition. Transitions whose target is the susceptible
    # (recovery `I → S`) become `I_p → S_p` for p ≥ 1 and `I_0 → S_0` at L=0.
    new_transitions = DiseaseTransition[]
    for tr in prog.transitions
        from_lo = tr.source == sus ? p_lo_sus : p_lo_inf
        for p in from_lo:L
            from_sym = _lifted_name(tr.source, p)
            # target index: if target is the susceptible, p stays
            # (recovery preserves the count); otherwise spontaneous transition
            # also preserves p (e.g., I_p → R_p in SIRS).
            to_sym = _lifted_name(tr.target, p)
            push!(new_transitions, DiseaseTransition(from_sym, to_sym, tr.rate))
        end
    end

    new_susceptible = _lifted_name(sus, 0)

    # Choose entry: lifted entry is the lowest-p version of the original entry.
    # At L=0 that is `entry_0`; at L≥1 it is `entry_1` (since entry is infectious).
    new_entry = _lifted_name(prog.entry, p_lo_inf)

    return DiseaseProgression(new_stages, new_transitions;
                              susceptible = new_susceptible, entry = new_entry)
end

"""
    with_reinfection_counting(model::StaticConfigurationModel, L::Integer)

Convenience wrapper: lifts the progression of a `StaticConfigurationModel`
via [`with_reinfection_counting`](@ref) and returns a new
`StaticConfigurationModel` with the same `pgf`. See the docstring on the
`DiseaseProgression` method for the EBCM compatibility caveat.
"""
function with_reinfection_counting(model::StaticConfigurationModel, L::Integer)
    StaticConfigurationModel(model.pgf, with_reinfection_counting(model.progression, L))
end

# ─── Edge-state SIS builder with reinfection-count stratification ────────────

"""
    build_sis_reinfection(pgf::DegreePGF, β, γ, L::Integer; name = :sis_reinf_ebm)

Build an edge-state SIS model whose nodes are stratified by infection count
`p ∈ {0, …, L}` (saturated at `L`).

The model tracks

- node strata `S_p` and `I_p`, where infection sends
  `S_p -> I_min(p+1,L)` and recovery sends `I_p -> S_p`;
- unordered edge densities for all stratum pairs, exposed under names such
  as `:edge_S_0_I_1`;
- triples via a configuration-model pair closure with coefficient
  `(ψ''(1)/ψ'(1)) / ψ'(1)`.

Thus aggregate `I(t) = Σ_p I_p` is free to differ from the scalar SIS EBCM:
local edge composition by infection history changes the transient force of
infection.

# Returns
An `EdgeModelSystem` exposing:

- node-stratum variables `:S_0, :S_1, …, :S_L, :I_1, …, :I_L`;
- edge-density variables `:edge_<A>_<B>` for every unordered stratum pair;
- observables `:S`, `:I`, and `:incidence`.

# Notes
- `L = 0` is the unstratified two-state edge model `{S_0, I_0}`.
- For `L = 1` the dynamics distinguish the never-infected susceptibles
  (`S_0`) from the recovered susceptibles (`S_1`).
- Initial conditions use EdgeBasedModels' usual `seed_fraction` convention:
  `seed_fraction` is converted through the PGF as
  `S_0(0)=ψ(1-seed_fraction)`, `I_entry(0)=1-S_0(0)`.
"""
function build_sis_reinfection(pgf::DegreePGF, β, γ, L::Integer;
                               name::Symbol = :sis_reinf_ebm)
    L >= 0 || throw(ArgumentError("L must be non-negative"))

    t = t_nounits
    D = D_nounits

    S_syms = [_lifted_name(:S, p) for p in 0:L]
    I_syms = L == 0 ? [_lifted_name(:I, 0)] : [_lifted_name(:I, p) for p in 1:L]
    states = vcat(S_syms, I_syms)
    order = Dict(state => i for (i, state) in enumerate(states))

    node_vars = Dict{Symbol, Any}()
    for sym in states
        node_vars[sym] = only(@variables $(sym)(t))
    end

    normalize_pair(a::Symbol, b::Symbol) =
        order[a] <= order[b] ? (a, b) : (b, a)

    pair_states = [(states[i], states[j]) for i in eachindex(states) for j in i:length(states)]
    pair_vars = Dict{Tuple{Symbol, Symbol}, Any}()
    for (a, b) in pair_states
        varname = _edge_pair_name(a, b)
        pair_vars[(a, b)] = only(@variables $(varname)(t))
    end

    get_pair(a::Symbol, b::Symbol) = pair_vars[normalize_pair(a, b)]
    pair_factor(a::Symbol, b::Symbol) = a == b ? 2 : 1

    ψ_prime_1 = Symbolics.simplify(_eval_pgf_deriv(pgf, 1, 1))
    ψ_double_1 = Symbolics.simplify(_eval_pgf_deriv(pgf, 2, 1))
    mean_k = _maybe_to_float64(ψ_prime_1)
    mean_k === nothing && throw(ArgumentError(
        "build_sis_reinfection requires a PGF with numeric mean degree for initial edge densities"))
    closure_coeff = Symbolics.simplify((ψ_double_1 / ψ_prime_1) / ψ_prime_1)

    safe_div(num, denom) = ifelse(denom == 0, 0, num / denom)
    triple_closure(a::Symbol, b::Symbol, c::Symbol) =
        Symbolics.simplify(closure_coeff * safe_div(get_pair(a, b) * get_pair(b, c), node_vars[b]))

    infection_transitions = Any[]
    for p in 0:L
        push!(infection_transitions,
              (; from = _lifted_name(:S, p),
                 to = _lifted_name(:I, min(p + 1, L)),
                 rate = β))
    end
    recovery_transitions = Any[]
    for I_sym in I_syms
        p = infection_count_of(I_sym)
        push!(recovery_transitions,
              (; from = I_sym, to = _lifted_name(:S, p), rate = γ))
    end

    eqs = Equation[]

    for state in states
        rhs = 0
        for tr in infection_transitions
            for inf in I_syms
                flux = tr.rate * get_pair(tr.from, inf)
                if state == tr.from
                    rhs -= flux
                elseif state == tr.to
                    rhs += flux
                end
            end
        end
        for tr in recovery_transitions
            flux = tr.rate * node_vars[tr.from]
            if state == tr.from
                rhs -= flux
            elseif state == tr.to
                rhs += flux
            end
        end
        push!(eqs, D(node_vars[state]) ~ Symbolics.simplify(rhs))
    end

    pair_rhs = Dict(state => Num(0) for state in pair_states)

    function add_ext_event!(X::Symbol, Y::Symbol, Z::Symbol, other::Symbol, rate)
        R = rate * triple_closure(Z, X, other)
        src = normalize_pair(X, other)
        tgt = normalize_pair(Y, other)
        pair_rhs[src] -= pair_factor(X, other) * R
        pair_rhs[tgt] += pair_factor(Y, other) * R
    end

    function add_direct_event!(X::Symbol, Y::Symbol, Z::Symbol, rate)
        R = rate * get_pair(X, Z)
        src = normalize_pair(X, Z)
        tgt = normalize_pair(Y, Z)
        pair_rhs[src] -= R
        pair_rhs[tgt] += pair_factor(Y, Z) * R
    end

    function add_recovery_event!(X::Symbol, Y::Symbol, other::Symbol, rate)
        R = rate * get_pair(X, other)
        src = normalize_pair(X, other)
        tgt = normalize_pair(Y, other)
        pair_rhs[src] -= pair_factor(X, other) * R
        pair_rhs[tgt] += pair_factor(Y, other) * R
    end

    for tr in infection_transitions
        X, Y = tr.from, tr.to
        for Z in I_syms
            for other in states
                add_ext_event!(X, Y, Z, other, tr.rate)
            end
            X != Z && add_direct_event!(X, Y, Z, tr.rate)
        end
    end

    for tr in recovery_transitions
        for other in states
            add_recovery_event!(tr.from, tr.to, other, tr.rate)
        end
    end

    for state in pair_states
        push!(eqs, D(pair_vars[state]) ~ Symbolics.simplify(pair_rhs[state]))
    end

    @variables S_obs(t) I_obs(t) incidence_obs(t) phi_I_obs(t)
    S_expr = Symbolics.simplify(_sum_expr(Any[node_vars[s] for s in S_syms]))
    I_expr = Symbolics.simplify(_sum_expr(Any[node_vars[i] for i in I_syms]))
    incidence_expr = Symbolics.simplify(β * _sum_expr(Any[
        get_pair(S_sym, I_sym) for S_sym in S_syms for I_sym in I_syms
    ]))
    phi_I_expr = Symbolics.simplify(_sum_expr(Any[
        get_pair(S_sym, I_sym) for S_sym in S_syms for I_sym in I_syms
    ]) / mean_k)

    push!(eqs, S_obs ~ S_expr)
    push!(eqs, I_obs ~ I_expr)
    push!(eqs, incidence_obs ~ incidence_expr)
    push!(eqs, phi_I_obs ~ phi_I_expr)

    sys = System(eqs, t; name = name)
    simplified = mtkcompile(sys)

    variables = Dict{Symbol, Any}()
    merge!(variables, node_vars)
    for ((a, b), v) in pair_vars
        variables[_edge_pair_name(a, b)] = v
    end

    observables = Dict{Symbol, Any}(
        :S => S_obs,
        :I => I_obs,
        :incidence => incidence_obs,
        :φ_I => phi_I_obs,
    )

    entry_I = L == 0 ? :I_0 : :I_1
    initial_S0(seed_fraction) =
        _to_float64(_cleanup_exp_zero(Symbolics.simplify(_eval_pgf(pgf, 1.0 - seed_fraction))))
    initial_I(seed_fraction) = max(0.0, 1.0 - initial_S0(seed_fraction))
    initial_node(sym::Symbol, seed_fraction) =
        sym == :S_0 ? initial_S0(seed_fraction) :
        sym == entry_I ? initial_I(seed_fraction) : 0.0

    seed_assignments = Any[]
    for sym in states
        push!(seed_assignments, (; var = node_vars[sym],
                                  value = seed_fraction -> initial_node(sym, seed_fraction)))
    end
    for (a, b) in pair_states
        push!(seed_assignments, (; var = pair_vars[(a, b)],
                                  value = seed_fraction -> mean_k *
                                      initial_node(a, seed_fraction) *
                                      initial_node(b, seed_fraction)))
    end

    metadata = Dict{Symbol, Any}(
        :node_strata => Dict(:S => S_syms, :I => I_syms),
        :edge_pairs => Dict(_edge_pair_name(a, b) => (a, b) for (a, b) in pair_states),
        :seed_fraction_assignments => seed_assignments,
    )

    return EdgeModelSystem(simplified, variables, observables, metadata)
end

# ─── Helpers ─────────────────────────────────────────────────────────────────

_lifted_name(base::Symbol, p::Integer) = Symbol(string(base) * "_" * string(p))

_edge_pair_name(a::Symbol, b::Symbol) = Symbol("edge_", string(a), "_", string(b))

"""
    base_compartment_of(name::Symbol) :: Symbol

Recover the base compartment from a lifted name like `:S_3 -> :S`.
Returns `name` itself when no `_<digits>` suffix is present.
"""
function base_compartment_of(name::Symbol)
    m = match(r"^(.+)_(\d+)$", string(name))
    m === nothing ? name : Symbol(m.captures[1])
end

"""
    infection_count_of(name::Symbol) :: Union{Int, Nothing}

Recover the infection count `p` from a lifted name. Returns `nothing` when
the name is not in lifted form.
"""
function infection_count_of(name::Symbol)
    m = match(r"^(.+)_(\d+)$", string(name))
    m === nothing ? nothing : parse(Int, m.captures[2])
end

"""
    reinfection_totals(sys::EdgeModelSystem, sol) :: Dict{Symbol, Vector{Float64}}

Aggregate the lifted stratum variables back into base-compartment totals
(over the saved trajectory). Useful for plotting `S = Σ_p S_p` and
`I = Σ_p I_p` from a solution of [`build_sis_reinfection`](@ref).

Only variables matching the lifted naming convention `:Name_p` (where `p`
is a non-negative integer) are aggregated. Other variables (e.g., `:θ`)
are ignored. The returned vectors have length `length(sol.t)`.
"""
function reinfection_totals(sys::EdgeModelSystem, sol)
    base_groups = Dict{Symbol, Vector{Symbol}}()
    if haskey(sys.metadata, :node_strata)
        for (base, members) in sys.metadata[:node_strata]
            base_groups[base] = collect(members)
        end
    else
        for sym in keys(sys.variables)
            startswith(string(sym), "edge_") && continue
            b = base_compartment_of(sym)
            b === sym && continue  # not in lifted form
            push!(get!(base_groups, b, Symbol[]), sym)
        end
    end

    totals = Dict{Symbol, Vector{Float64}}()
    for (base, members) in base_groups
        acc = zeros(length(sol.t))
        for m in members
            acc .+= sol[sys.variables[m]]
        end
        totals[base] = acc
    end
    return totals
end
