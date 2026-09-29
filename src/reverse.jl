# Owner: WP18 (DESIGN_NetworkEpiCore.md §A.3, §D.5 M1–M6, Λ1, calibrations, "the two senses of
# back to mass action"; §J; work package in §G.2).
#
# The reverse maps of an edge-based (EB) system: which mass-action (or other reaction-network)
# dynamics reproduce the EB dynamics, each returned with its semiconjugacy π (a morphism of Dyn,
# checked by NetworkEpiCore's `verify`) and an honest exactness label:
#
#   form = :exact       M1 well-mixed unit (WellMixed(κ): MA(c_κ P) on S and x_X)
#                       M2 Poisson isomorphism (Poisson(μ): MA(D_μ P), edge copies Φ_X and node
#                          copies X; the node copies are the prevalences)
#                       M4 power-law kinetics (Poisson-type ψ' = αψ^κ, κ ≠ 1)
#   form = :edge        M3 Rempała's quotient (Poisson(μ): MA(E_μ P) on the model's own species;
#                          for SIR MA(β = μτ, γ + τ), whose "I" is the edge variable φ_I)
#   form = :general     M5 general kinetics in an auxiliary Θ (any ψ; an encoding, always exact)
#   form = :limit       Λ1 the dense limit MA(c_⟨k⟩ P) (Poisson μ → ∞ with μτ fixed: O(1/μ));
#                          labelled :limit and expected to fail `verify`
#   form = :calibrated  an R₀- (or growth-, final-size-) matched MA; labelled :calibration (F6)
#
# plus `pairwise_image` (M6: EB → the S-anchored pairwise model PW^S with the closure
# K_ψ = ψψ''/ψ'², exact for every ψ), `as_reaction_system` (the reaction network of a form) and
# the registration of M1–M6 as NetworkEpiCore `NaturalTransformation`s (in `__init__`).
#
# The old `to_mass_action` map MA(τψ''(1)/ψ'(1), γ) (verified issue E08) is none of these: it
# keeps γ where Rempała's quotient needs γ + τ, and `verify` rejects it with the residual −τφ_I in
# dI/dt (test/suites/reverse.jl). The migration errors of `to_mass_action` and `compare_models`
# live in src/deprecated.jl.
#
# Every map starts from the uncompiled EB field `symbolic_ode(sys)` (metadata[:raw]); a compact
# (M9) system is first embedded into its expanded coordinates on the invariant set
# W = {τφ_R + γθ = γ}, so its maps are restrictions (kind :semiconjugacy).
#
# This file defines EdgeBasedModels' `__init__` (the registration of the natural
# transformations, which must happen at load time, not while the package precompiles).
#
# Include order: last but one (after the lifts, which it reads through their metadata, and before
# deprecated.jl).

export MassActionImage, as_reaction_system, pairwise_image

"""
    MASS_ACTION_FORMS

The forms of [`mass_action`](@ref)`(sys::EdgeModelSystem; form)`, the senses of "back to mass
action" (design §D.5): `:exact` (M1, M2, M4), `:edge` (M3, Rempała's quotient), `:general` (M5),
`:limit` (Λ1) and `:calibrated` (a calibration, F6).
"""
const MASS_ACTION_FORMS = (:exact, :edge, :general, :limit, :calibrated)

# ---------------------------------------------------------------------------------------------
# The image type
# ---------------------------------------------------------------------------------------------

"""
    MassActionImage

The result of [`mass_action`](@ref)`(sys::EdgeModelSystem; form)`: a reaction network whose
dynamics are the image of the edge-based dynamics of `sys` under a map π, with the evidence of
how exact that is. Fields:

- `model::Union{Nothing,ContactModel}`: the target as a `ContactModel` read as mass action
  (κ = 1, `PerContact`), when the target is one: c_κ P (`:exact` on `WellMixed`, `:limit`,
  `:calibrated`) or Rempała's E_μ P (`:edge`); `nothing` for the edge doubling D_μ, power-law
  and general kinetics, which are not contact models;
- `reaction_data::ReactionNetworkData`: the target as a general reaction network (any
  stoichiometry, rate laws where the kinetics are not mass action); `Catalyst.ReactionSystem`
  converts it (NetworkEpiCore's Catalyst extension);
- `ode::SymbolicODE`: its ODE, `mass_action(reaction_data)` (also `morphism.target`);
- `morphism::Semiconjugacy`: π from `symbolic_ode(sys)` to `ode`; `verify(img.morphism)` checks
  it and `pushforward(img, sys, sol, tgrid)` maps an edge-based solution to the target
  coordinates;
- `exactness::Symbol`: `:exact` (a morphism of Dyn), `:limit` or `:calibration` (not
  morphisms: `verify` fails, and they are labelled so);
- `notes::Vector{String}`: what the target's species mean (for example that Rempała's "I" is the
  edge variable φ_I, not the prevalence) and where the claim comes from;
- `form::Symbol`: the form asked for (one of [`MASS_ACTION_FORMS`](@ref));
- `kind::Symbol`: the kinetics of the target, `:mass_action`, `:power_law` (M4; mass action iff
  κ = 1) or `:general` (M5).
"""
struct MassActionImage
    model::Union{Nothing,ContactModel}
    reaction_data::ReactionNetworkData
    ode::SymbolicODE
    morphism::Semiconjugacy
    exactness::Symbol
    notes::Vector{String}
    form::Symbol
    kind::Symbol
end

Base.show(io::IO, img::MassActionImage) =
    print(io, "MassActionImage(:", img.form, ", ", img.morphism.name, " → :", img.ode.name,
          "; kind = :", img.kind, ", exactness = :", img.exactness, ")")

function Base.show(io::IO, ::MIME"text/plain", img::MassActionImage)
    print(io, "MassActionImage  form = :", img.form, "  (", img.morphism.name, ", kinetics :",
          img.kind, ", exactness :", img.exactness, ")")
    print(io, "\n  target  ")
    show(io, MIME"text/plain"(), img.reaction_data)
    for (k, v) in img.morphism.map
        print(io, "\n  π       ", _symname(k), " = ", _rate_text(v))
    end
    for n in img.notes                    # the notes the reaction data does not already show
        n in img.reaction_data.provenance.assumptions || print(io, "\n  note    ", n)
    end
end

# ---------------------------------------------------------------------------------------------
# The source: an edge-based field and its coordinates
# ---------------------------------------------------------------------------------------------

# What the reverse maps read from a lifted system (or from the per-reaction table of a model on a
# network): the source field and, as expressions in its states, θ, ξ (1 without exits), the seed
# factor q and the edge and node coordinates φ_X, pop_X of every non-susceptible species X
# (the model's species, then the removal sinks). For a compact (M9) system φ and pop are the
# embedding of its two states into the expanded coordinates.
struct _ReverseSource
    ode::SymbolicODE
    cm::ContactModel
    net::NetworkDescriptor
    closure::Symbol
    compact::Bool
    lm::_LiftModel
    s::Symbol
    nodes::Vector{Symbol}              # non-susceptible species of the model (model order)
    sinks::Vector{Symbol}              # the auto-added removal sinks (§J.2)
    exits::Bool
    θ::Any
    ξ::Any
    q::Any
    φ::Dict{Symbol,Any}
    pop::Dict{Symbol,Any}
end

function _reverse_source(sys::EdgeModelSystem, fname::AbstractString)
    md = sys.metadata
    get(md, :kind, :unknown) === :assembled && haskey(md, :raw) || throw(ArgumentError(
        "$fname: this edge-based system was not built by edge_based (metadata[:kind] = " *
        ":$(get(md, :kind, :unknown))) and records no uncompiled vector field; lift the model " *
        "with edge_based(model, net) onto a ConfigurationNetwork or a WellMixed network"))
    return _reverse_source(md[:model], md[:network], md[:contributions], md[:raw],
                   get(md, :form, :expanded) === :compact, get(md, :closure, :unknown), fname)
end

# From a model and a network: the per-reaction table (no MTK system is compiled).
function _reverse_source(cm::ContactModel, net::NetworkDescriptor, fname::AbstractString)
    table = lift_contributions(cm, net)
    return _reverse_source(cm, net, table, symbolic_ode(table), false, table.closure, fname)
end

function _reverse_source(cm::ContactModel, net::NetworkDescriptor, table::LiftContributions,
                 raw::SymbolicODE, compact::Bool, closure::Symbol, fname::AbstractString)
    closure in (:configuration, :well_mixed) || throw(ArgumentError(
        "$fname: the reverse maps are defined for models lifted on a ConfigurationNetwork or a " *
        "WellMixed network (one node type); this system uses the :$closure closure on " *
        "$(nameof(typeof(net)))"))
    Σ = susceptible_species(cm)
    length(Σ) == 1 || throw(ArgumentError(
        "$fname: the reverse maps need exactly one susceptible class; :$(cm.name) has " *
        "$(isempty(Σ) ? "none" : join(Σ, ", "))"))
    s = only(Σ)
    lm = _lift_model(cm, net, Σ; context = fname)
    coords = Dict{Symbol,Any}(x.name => x.var for x in table.coordinate_info)
    exits = any(r -> r.type === :exit, table.contributions)
    θ = coords[:θ]
    ξ = exits ? coords[:ξ] : 1
    q = last(only(table.seed_factors))
    nodes = Symbol[X for X in lm.nodes if !(X in lm.sinks)]
    φ = Dict{Symbol,Any}()
    pop = Dict{Symbol,Any}()
    for X in lm.nodes
        haskey(coords, Symbol(:φ_, X)) && (φ[X] = coords[Symbol(:φ_, X)])
        pop[X] = coords[Symbol(:pop_, X)]
    end
    if compact
        φ, pop = _compact_embedding(lm, net, θ, q, coords)
    end
    return _ReverseSource(raw, cm, net, closure, compact, lm, s, nodes, copy(lm.sinks), exits,
                          θ, ξ, q, φ, pop)
end

# M9: the compact form (θ, R) of an SIR-shaped model is the invariant set W = {τφ_R + γθ = γ}
# (with S + pop_I + R = 1) of the expanded form: φ_R = γ(1 − θ)/τ, φ_I = θ − φ_S − φ_R and
# pop_I = 1 − S − R.
function _compact_embedding(lm::_LiftModel, net, θ, q, coords)
    _, I, R, τ, γ = _compact_shape(lm)
    v = _numvalue(τ)
    (v === nothing || !iszero(v)) || throw(ArgumentError(
        "$(lm.context): the compact form with τ = 0 has no embedding into the expanded " *
        "coordinates; use form = :expanded"))
    d = net.degrees
    ψ, ψ1, k̄ = pgf(d, θ), pgf_derivative(d, θ, 1), mean_degree(d)
    φS = _ratio(q * ψ1, k̄, q * ψ)
    φR = γ * (1 - θ) / τ
    popR = coords[Symbol(:pop_, R)]
    φ = Dict{Symbol,Any}(I => θ - φS - φR, R => φR)
    pop = Dict{Symbol,Any}(I => 1 - q * ψ - popR, R => popR)
    return φ, pop
end

# The degree distribution and its PGF factors at the source's θ (configuration networks).
_rs_degrees(src::_ReverseSource) = src.net.degrees
_rs_ψ(src::_ReverseSource, n::Integer = 0) =
    n == 0 ? pgf(_rs_degrees(src), src.θ) : pgf_derivative(_rs_degrees(src), src.θ, n)

# S = qξψ(θ) (configuration) or qξe^{κ(θ−1)} (well mixed), in the source states.
_node_S(src::_ReverseSource) = src.closure === :well_mixed ?
    src.q * src.ξ * exp(src.net.κ * (src.θ - 1)) : src.q * src.ξ * _rs_ψ(src)

# Poisson type: (α, κ) with ψ' = αψ^κ, or nothing (also when the test cannot be made).
function _rs_poisson_type(d)
    return try
        is_poisson_type(d)
    catch err
        err isa ArgumentError || rethrow()
        nothing
    end
end
_rs_is_one(x) = (v = _numvalue(x); v !== nothing && v == 1)
_rs_is_poisson(src::_ReverseSource) = src.closure === :configuration &&
    (pt = _rs_poisson_type(_rs_degrees(src)); pt !== nothing && _rs_is_one(pt.κ))

# The kind of a map onto a target without the removal sinks (and without ξ unless `keeps_ξ`): a
# conjugacy when it forgets nothing, a quotient otherwise; from a compact source a restriction.
_forgetful_kind(src::_ReverseSource; keeps_ξ::Bool = false) =
    (src.compact || (src.exits && !keeps_ξ) || !isempty(src.sinks)) ? :semiconjugacy : :conjugacy

# The map as target state => expression, from expressions by target state name.
function _rs_map(tgt::SymbolicODE, byname::AbstractDict{Symbol}, fname)
    out = Pair{Any,Any}[]
    for (v, n) in zip(tgt.states, state_names(tgt))
        haskey(byname, n) || throw(ArgumentError(
            "$fname: internal error: no expression for the target state $n"))
        push!(out, v => byname[n])
    end
    return out
end

# SIR shape (one contact s + I → 2I, one transition I → R, nothing else): the case the Lean
# theorems NEP.rempala / NEP.rempala_lift cover.
function _is_sir_shaped(cm::ContactModel)
    cs, ts = contacts(cm), node_transitions(cm)
    (length(cs) == 1 && length(ts) == 1 && length(species_names(cm)) == 3) || return false
    c, t = only(cs), only(ts)
    return c.product === c.infector && t.from === c.infector && t.to !== nothing &&
           t.to !== c.recipient && rate_convention(cm) isa PerContact
end

# ---------------------------------------------------------------------------------------------
# Models and reaction networks of the targets
# ---------------------------------------------------------------------------------------------

# The model with the per-contact rates τ_r on this network written out (convention PerContact):
# c_κ of it is the mass-action model of WellMixed(κ) whatever the convention of `cm` (§B.6).
function _rs_per_contact_model(cm::ContactModel, net::NetworkDescriptor)
    rate_convention(cm) isa PerContact && return cm
    τs = isempty(contacts(cm)) ? Any[] : per_contact_rates(cm, net)
    cs = Contact[Contact(c.recipient, c.infector, c.product, τ, c.layer, c.name)
                 for (c, τ) in zip(contacts(cm), τs)]
    return ContactModel(Symbol(cm.name, :_per_contact); contacts = cs,
                        transitions = node_transitions(cm), species = species_names(cm),
                        susceptible = susceptible_species(cm), defaults = parameter_defaults(cm),
                        labels = species_labels(cm))
end

# A ContactModel read as mass action (κ = 1, PerContact) as a general reaction network.
function _contact_reaction_data(model::ContactModel, notes::Vector{String})
    rs = GeneralReaction[]
    for c in contacts(model)
        push!(rs, GeneralReaction([c.recipient => 1, c.infector => 1],
                                  [c.product => 1, c.infector => 1], c.rate; name = c.name))
    end
    for t in node_transitions(model)
        push!(rs, GeneralReaction([t.from => 1],
                                  t.to === nothing ? Pair{Symbol,Int}[] : [t.to => 1], t.rate;
                                  name = t.name))
    end
    sp = species_names(model)
    return ReactionNetworkData(model.name, sp, rs; defaults = parameter_defaults(model),
                               observables = Dict{Symbol,Vector{Symbol}}(x => [x] for x in sp),
                               provenance = Provenance(:transform; assumptions = notes))
end

_rs_edge_copy(X::Symbol) = Symbol(:Φ_, X)
_rs_plain(name::Symbol) = Symbolics.variable(name)
_rs_none() = Pair{Symbol,Int}[]

function _rs_check_new_species(src::_ReverseSource, new::Vector{Symbol}, fname)
    clash = [x for x in new if x in species_names(src.cm)]
    isempty(clash) || throw(ArgumentError(
        "$fname: the auxiliary species $(join(clash, ", ")) of the target collide with species " *
        "of the model :$(src.cm.name); rename those species"))
    return nothing
end

# M4 (Poisson type ψ' = αψ^κ): with Q = qξ (q without exits) and S = Qψ(θ),
#   contact r:  S + Φ_J → X + Φ_J  at τα Q^{1−κ} S^κ Φ_J       (node entry qξψ'(θ) τ φ_J)
#               Φ_J → Φ_J + Φ_X    at τκα Q^{2−2κ} S^{2κ−1} Φ_J (edge entry qξψ''(θ)/ψ'(1) τ φ_J)
#               Φ_J → ∅            at τ                         (the edge has transmitted)
#   transition: both copies, mass action;  exit s → Y: S → Y and Ξ → ∅ at ν, and
#               S → S + Φ_Y at ν Q^{1−κ} S^κ (φ_S = Q^{1−κ}S^κ).
# The auxiliary Ξ = ξ appears only with exits (for κ ≠ 1 the factor Q^{1−κ} depends on it).
function _power_law_data(src::_ReverseSource, α, κ, fname)
    lm, s, cm = src.lm, src.s, src.cm
    Φ = _rs_edge_copy
    Ξ = :Ξ
    new = vcat(src.exits ? [Ξ] : Symbol[], Φ.(src.nodes))
    _rs_check_new_species(src, new, fname)
    Sv = _rs_plain(s)
    Q = src.exits ? src.q * _rs_plain(Ξ) : src.q
    τraw = isempty(contacts(cm)) ? Any[] : per_contact_rates(cm, src.net)
    rs = GeneralReaction[]
    for (k, c) in enumerate(contacts(cm))
        τ = lm.contact_rates[k]
        J, X = c.infector, c.product
        ΦJ = _rs_plain(Φ(J))
        push!(rs, GeneralReaction([s => 1, Φ(J) => 1], [X => 1, Φ(J) => 1],
                                  τ * α * Q^(1 - κ) * Sv^κ * ΦJ; only_use_rate = true,
                                  name = c.name))
        push!(rs, GeneralReaction([Φ(J) => 1], [Φ(J) => 1, Φ(X) => 1],
                                  τ * κ * α * Q^(2 - 2κ) * Sv^(2κ - 1) * ΦJ; only_use_rate = true,
                                  name = Symbol(c.name, :_edge_entry)))
        push!(rs, GeneralReaction([Φ(J) => 1], _rs_none(), τraw[k];
                                  name = Symbol(c.name, :_transmitted)))
    end
    for (k, t) in enumerate(node_transitions(cm))
        a = t.rate
        if lm.transition_types[k] === :exit
            push!(rs, GeneralReaction([s => 1], t.to === nothing ? _rs_none() : [t.to => 1], a;
                                      name = t.name))
            push!(rs, GeneralReaction([Ξ => 1], _rs_none(), a; name = Symbol(t.name, :_survival)))
            t.to === nothing || push!(rs, GeneralReaction(
                [s => 1], [s => 1, Φ(t.to) => 1], lm.transition_rates[k] * Q^(1 - κ) * Sv^κ;
                only_use_rate = true, name = Symbol(t.name, :_edge)))
        else
            for (f, suffix) in ((identity, Symbol()), (Φ, :_edge))
                push!(rs, GeneralReaction([f(t.from) => 1],
                                          t.to === nothing ? _rs_none() : [f(t.to) => 1], a;
                                          name = Symbol(t.name, suffix)))
            end
        end
    end
    species = vcat(s, new, src.nodes)
    notes = ["power-law kinetics M4 on a Poisson-type network (ψ' = αψ^κ with α = $(α), κ = " *
             "$(κ)): S = qξψ(θ), Φ_X = φ_X, X = pop_X" * (src.exits ? ", Ξ = ξ" : "") *
             "; mass action iff κ = 1. For κ ≠ 1 the rate laws depend on the initially " *
             "susceptible fraction q (the parameter $(_symname(src.q))) through Q^{1−κ}, Q = qξ"]
    obs = Dict{Symbol,Vector{Symbol}}(x => [x] for x in vcat(s, src.nodes))
    d = ReactionNetworkData(Symbol(cm.name, :_power_law), species, rs;
                            defaults = parameter_defaults(cm), observables = obs,
                            provenance = Provenance(:transform; assumptions = notes))
    return d, notes
end

# M5 (any ψ): the EB field itself as a reaction network with the auxiliary species Θ (and Ξ with
# exits), edge copies Φ_X and node copies X (sinks included), and non-mass-action rate laws in
# qξψ'(Θ) and qξψ''(Θ)/ψ'(1): an encoding (the map is a renaming), exact for every ψ.
function _general_data(src::_ReverseSource, fname)
    lm, s, cm = src.lm, src.s, src.cm
    Φ = _rs_edge_copy
    Θ, Ξ = :Θ, :Ξ
    all_nodes = lm.nodes
    new = vcat([Θ], src.exits ? [Ξ] : Symbol[], Φ.(all_nodes), src.sinks)
    _rs_check_new_species(src, new, fname)
    d = _rs_degrees(src)
    Θv = _rs_plain(Θ)
    Q = src.exits ? src.q * _rs_plain(Ξ) : src.q
    ψ, ψ1, ψ2, k̄ = pgf(d, Θv), pgf_derivative(d, Θv, 1), pgf_derivative(d, Θv, 2), mean_degree(d)
    node_S, edge_S = Q * ψ, _ratio(Q * ψ1, k̄, Q * ψ)
    node_entry, edge_entry = Q * ψ1, _ratio(Q * ψ2, k̄, Q * ψ1)
    τraw = isempty(contacts(cm)) ? Any[] : per_contact_rates(cm, src.net)
    rs = GeneralReaction[]
    for (k, c) in enumerate(contacts(cm))
        τ = lm.contact_rates[k]
        J, X = c.infector, c.product
        ΦJ = _rs_plain(Φ(J))
        push!(rs, GeneralReaction([Θ => 1, Φ(J) => 1], [Φ(J) => 1], τ * ΦJ;
                                  only_use_rate = true, name = Symbol(c.name, :_hazard)))
        push!(rs, GeneralReaction([Φ(J) => 1], _rs_none(), τraw[k];
                                  name = Symbol(c.name, :_transmitted)))
        push!(rs, GeneralReaction([Φ(J) => 1], [Φ(J) => 1, Φ(X) => 1], τ * ΦJ * edge_entry;
                                  only_use_rate = true, name = Symbol(c.name, :_edge_entry)))
        push!(rs, GeneralReaction([Φ(J) => 1], [Φ(J) => 1, X => 1], τ * ΦJ * node_entry;
                                  only_use_rate = true, name = c.name))
    end
    for (k, t) in enumerate(node_transitions(cm))
        Y = lm.transition_targets[k]              # the sink for X → ∅
        if lm.transition_types[k] === :exit
            ν = lm.transition_rates[k]
            push!(rs, GeneralReaction([Ξ => 1], _rs_none(), t.rate;
                                      name = Symbol(t.name, :_survival)))
            push!(rs, GeneralReaction([Ξ => 1], [Ξ => 1, Φ(Y) => 1], ν * edge_S;
                                      only_use_rate = true, name = Symbol(t.name, :_edge)))
            push!(rs, GeneralReaction([Ξ => 1], [Ξ => 1, Y => 1], ν * node_S;
                                      only_use_rate = true, name = t.name))
        else
            for (f, suffix) in ((identity, Symbol()), (Φ, :_edge))
                push!(rs, GeneralReaction([f(t.from) => 1], [f(Y) => 1], t.rate;
                                          name = Symbol(t.name, suffix)))
            end
        end
    end
    species = vcat(Θ, src.exits ? [Ξ] : Symbol[], Φ.(all_nodes), all_nodes)
    notes = ["general kinetics M5: Θ = θ" * (src.exits ? ", Ξ = ξ" : "") *
             ", Φ_X = φ_X, X = pop_X (sinks included); S = q$(src.exits ? "Ξ" : "")ψ(Θ) is not " *
             "a species (an S-form needs ψ⁻¹). An encoding of the edge-based field, exact for " *
             "every degree distribution"]
    obs = Dict{Symbol,Vector{Symbol}}(x => [x] for x in all_nodes)
    data = ReactionNetworkData(Symbol(cm.name, :_general_kinetics), species, rs;
                               defaults = parameter_defaults(cm), observables = obs,
                               provenance = Provenance(:transform; assumptions = notes))
    return data, notes
end

# ---------------------------------------------------------------------------------------------
# The images, form by form
# ---------------------------------------------------------------------------------------------

const _EVIDENCE_HERE = Evidence(:symbolic, "EdgeBasedModels test/suites/reverse.jl")
const _EVIDENCE_EDGE_DOUBLING =
    Evidence(:symbolic, "NetworkEpiCore test/suites/morphisms.jl (edge_doubling)")
const _EVIDENCE_LADDER = Evidence(:numeric, "EdgeBasedModels test/suites/reverse.jl (Λ1 ladder)")
const _EVIDENCE_CALIBRATION =
    Evidence(:numeric, "EdgeBasedModels test/suites/reverse.jl (calibration)")

# A target that is a ContactModel read as mass action: S ↦ node S, X ↦ `values[X]` (pop_X or φ_X).
function _contact_image(src::_ReverseSource, model::ContactModel, values::AbstractDict;
                        name::Symbol, kind::Symbol, exactness::Symbol, evidence, notes, form,
                        fname)
    data = _contact_reaction_data(model, notes)
    tgt = mass_action(model)
    byname = Dict{Symbol,Any}(src.s => _node_S(src))
    for X in species_names(model)
        X === src.s && continue
        byname[X] = values[X]
    end
    m = Semiconjugacy(name, src.ode, tgt, _rs_map(tgt, byname, fname), Pair{Any,Any}[],
                      kind, exactness, evidence)
    return MassActionImage(model, data, tgt, m, exactness, notes, form, :mass_action)
end

function _data_image(src::_ReverseSource, data::ReactionNetworkData, byname::AbstractDict;
                     name::Symbol, kind::Symbol, evidence, notes, form, kinetics, fname)
    tgt = mass_action(data)
    m = Semiconjugacy(name, src.ode, tgt, _rs_map(tgt, byname, fname), Pair{Any,Any}[],
                      kind, :exact, evidence)
    return MassActionImage(nothing, data, tgt, m, :exact, notes, form, kinetics)
end

_compact_note(src) = src.compact ?
    ["the system is in the compact form (M9): the map is taken on the invariant set " *
     "W = {τφ_R + γθ = γ} of the expanded form, φ_R = γ(1 − θ)/τ, φ_I = θ − φ_S − φ_R"] : String[]

function _well_mixed_image(src::_ReverseSource, fname)
    κ = src.net.κ
    model = scale_contact_rates(_rs_per_contact_model(src.cm, src.net), κ)
    model = ContactModel(Symbol(src.cm.name, :_mass_action); contacts = contacts(model),
                         transitions = node_transitions(model), species = species_names(model),
                         susceptible = susceptible_species(model),
                         defaults = parameter_defaults(model), labels = species_labels(model))
    kind = _forgetful_kind(src)
    notes = ["well-mixed unit M1 on WellMixed($(κ)): S = qξe^{κ(θ−1)} and X = pop_X (node " *
             "fractions); mass action with contact rates κτ" *
             (kind === :conjugacy ? "; a conjugacy onto S ∈ (0, q]" :
              "; a quotient (ξ and the removal sink are forgotten)")]
    ev = [Evidence(:paper, "Miller, Slim & Volz 2012, Part II (papers/1106.6319v1.md:103-111)"),
          _EVIDENCE_HERE]
    return _contact_image(src, model, src.pop; name = :well_mixed_unit, kind,
                          exactness = :exact, evidence = ev, notes, form = :exact, fname)
end

function _poisson_iso_image(src::_ReverseSource, fname)
    μ = mean_degree(_rs_degrees(src))
    data = edge_doubling(src.cm, μ)
    byname = Dict{Symbol,Any}(src.s => _node_S(src))
    for X in src.nodes
        byname[_rs_edge_copy(X)] = src.φ[X]
        byname[X] = src.pop[X]
    end
    notes = vcat(["Poisson isomorphism M2 on Poisson($(μ)): MA(D_μ P) with S = qξe^{μ(θ−1)}, " *
                  "edge copies Φ_X = φ_X and node copies X = pop_X: the X are the node " *
                  "fractions (prevalences), and S(t) is exact"],
                 src.exits ? ["exits s → Y are lowered to s → Φ_Y + Y (design §J.10); ξ is " *
                              "forgotten (a quotient)"] : String[],
                 isempty(src.sinks) ? String[] : ["the removal sink is forgotten (a quotient)"],
                 _compact_note(src))
    return _data_image(src, data, byname; name = :poisson_iso, kind = _forgetful_kind(src),
                       evidence = [_EVIDENCE_EDGE_DOUBLING, _EVIDENCE_HERE],
                       notes, form = :exact, kinetics = :mass_action, fname)
end

function _power_law_image(src::_ReverseSource, pt, fname)
    data, notes = _power_law_data(src, pt.α, pt.κ, fname)
    byname = Dict{Symbol,Any}(src.s => _node_S(src))
    src.exits && (byname[:Ξ] = src.ξ)
    for X in src.nodes
        byname[_rs_edge_copy(X)] = src.φ[X]
        byname[X] = src.pop[X]
    end
    append!(notes, _compact_note(src))
    isempty(src.sinks) || push!(notes, "the removal sink is forgotten (a quotient)")
    return _data_image(src, data, byname; name = :power_law,
                       kind = _forgetful_kind(src; keeps_ξ = true), evidence = [_EVIDENCE_HERE],
                       notes, form = :exact, kinetics = :power_law, fname)
end

function _exact_image(src::_ReverseSource, fname)
    src.closure === :well_mixed && return _well_mixed_image(src, fname)
    pt = _rs_poisson_type(_rs_degrees(src))
    pt === nothing && throw(ArgumentError(
        "$fname: no mass-action (or power-law) network reproduces the edge-based dynamics " *
        "exactly on $(_network_text(src.net)): that needs a Poisson-type degree distribution " *
        "(ψ' = αψ^κ; M2 for Poisson, M4 otherwise, and M8: exactly the networks on which the " *
        "constant pairwise closure is exact). Use form = :general (M5: general kinetics with an " *
        "auxiliary Θ, exact for every ψ), :limit (the dense limit, not a morphism) or " *
        ":calibrated (an R₀-matched calibration, not a morphism)"))
    _rs_is_one(pt.κ) && return _poisson_iso_image(src, fname)
    return _power_law_image(src, pt, fname)
end

const _WELL_MIXED_ONLY_EXACT =
    "on WellMixed(κ) the edge-based lift is mass action exactly (the well-mixed unit M1): use " *
    "form = :exact"

function _edge_image(src::_ReverseSource, fname)
    src.closure === :well_mixed && throw(ArgumentError("$fname: $(_WELL_MIXED_ONLY_EXACT)"))
    _rs_is_poisson(src) || throw(ArgumentError(
        "$fname: Rempała's quotient (form = :edge, M3) needs a Poisson degree distribution " *
        "(ψ' = μψ); this system is lifted on $(_network_text(src.net)). Use form = :exact " *
        "(M1 on WellMixed, M4 power-law kinetics on a Poisson-type network), :general (M5, any " *
        "ψ), :limit or :calibrated"))
    μ = mean_degree(_rs_degrees(src))
    model = rempala_reduction(src.cm, μ)
    sir = _is_sir_shaped(src.cm)
    notes = vcat(["Rempała's quotient M3 on Poisson($(μ)): MA(E_μ P) = c_μ P plus J → ∅ at τ for " *
                  "every infector J, on the model's own species. S = qξe^{μ(θ−1)} is exact, but " *
                  "every other species X of the target is the EDGE variable φ_X, not the node " *
                  "fraction (the MA \"I\" is φ_I, not the prevalence; form = :exact gives the " *
                  "prevalences as the node copies of D_μ)"],
                 sir ? ["for SIR this is MA(β = μτ, γ_MA = γ + τ) (Rempała 2023, Thm 1); the old " *
                        "to_mass_action map MA(μτ, γ) is not a reduction (verified issue E08)"] :
                 String[],
                 _compact_note(src))
    ev = vcat(sir ? [Evidence(:lean, "NEP.rempala"), Evidence(:lean, "NEP.rempala_lift")] :
              Evidence[],
              [Evidence(:paper, "Rempała 2023, Thm 1 (papers/2310.13866v1.md:69; SIR)"),
               _EVIDENCE_HERE])
    return _contact_image(src, model, src.φ; name = :rempala, kind = :semiconjugacy,
                          exactness = :exact, evidence = ev, notes, form = :edge, fname)
end

function _general_image(src::_ReverseSource, fname)
    src.closure === :configuration ||
        throw(ArgumentError("$fname: $(_WELL_MIXED_ONLY_EXACT)"))
    data, notes = _general_data(src, fname)
    append!(notes, _compact_note(src))
    byname = Dict{Symbol,Any}(:Θ => src.θ)
    src.exits && (byname[:Ξ] = src.ξ)
    for X in src.lm.nodes
        byname[_rs_edge_copy(X)] = src.φ[X]
        byname[X] = src.pop[X]
    end
    return _data_image(src, data, byname; name = :general_kinetics,
                       kind = src.compact ? :semiconjugacy : :conjugacy,
                       evidence = [_EVIDENCE_HERE], notes, form = :general, kinetics = :general,
                       fname)
end

function _limit_image(src::_ReverseSource, fname)
    src.closure === :configuration ||
        throw(ArgumentError("$fname: $(_WELL_MIXED_ONLY_EXACT)"))
    k̄ = mean_degree(src.net)
    model = scale_contact_rates(_rs_per_contact_model(src.cm, src.net), k̄)
    model = ContactModel(Symbol(src.cm.name, :_dense_limit); contacts = contacts(model),
                         transitions = node_transitions(model), species = species_names(model),
                         susceptible = susceptible_species(model),
                         defaults = parameter_defaults(model), labels = species_labels(model))
    notes = ["the dense limit (Λ1): MA with contact rates ⟨k⟩τ = $(k̄)τ on the node fractions " *
             "(S = qξψ(θ), X = pop_X), the limit of the edge-based model as ⟨k⟩ → ∞ with ⟨k⟩τ " *
             "fixed; the error is O(1/μ) on Poisson(μ) (Λ1) and O(1/n) on n-regular networks " *
             "(Λ2). A limit, not a morphism: verify fails at every finite degree"]
    return _contact_image(src, model, src.pop; name = :dense_limit, kind = :semiconjugacy,
                          exactness = :limit,
                          evidence = [_EVIDENCE_LADDER],
                          notes, form = :limit, fname)
end

const _CALIBRATION_SCALE = :κ_calibrated

function _calibrated_image(src::_ReverseSource, sys, fname; p, target, initial)
    src.closure === :configuration ||
        throw(ArgumentError("$fname: $(_WELL_MIXED_ONLY_EXACT)"))
    what = target === :r ? :growth : target
    what in (:R0, :growth, :final_size) || throw(ArgumentError(
        "$fname: target must be :R0, :growth (alias :r) or :final_size; got :$(target)"))
    cm, net = src.cm, src.net
    pd = Dict{Symbol,Float64}(parameter_defaults(cm))
    if sys !== nothing
        for (k, v) in get(sys.metadata, :parameter_defaults, Dict{Symbol,Float64}())
            pd[k] = v
        end
    end
    if p !== nothing
        for (k, v) in p
            pd[Symbol(k)] = Float64(v)
        end
    end
    value = what === :R0 ? basic_reproduction_number(cm, net, pd) :
            what === :growth ? early_growth_rate(cm, net, pd) :
            final_size(cm, net, pd; initial)
    pc = _rs_per_contact_model(cm, net)
    _CALIBRATION_SCALE in Symbol[_pname(x) for x in rate_parameters(pc)] && throw(ArgumentError(
        "$fname: the model has a parameter named $(_CALIBRATION_SCALE), which the calibration " *
        "uses"))
    scaled = scale_contact_rates(pc, _CALIBRATION_SCALE)
    κ = calibrate(scaled, WellMixed(1.0), merge(pd, Dict(_CALIBRATION_SCALE => 1.0));
                  target = what => value, vary = _CALIBRATION_SCALE, initial)[_CALIBRATION_SCALE]
    model = scale_contact_rates(pc, κ)
    model = ContactModel(Symbol(cm.name, :_calibrated); contacts = contacts(model),
                         transitions = node_transitions(model), species = species_names(model),
                         susceptible = susceptible_species(model),
                         defaults = parameter_defaults(model), labels = species_labels(model))
    label = what === :R0 ? "R₀" : what === :growth ? "the early growth rate r" : "the final size"
    notes = ["a calibration (F6), not a morphism: MA with contact rates κτ, κ = $(κ) chosen so " *
             "that $(label) equals the network's ($(value)) at the given parameters; S = qξψ(θ), " *
             "X = pop_X. Its trajectories differ from the edge-based ones (verify fails), and " *
             "the calibration does not commute with gluing or stratification"]
    return _contact_image(src, model, src.pop; name = :calibrated, kind = :semiconjugacy,
                          exactness = :calibration,
                          evidence = [_EVIDENCE_CALIBRATION],
                          notes, form = :calibrated, fname)
end

function _reverse_image(src::_ReverseSource, form::Symbol, fname; sys = nothing, p = nothing,
                target = :R0, initial = nothing)
    form === :exact && return _exact_image(src, fname)
    form === :edge && return _edge_image(src, fname)
    form === :general && return _general_image(src, fname)
    form === :limit && return _limit_image(src, fname)
    form === :calibrated && return _calibrated_image(src, sys, fname; p, target, initial)
    throw(ArgumentError("$fname: unknown form = :$(form); expected one of " *
                        join((":$f" for f in MASS_ACTION_FORMS), ", ")))
end

const _FORMS_TEXT =
    "form = :exact (the exact reduction: the well-mixed unit M1 on WellMixed, the Poisson " *
    "isomorphism M2 onto edge and node copies on a Poisson network, power-law kinetics M4 on a " *
    "Poisson-type network), :edge (Rempała's quotient M3 on a Poisson network: MA(μτ, γ + τ) for " *
    "SIR, whose I is the edge variable φ_I), :general (general kinetics with an auxiliary Θ, M5, " *
    "any degree distribution), :limit (the dense limit Λ1, not a morphism) or :calibrated (an " *
    "R₀-matched mass action, a calibration, not a morphism)"

"""
    mass_action(sys::EdgeModelSystem; form, p = nothing, target = :R0, initial = nothing)
        -> MassActionImage

The reverse maps of an edge-based system ("back to mass action" in the dynamic sense, design
§D.5): a reaction network whose dynamics are the image of the edge-based dynamics under a map π,
returned as a [`MassActionImage`](@ref) with the map as a `Semiconjugacy` (check it with
`verify(img.morphism)`) and an exactness label. `form` is required (one of
[`MASS_ACTION_FORMS`](@ref)):

- `:exact`: the exact reduction, where one exists.
  - `WellMixed(κ)`: the well-mixed unit M1, MA(c_κ P) on the node fractions, S = qξe^{κ(θ−1)}
    (a conjugacy without exits and removals, a quotient otherwise).
  - `ConfigurationNetwork(PoissonDegree(μ))`: the Poisson isomorphism M2, the mass action of the
    edge doubling D_μ P (`edge_doubling`): S = qξe^{μ(θ−1)}, edge copies Φ_X = φ_X and node
    copies X = pop_X (the prevalences); contacts s + Φ_J → Φ_X + X + Φ_J at μτ and Φ_J → ∅ at
    τ, transitions on both copies, exits s → Φ_Y + Y.
  - A Poisson-type network (ψ' = αψ^κ, κ ≠ 1: regular, binomial, negative binomial): power-law
    kinetics M4 on the same species, with rate laws τα Q^{1−κ}S^κΦ_J (node entry) and
    τκα Q^{2−2κ}S^{2κ−1}Φ_J (edge entry), Q = qξ (an auxiliary species Ξ = ξ with exits);
    `img.kind === :power_law`.
  - Other degree distributions: an `ArgumentError` (no exact mass-action or power-law reduction
    exists, M8); use `:general`.
- `:edge`: Rempała's quotient M3 on a Poisson(μ) network, the mass action of
  `rempala_reduction(cm, μ)` on the model's own species: S = qξe^{μ(θ−1)} exactly, and **every
  other species is the edge variable φ_X, not the node fraction**. For SIR it is
  MA(β = μτ, γ_MA = γ + τ) (Rempała 2023, Thm 1; Lean `NEP.rempala`), not the old
  `to_mass_action` map MA(μτ, γ) (verified issue E08). The prevalence is the node copy of
  `form = :exact`.
- `:general`: general kinetics M5 on any configuration network: the edge-based field written as a
  reaction network in Θ = θ (Ξ = ξ with exits), Φ_X = φ_X and X = pop_X with rate laws in
  qξψ'(Θ) and qξψ''(Θ)/ψ'(1). Always exact (a conjugacy), but only an encoding: S = qξψ(Θ) is
  not a species. `img.kind === :general`.
- `:limit`: the dense limit Λ1, MA(c_⟨k⟩ P) on the node fractions, which the edge-based model
  approaches as ⟨k⟩ → ∞ with ⟨k⟩τ fixed (O(1/μ) on Poisson(μ), O(1/n) on n-regular networks).
  Labelled `exactness = :limit`: it is not a morphism, and `verify` fails.
- `:calibrated`: the mass action MA(c_κ P) whose κ is calibrated so that `target` (`:R0`,
  `:growth` or `:final_size` with `initial`) equals the network's, at the parameter values `p`
  (merged over the model's defaults). Labelled `exactness = :calibration` (F6): not a morphism.
  For `:sir_pois5` it is MA(1/2, 1/4), which has the same final size (0.8002) but peaks at
  t ≈ 17.5 instead of 11.35.

Every map starts from `symbolic_ode(sys)`, the uncompiled edge-based field (a compact-form
system is embedded into the expanded coordinates on its invariant set, M9, so its maps are
restrictions). The system must come from `edge_based` on a `ConfigurationNetwork` or a
`WellMixed` network with one susceptible class. `pushforward(img, sys, sol, tgrid)` maps a
solution of `sys` to the target coordinates.

```julia
sys = edge_based(sir_model(), ConfigurationNetwork(PoissonDegree(5)))
img = mass_action(sys; form = :edge)       # Rempała: MA(5τ, γ + τ) on (S, φ_I, φ_R)
verify(img.morphism)                       # VerificationResult(ok = true, method = :symbolic, …)
mass_action(sys; form = :exact).ode        # D_μ: S, Φ_I, Φ_R, I, R (I is the prevalence)
```
"""
function NetworkEpiCore.mass_action(sys::EdgeModelSystem; form::Union{Nothing,Symbol} = nothing,
                                    p = nothing, target::Symbol = :R0, initial = nothing)
    form === nothing && throw(ArgumentError(
        "mass_action(sys; form): choose the sense of \"back to mass action\" (design §D.5): " *
        _FORMS_TEXT))
    fname = "mass_action(sys; form = :$(form))"
    form in MASS_ACTION_FORMS || throw(ArgumentError(
        "$fname: unknown form; expected one of " * join((":$f" for f in MASS_ACTION_FORMS), ", ")))
    return _reverse_image(_reverse_source(sys, fname), form, fname; sys, p, target, initial)
end

"""
    as_reaction_system(sys::EdgeModelSystem; form = :general, kw...) -> ReactionNetworkData

The reaction network of the reverse map `mass_action(sys; form, kw...)`
(`mass_action(sys; form).reaction_data`): by default the general-kinetics encoding M5 of the
edge-based field (species Θ, Ξ with exits, Φ_X and X, rate laws in qξψ'(Θ) and qξψ''(Θ)/ψ'(1)),
which exists for every degree distribution; `form = :exact` gives D_μ on a Poisson network and the
power-law network on a Poisson-type one, and `form = :edge` Rempała's E_μ. Convert it with
`Catalyst.ReactionSystem(as_reaction_system(sys))` (NetworkEpiCore's Catalyst extension) or take
its ODE with `mass_action(data)`.
"""
as_reaction_system(sys::EdgeModelSystem; form::Symbol = :general, kw...) =
    mass_action(sys; form, kw...).reaction_data

# ---------------------------------------------------------------------------------------------
# M6: EB → the S-anchored pairwise model
# ---------------------------------------------------------------------------------------------

function _pairwise_image(src::_ReverseSource, fname)
    src.closure === :configuration || throw(ArgumentError(
        "$fname: the S-anchored pairwise image (M6) is defined on a ConfigurationNetwork; a " *
        "WellMixed network has no network pairs (its edge-based model is mass action, M1)"))
    lm, s = src.lm, src.s
    d = _rs_degrees(src)
    k̄ = mean_degree(d)
    v = _numvalue(k̄)
    (v === nothing || !iszero(v)) || throw(ArgumentError(
        "$fname: the network has mean degree 0, so there are no pairs"))
    all_nodes = lm.nodes
    pname(X) = Symbol(s, X)
    names = vcat([:θ, s], pname.(all_nodes), [pname(s)], all_nodes)
    dup = unique!([n for n in names if count(==(n), names) > 1])
    isempty(dup) || throw(ArgumentError(
        "$fname: the pair names $(join(dup, ", ")) collide with species names (a pair [sX] is " *
        "named by joining the two species names); rename the species"))
    pnames = Set(_symname(p) for p in src.ode.parameters)
    clash = [n for n in names if n in pnames]
    isempty(clash) || throw(ArgumentError(
        "$fname: the state names $(join(clash, ", ")) of the pairwise image collide with " *
        "parameter names; rename the parameters"))
    θt = _state(:θ)
    St = _state(s)
    pair = Dict{Symbol,Any}(X => _state(pname(X)) for X in all_nodes)
    sst = _state(pname(s))
    node = Dict{Symbol,Any}(X => _state(X) for X in all_nodes)
    ψ, ψ1, ψ2 = pgf(d, θt), pgf_derivative(d, θt, 1), pgf_derivative(d, θt, 2)
    K = ψ * ψ2 / ψ1^2
    triple(a, b) = K * a * b / St
    f = Dict{Symbol,Vector{Any}}(n => Any[] for n in names)
    add!(n, e) = push!(f[n], e)
    for (k, c) in enumerate(contacts(src.cm))
        τ = lm.contact_rates[k]
        J, X = c.infector, c.product
        h = τ * pair[J]
        add!(:θ, -h * ψ / (St * ψ1))
        add!(s, -h)
        add!(X, h)
        add!(pname(J), -h)                                  # the partner J transmits to the s
        for Z in all_nodes                                  # the s is infected by another J
            add!(pname(Z), -τ * triple(pair[J], pair[Z]))
        end
        add!(pname(s), -2τ * triple(sst, pair[J]))
        add!(pname(X), τ * triple(sst, pair[J]))            # the partner s of an s–s pair
    end
    for (k, t) in enumerate(node_transitions(src.cm))
        a = lm.transition_rates[k]
        Y = lm.transition_targets[k]
        if lm.transition_types[k] === :exit
            add!(s, -a * St)
            add!(Y, a * St)
            for Z in all_nodes
                add!(pname(Z), -a * pair[Z])
            end
            add!(pname(s), -2a * sst)
            add!(pname(Y), a * sst)
        else
            X = t.from
            add!(X, -a * node[X])
            add!(Y, a * node[X])
            add!(pname(X), -a * pair[X])
            add!(pname(Y), a * pair[X])
        end
    end
    states = Any[θt, St]
    append!(states, Any[pair[X] for X in all_nodes])
    push!(states, sst)
    append!(states, Any[node[X] for X in all_nodes])
    rhs = Any[_sum_terms(f[n]) for n in names]
    tgt = SymbolicODE(Symbol(src.cm.name, :_s_anchored_pairwise); states, rhs,
                      parameters = :infer,
                      domain = Pair{Any,Tuple{Float64,Float64}}[θt => (0.05, 1.0)])
    Q = src.q * src.ξ
    byname = Dict{Symbol,Any}(:θ => src.θ, s => Q * _rs_ψ(src),
                              pname(s) => _ratio((Q * _rs_ψ(src, 1))^2, k̄, 0))
    for X in all_nodes
        byname[pname(X)] = Q * _rs_ψ(src, 1) * src.φ[X]
        byname[X] = src.pop[X]
    end
    ev = [Evidence(:paper, "Kiss, Kenah & Rempała 2023 (the dynamic-survival-analysis closure)"),
          _EVIDENCE_HERE]
    m = Semiconjugacy(:eb_to_pws, src.ode, tgt, _rs_map(tgt, byname, fname), Pair{Any,Any}[],
                      :semiconjugacy, :exact, ev)
    return (ode = tgt, morphism = m)
end

"""
    pairwise_image(sys::EdgeModelSystem) -> (ode::SymbolicODE, morphism::Semiconjugacy)

The S-anchored pairwise image of an edge-based system on a configuration network (M6, design
§D.5): the map

    π(θ, ξ, φ, pop) = (θ, [s] = qξψ(θ), [sX] = qξψ'(θ)φ_X, [ss] = q²ξ²ψ'(θ)²/ψ'(1), [X] = pop_X)

onto the pairwise model PW^S of the susceptible-centred pairs with the closure
[Z s J] = K_ψ(θ)[Zs][sJ]/[s], K_ψ = ψψ''/ψ'², and the auxiliary θ̇ = −Σ_r τ_r[sJ_r]ψ(θ)/([s]ψ'(θ))
(= −Σ_r τ_r[sJ_r]/(qξψ'(θ))). It is a semiconjugacy for every C² degree PGF ψ and every T_EB
model (exits and removals included; the removal sink is a species), on {ψ ≠ 0, ψ' ≠ 0} (Kiss,
Kenah & Rempała 2023). On a Poisson-type network K_ψ is the constant κ (M8), NodeBasedModels'
constant closure. Pairs are ordered, with Σ_{X,Y}[XY] = ⟨k⟩ per node.

The states of `ode` are named `θ`, the susceptible species `s`, the pairs `Symbol(s, X)` (`SI`,
`SR`, …, `SS`) and the node species `X`, as in NodeBasedModels, whose `PGFClosure` system should
equal `ode` up to renaming (`vector_fields_equal`). Check the map with `verify(morphism)`.
"""
pairwise_image(sys::EdgeModelSystem) =
    _pairwise_image(_reverse_source(sys, "pairwise_image(sys)"), "pairwise_image(sys)")

# ---------------------------------------------------------------------------------------------
# Pushing solutions forward
# ---------------------------------------------------------------------------------------------

# The values of the parameters of a solved system by name, with the seed factors q_<s> computed
# from the seed parameters.
function _rs_solution_parameters(sys::EdgeModelSystem, sol)
    vals = Dict{Symbol,Float64}()
    for p in ModelingToolkit.parameters(sys.system)
        v = try
            sol.ps[p]
        catch
            continue
        end
        v isa Real && (vals[_symname(p)] = Float64(v))
    end
    for (_, qv) in get(sys.metadata, :q, Dict{Symbol,Any}())
        e = qv.value
        subs = Dict{Any,Any}(x => vals[_symname(x)] for x in Symbolics.get_variables(e)
                             if haskey(vals, _symname(x)))
        n = _numvalue(Symbolics.substitute(e, subs; fold = Val(true)))
        n === nothing || (vals[_symname(qv.param)] = n)
    end
    return vals
end

"""
    pushforward(img::MassActionImage, sys::EdgeModelSystem, sol, tgrid)
        -> Dict{Symbol,Vector{Float64}}
    pushforward(m::Semiconjugacy, sys::EdgeModelSystem, sol, tgrid)

The target coordinates π(u(t)) of a reverse map along a solution `sol` of the edge-based system
`sys`, on `tgrid`, keyed by target state name: for example `pushforward(mass_action(sys; form =
:edge), sys, sol, tgrid)[:S]` is S(t) of Rempała's mass action along the edge-based trajectory.
The parameter values the map needs (the seed factor q = 1 − Σ seeds, rates and network
parameters) are read from the solution. `m` must be a map out of `symbolic_ode(sys)` (such as
`pairwise_image(sys).morphism`).
"""
NetworkEpiCore.pushforward(img::MassActionImage, sys::EdgeModelSystem, sol, tgrid) =
    NetworkEpiCore.pushforward(img.morphism, sys, sol, tgrid)

function NetworkEpiCore.pushforward(m::Semiconjugacy, sys::EdgeModelSystem, sol, tgrid)
    states = m.source.states
    return NetworkEpiCore.pushforward(m, t -> sol(t; idxs = states), tgrid;
                                      p = _rs_solution_parameters(sys, sol))
end

# ---------------------------------------------------------------------------------------------
# Natural transformations M1–M6 (registered from __init__)
# ---------------------------------------------------------------------------------------------

# Whether the reverse maps apply to a model on a network: an admissible T_EB model with one
# susceptible class and no layers, on a ConfigurationNetwork or WellMixed network (`which`
# narrows the degree distribution). Never throws.
function _reverse_applies(cm, net, which::Symbol)
    try
        cm isa ContactModel || (cm = contact_model(cm))
        (net isa ConfigurationNetwork || net isa WellMixed) || return false
        is_admissible(cm, :edge_based; network = net) || return false
        length(susceptible_species(cm)) == 1 || return false
        all(c -> c.layer === :all, contacts(cm)) || return false
        which === :well_mixed && return net isa WellMixed
        net isa ConfigurationNetwork || return false
        which === :configuration && return true
        pt = _rs_poisson_type(net.degrees)
        pt === nothing && return false
        which === :poisson && return _rs_is_one(pt.κ)
        which === :power_law && return !_rs_is_one(pt.κ)
        return false
    catch err
        err isa InterruptException && rethrow()
        return false
    end
end

function _reverse_component(cm, net, form::Symbol)
    cm isa ContactModel || (cm = contact_model(cm))
    fname = "natural transformation component (form = :$(form))"
    return _reverse_image(_reverse_source(cm, net, fname), form, fname).morphism
end

"""
    _register_reverse_transformations!()

Register M1–M6 (design §D.5) as NetworkEpiCore `NaturalTransformation`s from the edge-based
representation: `:well_mixed_unit` (M1, ⇒ `:mass_action`), `:poisson_iso` (M2, ⇒ `:mass_action`),
`:rempala` (M3, ⇒ `:mass_action`), `:power_law` (M4, ⇒ `:power_law_kinetics`),
`:general_kinetics` (M5, ⇒ `:general_kinetics`) and `:eb_to_pws` (M6, ⇒ `:s_anchored`). Each
component is computed from the per-reaction table `lift_contributions(cm, net)` (no MTK system is
compiled). Called from `__init__`.
"""
function _register_reverse_transformations!()
    ev = [_EVIDENCE_HERE]
    for (name, target, which, form, kind, extra) in (
            (:well_mixed_unit, :mass_action, :well_mixed, :exact, :conjugacy,
             [Evidence(:paper, "Miller, Slim & Volz 2012, Part II")]),
            (:poisson_iso, :mass_action, :poisson, :exact, :conjugacy, Evidence[]),
            (:rempala, :mass_action, :poisson, :edge, :semiconjugacy,
             [Evidence(:paper, "Rempała 2023, Thm 1 (SIR)"), Evidence(:lean, "NEP.rempala")]),
            (:power_law, :power_law_kinetics, :power_law, :exact, :conjugacy, Evidence[]),
            (:general_kinetics, :general_kinetics, :configuration, :general, :conjugacy,
             Evidence[]))
        register_transformation!(NaturalTransformation(name; source = :edge_based, target,
            applies = (cm, net) -> _reverse_applies(cm, net, which),
            component = (cm, net) -> _reverse_component(cm, net, form),
            kind, evidence = vcat(extra, ev)))
    end
    register_transformation!(NaturalTransformation(:eb_to_pws; source = :edge_based,
        target = :s_anchored,
        applies = (cm, net) -> _reverse_applies(cm, net, :configuration),
        component = function (cm, net)
            cm isa ContactModel || (cm = contact_model(cm))
            fname = "natural transformation component :eb_to_pws"
            return _pairwise_image(_reverse_source(cm, net, fname), fname).morphism
        end,
        kind = :semiconjugacy,
        evidence = [Evidence(:paper, "Kiss, Kenah & Rempała 2023"), _EVIDENCE_HERE]))
    return nothing
end

function __init__()
    _register_reverse_transformations!()
    return nothing
end
