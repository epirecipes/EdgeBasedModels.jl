# Owner: WP14 (DESIGN_NetworkEpiCore.md §A.3, §A.7; work package in §G.2).
#
# Converters between the legacy EdgeBasedModels 0.1 objects and NetworkEpiCore's model and
# network objects, plus the two helpers every legacy lowering path shares:
#
# - `contact_model(::DiseaseProgression)` and `DiseaseProgression(::ContactModel)` (both ways;
#   the latter throws for what the legacy type cannot express);
# - `contact_model` of the legacy model types, and constructors of the legacy model types that
#   accept a `ContactModel` (so `StaticConfigurationModel(pgf, sir_model())` keeps working now
#   that `sir_model` returns a ContactModel);
# - network conversions (`ConfigurationNetwork(::DegreePGF)`, `DegreePGF(::DegreeDistribution)`
#   in pgf.jl, `ClusteredNetwork(::ClusteredPGF)` and `ClusteredPGF(::ClusteredDegree)`);
# - `_lift_rate`: Symbol and Expr rates become ModelingToolkit parameters through
#   NetworkEpiCore's `as_parameter`, in one place (verified issue E10), for the assembler and the
#   legacy analysis functions, so a user's progression keeps its Symbols; a parameter with a model default
#   carries it, as Catalyst's parameters did in 0.1 (`_rate_defaults` reads such defaults back).
#   (The 0.1 check that no parameter is named like a builder's seed parameter ρ, verified issue
#   E26, is gone with the builders: the seed parameters are now named `seed_<X>`.)

# --- ContactModel <-> DiseaseProgression ---------------------------------------------------------

"""
    contact_model(prog::DiseaseProgression; name = :disease_progression) -> ContactModel
    contact_model(m::StaticConfigurationModel)        # also Clustered- and DynamicConfigurationModel

The `ContactModel` of a legacy disease progression: one contact `S + X → entry + X` for every
stage X with a non-zero transmission rate (at that per-contact rate) and one node transition per
`DiseaseTransition`, with the susceptible state as the only susceptible species and the species
ordered as the progression (`S`, then its stages). The numeric default values that symbolic rate
parameters carry (Catalyst's `@parameters τ = 0.3`, the way 0.1 kept defaults) become the model's
`parameter_defaults`. No information is lost: `DiseaseProgression(contact_model(prog))` reproduces
`prog`. The methods on the legacy model types convert their progression (the network is not part
of a `ContactModel`).
"""
function contact_model(prog::DiseaseProgression; name::Symbol = :disease_progression)
    S = prog.susceptible
    cs = Contact[Contact(S, st.name, prog.entry, st.transmission_rate)
                 for st in prog.stages if !_is_zero_rate(st.transmission_rate)]
    ts = NodeTransition[NodeTransition(tr.source, tr.target, tr.rate) for tr in prog.transitions]
    return ContactModel(name; contacts = cs, transitions = ts,
                        species = vcat(S, Symbol[st.name for st in prog.stages]),
                        susceptible = [S], defaults = _rate_defaults(prog),
                        provenance = Provenance(:legacy_ebm; method = :explicit,
                            assumptions = ["converted from an EdgeBasedModels DiseaseProgression " *
                                           "(one contact per transmitting stage, entry $(prog.entry))"]))
end

contact_model(m::StaticConfigurationModel; kw...) = contact_model(m.progression; kw...)
contact_model(m::ClusteredConfigurationModel; kw...) = contact_model(m.progression; kw...)
contact_model(m::DynamicConfigurationModel; kw...) = contact_model(m.progression; kw...)

function DiseaseProgression(cm::ContactModel)
    rate_convention(cm) isa PerContact || throw(ArgumentError(
        "DiseaseProgression(:$(cm.name)): the contact rates use the $(rate_convention(cm)) " *
        "convention, which needs the mean degree of a network to become per-contact rates; " *
        "use DiseaseProgression(cm, net)"))
    return _with_rate_defaults(_legacy_progression(cm, Any[c.rate for c in contacts(cm)]),
                               parameter_defaults(cm))
end

"""
    DiseaseProgression(cm::ContactModel, net::NetworkDescriptor)

As `DiseaseProgression(cm)`, with the contact rates converted to per-contact rates on `net` by
NetworkEpiCore's `per_contact_rates` (needed for frequency- and density-dependent models).
"""
DiseaseProgression(cm::ContactModel, net::NetworkDescriptor) =
    _with_rate_defaults(_legacy_progression(cm, per_contact_rates(cm, net)), parameter_defaults(cm))

# `context` names the operation in error messages; `hint` says what to use instead.
function _legacy_progression(cm::ContactModel, τs::AbstractVector;
                             context::AbstractString = "DiseaseProgression(:$(cm.name))",
                             hint::AbstractString = "pass the ContactModel itself to " *
                                 "NodeBasedModels.node_based or NetworkOutbreaks.simulate, which " *
                                 "accept it, or to edge_based, which lifts it where the " *
                                 "per-reaction edge-based assembler is available and otherwise " *
                                 "says why it cannot")
    cannot(what) = throw(ArgumentError("$context: $what, which the legacy DiseaseProgression " *
                                       "cannot express; $hint"))
    Σ = susceptible_species(cm)
    length(Σ) == 1 || cannot(isempty(Σ) ? "the model has no susceptible class" :
                             "the model has $(length(Σ)) susceptible classes ($(join(Σ, ", ")))")
    S = only(Σ)
    cs = contacts(cm)
    rates = Dict{Symbol,Any}()
    for (c, τ) in zip(cs, τs)
        c.recipient === S || cannot("contact `$(c.name)` has the recipient $(c.recipient), " *
                                    "which is not the susceptible class $S")
        c.layer === :all || cannot("contact `$(c.name)` acts on the layer :$(c.layer) only")
        rates[c.infector] = τ
    end
    entries = unique(Symbol[c.product for c in cs])
    length(entries) <= 1 || cannot("infection has several entry states ($(join(entries, ", "))): " *
                                   "branching at infection or several strains")
    for t in node_transitions(cm)
        t.to === nothing && cannot("`$(t.name)` removes nodes ($(t.from) → ∅)")
        t.from === S && cannot("`$(t.name)` is an exit out of the susceptible class ($S → $(t.to))")
    end
    stages = DiseaseStage[DiseaseStage(X; transmission_rate = get(rates, X, 0))
                          for X in species_names(cm) if X !== S]
    transitions = DiseaseTransition[DiseaseTransition(t.from, t.to, t.rate) for t in node_transitions(cm)]
    return DiseaseProgression(stages, transitions; susceptible = S,
                              entry = isempty(entries) ? nothing : only(entries))
end

# --- Legacy model types built from a ContactModel -----------------------------------------------

"""
    StaticConfigurationModel(pgf::DegreePGF, progression)
    StaticConfigurationModel(d::DegreeDistribution, progression)

The legacy static configuration-model EBCM: a degree PGF and a disease model. `progression` is
a [`DiseaseProgression`](@ref) or a NetworkEpiCore `ContactModel` (converted with
`DiseaseProgression(cm, ConfigurationNetwork(pgf))`); a NetworkEpiCore degree distribution is
converted with [`DegreePGF`](@ref). Build it with `build_edge_system`, or use
`edge_based(model, ConfigurationNetwork(d))` directly.
"""
StaticConfigurationModel(pgf::DegreePGF, cm::ContactModel) =
    StaticConfigurationModel(pgf, DiseaseProgression(cm, ConfigurationNetwork(pgf)))
StaticConfigurationModel(d::DegreeDistribution, m::Union{DiseaseProgression,ContactModel}) =
    StaticConfigurationModel(DegreePGF(d), m)

"""
    ClusteredConfigurationModel(pgf::ClusteredPGF, progression)

The legacy clustered EBCM (triangle degrees from `pgf`); `progression` is a
[`DiseaseProgression`](@ref) or a per-contact `ContactModel`.
"""
ClusteredConfigurationModel(pgf::ClusteredPGF, cm::ContactModel) =
    ClusteredConfigurationModel(pgf, DiseaseProgression(cm))

"""
    DynamicConfigurationModel(pgf::DegreePGF, progression, η₁, η₂)

The legacy dynamic-network EBCM (edge formation rate η₁, breaking rate η₂); `progression` is a
[`DiseaseProgression`](@ref) or a per-contact `ContactModel`.
"""
DynamicConfigurationModel(pgf::DegreePGF, cm::ContactModel, η₁, η₂) =
    DynamicConfigurationModel(pgf, DiseaseProgression(cm), η₁, η₂)

"""
    MultiTypeConfigurationModel(; types, pgfs, progression, contact_matrix = Dict())

The legacy multitype EBCM: one [`MultivariatePGF`](@ref) per type, one disease model shared by
all types (a [`DiseaseProgression`](@ref) or a per-contact `ContactModel`), and optional
per-(infector type, recipient type) multipliers of the transmission rate (default 1).
"""
function MultiTypeConfigurationModel(;
    types::Vector{Symbol},
    pgfs::Dict{Symbol, MultivariatePGF},
    progression::Union{DiseaseProgression,ContactModel},
    contact_matrix::Dict = Dict{Tuple{Symbol,Symbol}, Any}(),
)
    prog = progression isa ContactModel ? DiseaseProgression(progression) : progression
    for type in types
        haskey(pgfs, type) || throw(ArgumentError("missing PGF for type $type"))
        Set(pgfs[type].types) == Set(types) ||
            throw(ArgumentError("PGF for type $type must have variables for all types: $types"))
    end
    # Fill missing contact matrix entries with 1 (homogeneous mixing)
    filled = Dict{Tuple{Symbol,Symbol}, Any}()
    for j in types, l in types
        filled[(j, l)] = get(contact_matrix, (j, l), 1)
    end
    return MultiTypeConfigurationModel(types, pgfs, prog, filled)
end

# --- Networks ------------------------------------------------------------------------------------

"""
    ConfigurationNetwork(pgf::DegreePGF)

A NetworkEpiCore configuration network whose degree distribution is the legacy PGF itself (a
`DegreePGF` is a `DegreeDistribution`), so the edge-based lift reuses its exact symbolic
expression. NetworkOutbreaks and scenario hashing use the PGF's provenance distribution.
"""
NetworkEpiCore.ConfigurationNetwork(pgf::DegreePGF) = ConfigurationNetwork{DegreePGF}(pgf)

"""
    ClusteredNetwork(g::ClusteredPGF)

The NetworkEpiCore clustered network of a legacy clustered PGF, from its provenance
`ClusteredDegree` (set by `clustered_pgf` and `clustered_poisson_pgf`); an error without it.
"""
function NetworkEpiCore.ClusteredNetwork(g::ClusteredPGF)
    g.joint === nothing && throw(ArgumentError(
        "ClusteredNetwork(::ClusteredPGF): this ClusteredPGF has no ClusteredDegree provenance " *
        "(build it with clustered_pgf or clustered_poisson_pgf, or pass a ClusteredDegree)"))
    return ClusteredNetwork(g.joint)
end

"""
    ClusteredPGF(cd::ClusteredDegree; single_var = :x, triangle_var = :y)
    ClusteredPGF(net::ClusteredNetwork; kw...)

The legacy symbolic clustered PGF g(x, y) of a NetworkEpiCore clustered degree law. Independent
Poisson singles and triangles give exactly `clustered_poisson_pgf`, a joint matrix exactly
`clustered_pgf`; other laws use NetworkEpiCore's closed-form `pgf(cd, x, y)`.
"""
function ClusteredPGF(cd::ClusteredDegree; single_var::Symbol = :x, triangle_var::Symbol = :y)
    j = cd.joint
    if j isa Tuple{PoissonDegree,PoissonDegree}
        return clustered_poisson_pgf(j[1].mean, j[2].mean; single_var, triangle_var)
    elseif j isa AbstractMatrix
        return clustered_pgf(j; single_var, triangle_var)
    end
    x = only(@variables $(single_var))
    y = only(@variables $(triangle_var))
    return ClusteredPGF(x, y, pgf(cd, x, y), cd)
end
ClusteredPGF(net::ClusteredNetwork; kw...) = ClusteredPGF(net.joint; kw...)

# --- Symbol and Expr rates become parameters (E10) ------------------------------------------------

const _NO_DEFAULTS = Dict{Symbol,Float64}()

# A rate as the assembler needs it: numbers and symbolic expressions unchanged, a Symbol the
# parameter of that name (`as_parameter`, equal to `@parameters τ`), an Expr the symbolic
# expression with its parameters replaced by `as_parameter` and `t` by the ModelingToolkit time.
# A parameter named in `defaults` carries its default value as metadata (`@parameters τ = 0.3`),
# which ModelingToolkit uses when no value is given: the way 0.1 kept Catalyst's defaults.
function _lift_rate(r::Symbol; defaults::AbstractDict = _NO_DEFAULTS)
    r === :t && throw(ArgumentError(
        "a rate named t: t denotes time in NetworkEpiCore rates; rename the parameter, or write a " *
        "time-dependent rate as an expression such as :(τ0 * exp(-a * t))"))
    x = as_parameter(r)
    return haskey(defaults, r) ? Symbolics.setdefaultval(x, defaults[r]) : x
end
function _lift_rate(r::Expr; defaults::AbstractDict = _NO_DEFAULTS)
    x = as_parameter(r; t = t_nounits)              # validates the expression
    names = rate_parameters(r)
    any(n -> haskey(defaults, n), names) || return x
    return rate_value(r, Dict{Symbol,Any}(n => _lift_rate(n; defaults) for n in names); t = t_nounits)
end
_lift_rate(r; defaults::AbstractDict = _NO_DEFAULTS) = r

# `DiseaseProgression(cm)`: the rates that use a parameter with a default become symbolic, with
# the default attached (the legacy type has no field for defaults); the others keep their Symbols.
function _with_rate_defaults(prog::DiseaseProgression, defaults::AbstractDict)
    isempty(defaults) && return prog
    keep(r) = (r isa Union{Symbol,Expr} && any(n -> haskey(defaults, n), _parameter_names(r))) ?
              Symbolics.unwrap(_lift_rate(r; defaults)) : r
    return DiseaseProgression(prog.susceptible, prog.entry,
        DiseaseStage[DiseaseStage(s.name, keep(s.transmission_rate)) for s in prog.stages],
        DiseaseTransition[DiseaseTransition(t.source, t.target, keep(t.rate)) for t in prog.transitions])
end

# The numeric defaults carried by the symbolic parameters of a progression's rates (Catalyst's
# `@parameters τ = 0.3`, or `_with_rate_defaults`), by name.
function _rate_defaults(prog::DiseaseProgression)
    defaults = Dict{Symbol,Float64}()
    for r in Iterators.flatten(((s.transmission_rate for s in prog.stages),
                                (t.rate for t in prog.transitions)))
        _collect_rate_defaults!(defaults, r)
    end
    return defaults
end
_collect_rate_defaults!(defaults, r) = defaults
function _collect_rate_defaults!(defaults, r::Union{Symbolics.Num,Symbolics.SymbolicUtils.BasicSymbolic})
    for v in Symbolics.get_variables(r)
        Symbolics.hasmetadata(v, Symbolics.VariableDefaultValue) || continue
        val = _numeric_default(Symbolics.getmetadata(v, Symbolics.VariableDefaultValue))
        name = Symbol(Symbolics.getname(v))
        (val === nothing || name === :t) || (defaults[name] = val)
    end
    return defaults
end
# A default given as a number (a default that is an expression of other parameters is skipped).
_numeric_default(x::Symbolics.Num) = _numeric_default(Symbolics.unwrap(x))
_numeric_default(x::Real) = Float64(x)
_numeric_default(x) = nothing

# --- Parameter names ------------------------------------------------------------------------------

# The names of the parameters of a rate or a symbolic expression (time excluded).
_parameter_names(r::Symbol) = r === :t ? Symbol[] : [r]
_parameter_names(r::Expr) = Symbol[_pname(p) for p in rate_parameters(r)]
_parameter_names(r::Symbolics.Num) = _symbolic_names(r)
_parameter_names(r::Symbolics.SymbolicUtils.BasicSymbolic) = _symbolic_names(r)
_parameter_names(r) = Symbol[]      # numbers (and, for dynamic models, rate functions)
_symbolic_names(x) = Symbol[n for n in (Symbol(Symbolics.getname(v)) for v in Symbolics.get_variables(x))
                            if n !== :t]
_pname(p::Symbol) = p
_pname(p) = Symbol(Symbolics.getname(p))
