# Owner: WP29 (DESIGN_NetworkEpiCore.md §A.3; work package in §G.2).
#
# `EdgeModelSystem`, the lowered edge-based model, moved here from src/builders.jl with its four
# fields unchanged (design §A.3: new data goes in `metadata`). Every system of EdgeBasedModels 0.2
# is built by the per-reaction assembler (src/lift/assembler.jl) or by one of the descriptor lifts
# that reuse it, and records `metadata[:kind] = :assembled`.

"""
    EdgeModelSystem(system, variables, observables[, metadata])

A lowered edge-based model: the compiled ModelingToolkit `system`, the state variables by name
(`:θ`, `:φ_I`, `:pop_I`, `:cumulative`, the alias `:R`, …), the observables by name (`:S`, `:I`,
`:φ_S`, `:edge_hazard`, …) and `metadata`. Systems built by [`edge_based`](@ref) and the factories
record (design §A.3):

- `:kind => :assembled`, `:form` (`:expanded` or `:compact`) and `:closure` (`:configuration`,
  `:well_mixed`, `:multitype`, `:multiplex`, `:clustered`, `:dynamic`, `:degree_correlated`,
  `:mfsh`, `:heterogeneous`, …);
- `:model` (the `ContactModel`), `:network` (the `NetworkDescriptor`), `:entry` (the default
  seeded state, when unique) and `:susceptible`;
- `:raw` (the uncompiled field, see `symbolic_ode(sys)`), `:contributions` (the per-reaction
  table), `:coords` and `:ic` (the initial-condition builder);
- `:seed_params` (the seed fractions `seed_<X>`, verified issue E26), `:q`, `:infected`, `:sinks`
  and `:parameter_defaults` (the values `solve_epidemic` uses when `p` does not give them).

Read solutions with [`compartment`](@ref)`(sys, sol, X)` and [`model_curves`](@ref).
"""
struct EdgeModelSystem
    system
    variables::Dict{Symbol, Any}
    observables::Dict{Symbol, Any}
    metadata::Dict{Symbol, Any}
end

EdgeModelSystem(system, variables::Dict{Symbol, Any}, observables::Dict{Symbol, Any}) =
    EdgeModelSystem(system, variables, observables, Dict{Symbol, Any}())

function Base.show(io::IO, sys::EdgeModelSystem)
    md = sys.metadata
    print(io, "EdgeModelSystem(")
    model = get(md, :model, nothing)
    model isa ContactModel && print(io, ":", model.name, ", ")
    print(io, get(md, :closure, get(md, :kind, :unknown)), " closure, ", length(sys.variables),
          " variables)")
end
