"""
    GoldenTools

Golden-file infrastructure for the EdgeBasedModels test suite (work package WP1 of
`DESIGN_NetworkEpiCore.md`).

Goldens freeze the numbers produced by EdgeBasedModels 0.1 (the working tree of 2026-09-26),
**bugs included**, so that the NetworkEpiCore refactor can prove it changes nothing it does not
mean to change. A golden is replaced only by the work package that owns its area, in a bug-fix
change that also adds a literature or simulation test (design §G.1). Cases whose numbers are known
to be wrong list the verified-issue ids (`VERIFIED_ISSUES.md`) in `issues`.

# Layout

```
test/golden/GoldenTools.jl        this module: case types, solving, I/O, comparison
test/golden/generate.jl           writes the golden files (see its header for usage)
test/golden/<area>/cases.jl       the case definitions of one area; evaluates to a Vector{GoldenCase}
test/golden/<area>/<case>.toml    metadata: description, issues, provenance, setup, structure, scalars
test/golden/<area>/<case>.csv     trajectory cases only: `t` and one column per recorded quantity
test/golden/<area>/v01/<case>.csv the EdgeBasedModels 0.1 numbers of a golden that was regenerated
                                  for a change of names or normalisation (see `check_v01`)
```

Each area directory is owned by the work package that later replaces that area (design §G.2):
`analysis` (WP19), `clustered` (WP20), `dynamic` (WP21), `multiplex` (WP22), and `core`,
`seir_multistage`, `multitype`, `categorical` (WP29). `eon/` holds external EoN references
written by `eon/generate_eon.py`, not by `generate.jl`.

# File formats

* CSV: comma separated, a header row `t,<column>,...`, then one row per saved time. Values are
  written with Julia's shortest round-trip `Float64` printing, so they read back bit for bit.
* TOML (`schema = 1`): `area`, `name`, `kind` (`"trajectory"` or `"scalars"`), `description`,
  `issues`, `notes`, `columns`; tables `[provenance]` (versions, git state), `[setup]` (every
  numeric input and the solver settings), `[check]` (`rtol`, `atol`), `[structure]` (sorted name
  sets and equation counts) and `[scalars]`.

# Comparison

Entry `x` of a fresh run matches golden `g` when `abs(x - g) <= atol + rtol * max(abs(x), abs(g))`
(two NaNs match; an infinity matches only the same infinity), with the tolerances recorded in the
file's `[check]` table (by default `rtol = 1e-8`, `atol = 1e-12`). Structural name sets, the
`[setup]` table and the metadata (`description`, `issues`, `notes`) must match exactly. After
editing only the metadata of a case in `cases.jl`, rewrite it with `generate.jl --metadata-only`,
which leaves every number and the provenance untouched.
Trajectories are generated with `OrdinaryDiffEq.Vern9` at `reltol = 1e-12`, `abstol = 1e-14`
on `t = 0:1:T`, i.e. more accurately than the `1e-10` the design asks for, so that later
reimplementations can be compared at `1e-10` relative.
"""
module GoldenTools

using Test
using TOML
using DelimitedFiles
using EdgeBasedModels
using ModelingToolkit
using Symbolics
import OrdinaryDiffEq

export GoldenCase, GoldenResult, GOLDEN_DIR, SOLVER_NAME, RELTOL, ABSTOL, CHECK_RTOL, CHECK_ATOL,
    numval, edge_system_trajectory, ode_system_trajectory, scalar_result, system_structure,
    edge_system_structure, load_cases, golden_areas, run_case, check_case, check_area,
    write_golden, read_golden_csv, compare_columns, golden_paths, update_golden_metadata,
    GOLDEN_METADATA_KEYS, join_notes, E26_NOTE, E26_FIXED_NOTE, V01_DIR, check_v01, within_type_columns

"""Directory that holds the golden areas (`test/golden`)."""
const GOLDEN_DIR = @__DIR__

"""Name of the ODE solver used for every golden trajectory."""
const SOLVER_NAME = "OrdinaryDiffEq.Vern9"
"""Relative tolerance of the golden ODE solves."""
const RELTOL = 1e-12
"""Absolute tolerance of the golden ODE solves."""
const ABSTOL = 1e-14
"""Default relative tolerance of a golden comparison (design §G.2, WP1: `1e-8`)."""
const CHECK_RTOL = 1e-8
"""Default absolute floor of a golden comparison, for entries that are (close to) zero."""
const CHECK_ATOL = 1e-12

"""
    GoldenResult(setup, t, columns, data, structure, scalars)

What one run of a [`GoldenCase`](@ref) produces.

* `setup::Dict{String,Any}`: every numeric input (rates, seed, time span, solver settings);
  written to the `[setup]` table and compared exactly on every check.
* `t::Vector{Float64}` and `data::Matrix{Float64}` (`length(t) × length(columns)`): the saved
  trajectories; both empty for scalar cases.
* `columns::Vector{String}`: the names of the columns of `data`.
* `structure::Dict{String,Any}`: structural facts (sorted name vectors, equation counts).
* `scalars::Dict{String,Float64}`: scalar outputs.
"""
struct GoldenResult
    setup::Dict{String, Any}
    t::Vector{Float64}
    columns::Vector{String}
    data::Matrix{Float64}
    structure::Dict{String, Any}
    scalars::Dict{String, Float64}
end

"""
    GoldenCase(area, name, kind, description, issues, notes, run)
    GoldenCase(area, name; kind = :trajectory, description, issues = String[], notes = "", run)

A reproducible computation whose output is frozen in `test/golden/<area>/<name>.{toml,csv}`.
`run` is a zero-argument function returning a [`GoldenResult`](@ref). `kind` is `:trajectory`
(a CSV is written) or `:scalars` (TOML only). `issues` lists the verified-issue ids whose wrong
behaviour this golden encodes; `notes` says how.
"""
struct GoldenCase
    area::String
    name::String
    kind::Symbol
    description::String
    issues::Vector{String}
    notes::String
    run::Function
end

function GoldenCase(area::AbstractString, name::AbstractString; kind::Symbol = :trajectory,
                    description::AbstractString, issues = String[], notes::AbstractString = "",
                    run::Function)
    kind in (:trajectory, :scalars) || throw(ArgumentError("kind must be :trajectory or :scalars, got :$kind"))
    occursin(r"^[A-Za-z0-9_]+$", name) || throw(ArgumentError("golden case names must match [A-Za-z0-9_]+, got $name"))
    return GoldenCase(String(area), String(name), kind, String(description), String.(collect(issues)),
                      String(notes), run)
end

# --- numeric helpers -----------------------------------------------------------------------------

"""
    numval(x) -> Float64

Convert a numeric or fully numeric symbolic value (for example an EBM `basic_reproduction_number`
built from numeric rates) to `Float64`. Leftover `exp(0)` factors are folded first. Throws an
`ArgumentError` if `x` still has free symbols.
"""
function numval(x)
    # `Symbolics.Num <: Real`, so test for it before the plain-number fast path.
    (x isa Number && !(x isa Symbolics.Num)) && return Float64(x)
    ex = Symbolics.substitute(Symbolics.Num(x), Dict(exp(Symbolics.Num(0)) => 1, exp(Symbolics.Num(0.0)) => 1))
    v = Symbolics.value(Symbolics.simplify(ex))
    (v isa Number && !(v isa Symbolics.Num)) && return Float64(v)
    isempty(Symbolics.get_variables(ex)) ||
        throw(ArgumentError("cannot convert an expression with free symbols to Float64: $ex"))
    f = Symbolics.build_function(ex; expression = Val{false})
    return Float64((f isa Tuple ? first(f) : f)())
end

_names(xs) = sort!([string(Symbolics.getname(x)) for x in xs])

"""
    system_structure(sys) -> Dict{String,Any}

Structural facts of a compiled ModelingToolkit system: sorted `unknowns`, `parameters` and
`observed` (left-hand sides) names, and `n_equations`.
"""
function system_structure(sys)
    return Dict{String, Any}(
        "unknowns" => _names(ModelingToolkit.unknowns(sys)),
        "parameters" => _names(ModelingToolkit.parameters(sys)),
        "observed" => _names([eq.lhs for eq in ModelingToolkit.observed(sys)]),
        "n_equations" => length(ModelingToolkit.equations(sys)),
    )
end

"""
    edge_system_structure(sys::EdgeModelSystem) -> Dict{String,Any}

[`system_structure`](@ref) of `sys.system` plus the sorted keys of `sys.variables` and
`sys.observables`: the "structural unknown-name sets" of design §G.2 (WP1).
"""
function edge_system_structure(sys::EdgeModelSystem)
    s = system_structure(sys.system)
    s["variables"] = sort!(string.(collect(keys(sys.variables))))
    s["observables"] = sort!(string.(collect(keys(sys.observables))))
    return s
end

_solver_setup() = Dict{String, Any}("solver" => SOLVER_NAME, "reltol" => RELTOL, "abstol" => ABSTOL,
                                    "saveat" => 1.0)

"""
    edge_system_trajectory(sys::EdgeModelSystem; T, seed_fraction, setup, extra = Dict(), op_extra = Dict(),
                           initial = nothing) -> GoldenResult

Solve `sys` from `default_initial_conditions(sys; seed_fraction)` (or, when `initial` is given, from
`default_initial_conditions(sys; initial)`, with `seed_fraction` only recorded in the setup), merged
with `op_extra` (e.g. values of symbolic network parameters), on `t = 0:1:T` and record every key of `sys.variables` and
`sys.observables` (observables win on a name clash, as in `compartment`). `extra` maps further
column names to functions `(sys, sol) -> vector`.
"""
function edge_system_trajectory(sys::EdgeModelSystem; T::Real, seed_fraction::Real,
                                setup::AbstractDict, extra::AbstractDict = Dict{String, Function}(),
                                op_extra::AbstractDict = Dict(), initial = nothing)
    ic0 = initial === nothing ? default_initial_conditions(sys; seed_fraction = seed_fraction) :
          default_initial_conditions(sys; initial = initial)
    ic = merge(ic0, op_extra)
    sol = solve_epidemic(sys; tspan = (0.0, Float64(T)), init = ic, solver = OrdinaryDiffEq.Vern9(),
                         saveat = 1.0, reltol = RELTOL, abstol = ABSTOL)
    string(sol.retcode) == "Success" || error("golden solve failed with retcode $(sol.retcode)")
    names = sort!(collect(union(keys(sys.variables), keys(sys.observables))))
    columns = String[string(n) for n in names]
    cols = Vector{Vector{Float64}}([Float64.(compartment(sys, sol, n)) for n in names])
    for (name, f) in sort!(collect(extra); by = first)
        push!(columns, String(name))
        push!(cols, Float64.(f(sys, sol)))
    end
    full_setup = merge(Dict{String, Any}(setup), _solver_setup(),
                       Dict{String, Any}("T" => Float64(T), "seed_fraction" => Float64(seed_fraction)))
    return GoldenResult(full_setup, Float64.(sol.t), columns, reduce(hcat, cols),
                        edge_system_structure(sys), Dict{String, Float64}())
end

"""
    ode_system_trajectory(sys, op, T; columns, setup, extra = Dict()) -> GoldenResult

Solve a compiled ModelingToolkit system from the operating point `op` (initial values and
parameters) on `t = 0:1:T`. `columns` maps column names to symbolic variables or expressions;
`extra` maps column names to functions `sol -> vector`.
"""
function ode_system_trajectory(sys, op, T::Real; columns::AbstractDict, setup::AbstractDict,
                               extra::AbstractDict = Dict{String, Function}())
    prob = OrdinaryDiffEq.ODEProblem(sys, op, (0.0, Float64(T)))
    sol = OrdinaryDiffEq.solve(prob, OrdinaryDiffEq.Vern9(); saveat = 1.0, reltol = RELTOL, abstol = ABSTOL)
    string(sol.retcode) == "Success" || error("golden solve failed with retcode $(sol.retcode)")
    names = String[]
    cols = Vector{Vector{Float64}}()
    for (name, var) in sort!(collect(columns); by = first)
        push!(names, String(name))
        push!(cols, Float64.(sol[var]))
    end
    for (name, f) in sort!(collect(extra); by = first)
        push!(names, String(name))
        push!(cols, Float64.(f(sol)))
    end
    full_setup = merge(Dict{String, Any}(setup), _solver_setup(), Dict{String, Any}("T" => Float64(T)))
    return GoldenResult(full_setup, Float64.(sol.t), names, reduce(hcat, cols), system_structure(sys),
                        Dict{String, Float64}())
end

"""
    scalar_result(setup, scalars; structure = Dict()) -> GoldenResult

A [`GoldenResult`](@ref) for a `:scalars` case. `scalars` maps names to real numbers (symbolic
values with no free symbols are converted with [`numval`](@ref)).
"""
function scalar_result(setup::AbstractDict, scalars::AbstractDict; structure::AbstractDict = Dict{String, Any}())
    s = Dict{String, Float64}(String(k) => numval(v) for (k, v) in scalars)
    return GoldenResult(Dict{String, Any}(setup), Float64[], String[], zeros(0, 0),
                        Dict{String, Any}(structure), s)
end

# --- cases ------------------------------------------------------------------------------------------

"""
    golden_areas(dir = GOLDEN_DIR) -> Vector{String}

The sorted names of the area directories that define cases (`<area>/cases.jl`).
"""
golden_areas(dir::AbstractString = GOLDEN_DIR) =
    sort!([d for d in readdir(dir) if isfile(joinpath(dir, d, "cases.jl"))])

"""
    load_cases(area; dir = GOLDEN_DIR) -> Vector{GoldenCase}

Evaluate `test/golden/<area>/cases.jl` in a fresh module and return its cases. The file must
evaluate to a vector of [`GoldenCase`](@ref)s whose `area` is `area`, with unique names.
"""
function load_cases(area::AbstractString; dir::AbstractString = GOLDEN_DIR)
    path = joinpath(dir, area, "cases.jl")
    isfile(path) || throw(ArgumentError("no golden area $area (missing $path)"))
    mod = Module(Symbol("GoldenCases_", area))
    Core.eval(mod, :(const GoldenTools = $GoldenTools))
    Core.eval(mod, :(using .GoldenTools))
    cases = Base.include(mod, path)
    cases isa AbstractVector{GoldenCase} ||
        throw(ArgumentError("$path must evaluate to a Vector{GoldenCase}, got $(typeof(cases))"))
    for c in cases
        c.area == area || throw(ArgumentError("case $(c.name) in $path declares area $(c.area)"))
    end
    names = [c.name for c in cases]
    allunique(names) || throw(ArgumentError("duplicate golden case names in $path"))
    return collect(GoldenCase, cases)
end

"""
    golden_paths(case; dir = GOLDEN_DIR) -> (toml, csv)
"""
golden_paths(case::GoldenCase; dir::AbstractString = GOLDEN_DIR) =
    (joinpath(dir, case.area, case.name * ".toml"), joinpath(dir, case.area, case.name * ".csv"))

"""
    run_case(case) -> GoldenResult

Run `case.run()` and validate the shape of its result.
"""
function run_case(case::GoldenCase)
    r = Base.invokelatest(case.run)   # the case file was included after the caller started
    r isa GoldenResult || error("golden case $(case.area)/$(case.name) returned $(typeof(r)), not a GoldenResult")
    if case.kind === :trajectory
        size(r.data) == (length(r.t), length(r.columns)) || error("golden case $(case.name): data has size $(size(r.data))")
        allunique(r.columns) || error("golden case $(case.name): duplicate column names")
        "t" in r.columns && error("golden case $(case.name): `t` is reserved for the time column")
    end
    return r
end

# --- I/O ----------------------------------------------------------------------------------------------

_normalise(d::AbstractDict) = TOML.parse(sprint(io -> TOML.print(io, Dict{String, Any}(d); sorted = true)))

function _provenance()
    versions = Dict{String, Any}("julia" => string(VERSION))
    for (name, m) in (("EdgeBasedModels", EdgeBasedModels), ("ModelingToolkit", ModelingToolkit),
                      ("Symbolics", Symbolics), ("OrdinaryDiffEq", OrdinaryDiffEq))
        v = pkgversion(m)
        versions[name] = v === nothing ? "unknown" : string(v)
    end
    repo = normpath(joinpath(GOLDEN_DIR, "..", ".."))
    try
        versions["git_head"] = strip(read(`git -C $repo rev-parse HEAD`, String))
        versions["git_dirty"] = !isempty(strip(read(`git -C $repo status --porcelain -- src`, String)))
    catch
        versions["git_head"] = "unknown"
    end
    return versions
end

function _write_toml(path::AbstractString, meta::AbstractDict)
    open(path, "w") do io
        println(io, "# Golden file written by test/golden/generate.jl. Do not edit by hand: a golden is")
        println(io, "# replaced only by the work package that owns its area (DESIGN_NetworkEpiCore.md, section G.1).")
        TOML.print(io, meta; sorted = true)
    end
    return path
end

"""
    GOLDEN_METADATA_KEYS

The TOML keys that hold a golden's metadata rather than its numbers: `description`, `issues`
and `notes`, taken from the case definition. [`update_golden_metadata`](@ref) rewrites exactly
these.
"""
const GOLDEN_METADATA_KEYS = ("description", "issues", "notes")

"""
    update_golden_metadata(case; dir = GOLDEN_DIR) -> Bool

Rewrite the metadata ([`GOLDEN_METADATA_KEYS`](@ref)) of the existing golden of `case` from
its definition, without running the case: setup, structure, scalars, columns, the CSV and the
provenance are left exactly as they are. Returns `true` if the file changed. Throws if the
golden does not exist or has a different `kind`.

This is how an issue id or a note is added to a golden whose numbers must stay frozen; running
the case again would instead freeze whatever the current source computes.
"""
function update_golden_metadata(case::GoldenCase; dir::AbstractString = GOLDEN_DIR)
    toml_path, _ = golden_paths(case; dir = dir)
    isfile(toml_path) || throw(ArgumentError("no golden $(case.area)/$(case.name) to update ($toml_path)"))
    meta = TOML.parsefile(toml_path)
    meta["kind"] == string(case.kind) ||
        throw(ArgumentError("golden $(case.area)/$(case.name) has kind $(meta["kind"]), the case has :$(case.kind)"))
    new = Dict{String, Any}("description" => case.description, "issues" => case.issues, "notes" => case.notes)
    all(k -> get(meta, k, nothing) == new[k], GOLDEN_METADATA_KEYS) && return false
    merge!(meta, new)
    _write_toml(toml_path, meta)
    return true
end

"""
    join_notes(parts::AbstractString...) -> String

Join the non-empty `parts` with single spaces: the `notes` of a case that records several issues.
"""
join_notes(parts::AbstractString...) = join(filter(!isempty, collect(String, parts)), " ")

"""
    E26_NOTE

Note shared by every golden whose `[structure]` pins a legacy seed-parameter name. The legacy
builders name the seed fraction `ρ` (`ρ_<type>` in multitype builds, `ρ_<prefix>` in categorical
ones), which silently merges with a user parameter of the same name (verified issue E26). Design
§A.3 renames the seed parameters `seed_<X>`, so the owner of the area replaces these name sets
deliberately.
"""
const E26_NOTE = "E26: [structure].parameters pins the legacy seed-parameter name (ρ, or ρ_<type> / ρ_<prefix>), " *
                 "which silently merges with a user parameter of the same name; design A.3 renames it seed_<X>."

"""
    E26_FIXED_NOTE

Note shared by the goldens regenerated by WP29 when the legacy builders were deleted and the
factories and legacy entry points went through the per-reaction assembler. Verified issue E26 is
fixed (the seed parameters are `seed_<X>`, one per node species, and never merge with a user's
`ρ`), and the design adds names: the cumulative accumulator of §J.8 (a variable and an equation),
the `:infectious` observable, and `pop_<X>`/`φ_S` in the compact form. The numbers of every 0.1
column are unchanged; the area's legacy suite checks them against the 0.1 CSVs in `<area>/v01/`
with [`check_v01`](@ref).
"""
const E26_FIXED_NOTE = "E26 fixed (WP29): regenerated when the legacy builders were deleted; the seed parameters are " *
                       "seed_<X> (one per node species), and the cumulative accumulator (design J.8), the :infectious " *
                       "observable and, in the compact form, pop_<X> and φ_S are new names. The numbers of every 0.1 " *
                       "column are unchanged, checked against <area>/v01/ by check_v01 in the area's legacy suite."

"""Subdirectory of an area that holds the EdgeBasedModels 0.1 CSVs of regenerated goldens."""
const V01_DIR = "v01"

"""
    check_v01(case; columns = Dict(), dir = GOLDEN_DIR, rtol = CHECK_RTOL, atol = CHECK_ATOL)

Re-run `case` and compare it, inside a `@testset`, with the EdgeBasedModels 0.1 numbers of the
same computation kept in `<area>/v01/<name>.csv` (the golden before it was regenerated for a
change of names or normalisation, never for a change of numbers). Every 0.1 column must be
reproduced: by the fresh column of the same name, or, when `columns` has an entry for it, by
`columns[name](fresh)`, where `fresh` is a `Dict{String,Vector{Float64}}` of the fresh run's
columns (e.g. `f -> 2 .* f["pop_I_a"]` for a within-type fraction when the type has size 1/2).
The time grids must be equal. Returns nothing.
"""
function check_v01(case::GoldenCase; columns::AbstractDict = Dict{String,Function}(),
                   dir::AbstractString = GOLDEN_DIR, rtol::Real = CHECK_RTOL, atol::Real = CHECK_ATOL)
    @testset "0.1 numbers of $(case.area)/$(case.name)" begin
        path = joinpath(dir, case.area, V01_DIR, case.name * ".csv")
        @test isfile(path)
        if isfile(path)
            header, data = read_golden_csv(path)
            r = run_case(case)
            @test size(data, 1) == length(r.t) && data[:, 1] == r.t
            fresh = Dict{String,Vector{Float64}}(c => r.data[:, j] for (j, c) in enumerate(r.columns))
            for (j, name) in enumerate(header[2:end])
                new = haskey(columns, name) ? columns[name](fresh) : get(fresh, name, nothing)
                new === nothing && @error "0.1 column $(name) of $(case.area)/$(case.name) is not reproduced"
                ok = new !== nothing && size(data, 1) == length(r.t) &&
                     compare_columns(new, data[:, j + 1]; rtol, atol).ok
                ok || new === nothing ||
                    @error "0.1 column $(name) of $(case.area)/$(case.name) differs" c = compare_columns(new, data[:, j + 1]; rtol, atol)
                @test ok
            end
        end
    end
    return nothing
end

"""
    within_type_columns(sizes::AbstractDict{Symbol}, stages; infectious = [:I], recovered = :R)
        -> Dict{String,Function}

The `columns` argument of [`check_v01`](@ref) for a 0.1 multitype golden. 0.1 reported node-level
quantities as fractions of each node type; 0.2 reports fractions of all nodes (design §J.6). For
every type `a` (with size `sizes[a]`) this maps the 0.1 columns `S_a` and `pop_<X>_a` (X in
`stages`) to the 0.2 columns divided by `sizes[a]`, the 0.1 `I_a` to the sum of the `infectious`
populations and `R_a` to the `recovered` population, both divided by `sizes[a]`.
"""
function within_type_columns(sizes::AbstractDict{Symbol}, stages; infectious = [:I], recovered::Symbol = :R)
    cols = Dict{String,Function}()
    for (a, n) in sizes
        cols["S_$a"] = f -> f["S_$a"] ./ n
        for X in stages
            cols["pop_$(X)_$a"] = f -> f["pop_$(X)_$a"] ./ n
        end
        cols["I_$a"] = f -> sum(f["pop_$(X)_$a"] for X in infectious) ./ n
        cols["R_$a"] = f -> f["pop_$(recovered)_$a"] ./ n
    end
    return cols
end

"""
    write_golden(case, result; dir = GOLDEN_DIR)

Write `<area>/<name>.toml` (and `<area>/<name>.csv` for trajectory cases).
"""
function write_golden(case::GoldenCase, r::GoldenResult; dir::AbstractString = GOLDEN_DIR)
    toml_path, csv_path = golden_paths(case; dir = dir)
    mkpath(dirname(toml_path))
    meta = Dict{String, Any}(
        "schema" => 1,
        "area" => case.area,
        "name" => case.name,
        "kind" => string(case.kind),
        "description" => case.description,
        "issues" => case.issues,
        "notes" => case.notes,
        "generated_by" => "test/golden/generate.jl",
        "provenance" => _provenance(),
        "setup" => r.setup,
        "check" => Dict{String, Any}("rtol" => CHECK_RTOL, "atol" => CHECK_ATOL),
        "structure" => r.structure,
        "scalars" => r.scalars,
        "columns" => r.columns,
    )
    _write_toml(toml_path, meta)
    if case.kind === :trajectory
        open(csv_path, "w") do io
            println(io, join(["t"; r.columns], ","))
            writedlm(io, hcat(r.t, r.data), ',')
        end
    end
    return toml_path
end

"""
    read_golden_csv(path) -> (header::Vector{String}, data::Matrix{Float64})
"""
function read_golden_csv(path::AbstractString)
    data, header = readdlm(path, ',', Float64, '\n'; header = true)
    return String.(vec(header)), data
end

"""
    compare_columns(new, golden; rtol, atol) -> NamedTuple

Entrywise comparison of two equally sized arrays. Returns `(ok, maxabs, maxrel, worst)` where
`worst` is the linear index of the largest scaled error `|x-g| / (atol + rtol*max(|x|,|g|))`.

Non-finite entries match only exactly: two NaNs match, and `±Inf` matches only the same `±Inf`.
A NaN against a number gives `ok = false` with `maxabs = maxrel = NaN`; an infinity against a
finite value or the opposite infinity gives `ok = false` with `maxabs = maxrel = Inf`. In both
cases `worst` is the index of the first such entry.
"""
function compare_columns(new::AbstractArray, golden::AbstractArray; rtol::Real = CHECK_RTOL, atol::Real = CHECK_ATOL)
    size(new) == size(golden) || return (ok = false, maxabs = Inf, maxrel = Inf, worst = 0)
    maxabs = 0.0
    maxrel = 0.0
    worst_scaled = -1.0
    worst = 0
    for i in eachindex(new, golden)
        x, g = Float64(new[i]), Float64(golden[i])
        (isnan(x) && isnan(g)) && continue
        (isnan(x) || isnan(g)) && return (ok = false, maxabs = NaN, maxrel = NaN, worst = i)
        # With an infinite entry the scaled error below is Inf/Inf = NaN, which no `>` comparison
        # would ever flag, so infinities are decided here: they match only the same infinity.
        if isinf(x) || isinf(g)
            x == g && continue
            return (ok = false, maxabs = Inf, maxrel = Inf, worst = i)
        end
        x == g && continue    # exact match; also avoids 0/0 when atol = 0 and x = g = 0
        d = abs(x - g)
        scale = max(abs(x), abs(g))
        maxabs = max(maxabs, d)
        scale > 0 && (maxrel = max(maxrel, d / scale))
        scaled = d / (atol + rtol * scale)
        if scaled > worst_scaled
            worst_scaled = scaled
            worst = i
        end
    end
    return (ok = worst_scaled <= 1, maxabs = maxabs, maxrel = maxrel, worst = worst)
end

# --- checking --------------------------------------------------------------------------------------------

"""
    check_case(case; dir = GOLDEN_DIR)

Re-run `case` and compare it with its golden files inside a `@testset`: the metadata
(`description`, `issues`, `notes`) and the recorded setup (exactly), the columns and time grid,
every trajectory column and every scalar (at the file's `[check]` tolerances), and every
structural name set (exactly).
"""
function check_case(case::GoldenCase; dir::AbstractString = GOLDEN_DIR)
    @testset "golden $(case.area)/$(case.name)" begin
        toml_path, csv_path = golden_paths(case; dir = dir)
        have_files = isfile(toml_path) && (case.kind === :scalars || isfile(csv_path))
        have_files || @error "missing golden files for $(case.area)/$(case.name); run test/golden/generate.jl"
        @test have_files
        if have_files
            meta = TOML.parsefile(toml_path)
            rtol = Float64(meta["check"]["rtol"])
            atol = Float64(meta["check"]["atol"])
            @test meta["kind"] == string(case.kind)
            for (k, v) in (("description", case.description), ("issues", case.issues), ("notes", case.notes))
                same = get(meta, k, nothing) == v
                same || @error "metadata of $(case.area)/$(case.name) differs from cases.jl; if only the metadata " *
                               "changed, run test/golden/generate.jl --metadata-only" key = k golden = get(meta, k, missing) new = v
                @test same
            end
            r = run_case(case)
            @test _normalise(r.setup) == meta["setup"]
            @test sort(collect(keys(r.structure))) == sort(collect(keys(meta["structure"])))
            for (k, v) in sort!(collect(meta["structure"]); by = first)
                same = haskey(r.structure, k) && _normalise(Dict(k => r.structure[k]))[k] == v
                same || @error "structure mismatch in $(case.area)/$(case.name)" key = k golden = v new = get(r.structure, k, missing)
                @test same
            end
            @test sort(collect(keys(r.scalars))) == sort(collect(keys(meta["scalars"])))
            for (k, v) in sort!(collect(meta["scalars"]); by = first)
                c = compare_columns([get(r.scalars, k, NaN)], [Float64(v)]; rtol = rtol, atol = atol)
                c.ok || @error "scalar mismatch in $(case.area)/$(case.name)" key = k golden = v new = get(r.scalars, k, missing)
                @test c.ok
            end
            if case.kind === :trajectory
                header, data = read_golden_csv(csv_path)
                @test header == ["t"; r.columns]
                @test Vector{String}(meta["columns"]) == r.columns
                @test size(data, 1) == length(r.t) && data[:, 1] == r.t
                if header == ["t"; r.columns] && size(data, 1) == length(r.t)
                    for (j, col) in enumerate(r.columns)
                        c = compare_columns(r.data[:, j], data[:, j + 1]; rtol = rtol, atol = atol)
                        c.ok || @error "trajectory mismatch in $(case.area)/$(case.name)" column = col maxabs = c.maxabs maxrel = c.maxrel t = r.t[max(c.worst, 1)]
                        @test c.ok
                    end
                end
            end
        end
    end
end

"""
    check_area(area; dir = GOLDEN_DIR)

Check every case of `area` and that the area directory holds no golden file without a case.
"""
function check_area(area::AbstractString; dir::AbstractString = GOLDEN_DIR)
    @testset "goldens: $area" begin
        cases = load_cases(area; dir = dir)
        @test !isempty(cases)
        expected = Set{String}()
        for c in cases
            push!(expected, c.name * ".toml")
            c.kind === :trajectory && push!(expected, c.name * ".csv")
        end
        present = Set(f for f in readdir(joinpath(dir, area)) if endswith(f, ".toml") || endswith(f, ".csv"))
        orphans = sort!(collect(setdiff(present, expected)))
        isempty(orphans) || @error "golden files without a case in $area" orphans
        @test isempty(orphans)
        for c in cases
            check_case(c; dir = dir)
        end
    end
end

end # module GoldenTools
