# Shared set-up for the EdgeBasedModels.jl vignettes (E01–E16).
#
# Include it from a page with
#
#     include(joinpath(@__DIR__, "..", "_shared", "setup.jl"))
#
# (quarto runs each page with its own directory as the working directory, so
# `include("../_shared/setup.jl")` works as well). It carries no model code: the shared first cell
# of DESIGN §E.5 stays textually in each page, so that E01 and N01 can be diffed. What lives here:
#
#   * the strict summary cache (NETEPI_STRICT_CACHE=1 unless the caller set it): a page never
#     falls back to a user cache or to a fresh ensemble;
#   * the canonical anchors (R0 = 2, γ = 1/4, τ = 1/6) as named constants;
#   * plot defaults for every page;
#   * `reference_note(sc, ref)`: the one-line statement of N, runs, graph draws, conditioning and
#     P(major) (or P(survival), named by `kept_label`) that §F rule 2 requires next to every
#     simulation comparison;
#   * `mdtable(header, rows)`: a Markdown table for numbers printed by code (§F rule 3);
#   * `lean_cite(name)`: a Lean theorem name, checked against NetworkEpiCore's CITABLE.txt
#     (§F rule 4); an unlisted name is an error, so a page cannot cite it by accident.

get!(ENV, "NETEPI_STRICT_CACHE", "1")
get!(ENV, "GKSwstype", "100")          # headless GR

using Markdown
using Printf
using Plots

"Canonical anchors of the shared scenarios (DESIGN §E.2): basic reproduction number."
const R0_ANCHOR = 2.0
"Canonical anchors of the shared scenarios (DESIGN §E.2): recovery rate γ."
const GAMMA_ANCHOR = 1 / 4
"Canonical anchors of the shared scenarios (DESIGN §E.2): per-contact transmission rate τ."
const TAU_ANCHOR = 1 / 6

gr()
default(; size = (720, 440), dpi = 150, linewidth = 2, framestyle = :box, legend = :best,
        titlefontsize = 11, guidefontsize = 10, tickfontsize = 9, legendfontsize = 8)

"""
    condition_label(c) -> String

The conditioning rule of a scenario (`sc.sim.condition`) as text, without the module prefix:
`"MajorOutbreak(0.05)"`, `"Survival()"` or `"Unconditioned()"`.
"""
condition_label(c) = replace(sprint(show, c), r"^(?:\w+\.)+" => "")

"""
    kept_label(c) -> (runs, probability)

How to name the runs that satisfy the conditioning rule `c` (`sc.sim.condition`) and the fraction
`p_major = n_major/nsims` of a summary: `("major runs", "P(major)")` for `MajorOutbreak`,
`("surviving runs", "P(survival)")` for `Survival()` (an endemic SIS/SIRS ensemble keeps the runs
still infected at the horizon, so the fraction is a survival probability, not a major-outbreak
probability), and `("runs kept", "P(kept)")` for `Unconditioned()`, where every run is kept.
"""
function kept_label(c)
    lab = condition_label(c)
    startswith(lab, "MajorOutbreak") && return ("major runs", "P(major)")
    startswith(lab, "Survival") && return ("surviving runs", "P(survival)")
    return ("runs kept", "P(kept)")
end

_fmt(x::Integer) = string(x)
_fmt(x::AbstractFloat) = isfinite(x) ? @sprintf("%.4g", x) : string(x)
_fmt(x) = string(x)

"""
    _is_no_alignment(a) -> Bool

Whether the alignment rule `a` (`sc.sim.align`) is NetworkEpiCore's `NoAlignment()`, decided by
its type (not by its printed text, which carries a module prefix such as
`NetworkEpiCore.NoAlignment()` depending on what the page has loaded).
"""
function _is_no_alignment(a)
    T = typeof(a)
    return nameof(T) === :NoAlignment && nameof(parentmodule(T)) === :NetworkEpiCore
end

"""
    reference_note(sc, ref) -> Markdown.MD

The sentence that must accompany every comparison with a NetworkOutbreaks reference ensemble:
the scenario id, population size N, number of runs, how graphs were drawn, the conditioning
rule, and the fraction of runs it keeps (P(major), or P(survival) for `Survival()`; see
`kept_label`) with its 95% Wilson interval, all read from the committed summary `ref`
(`scenario_summary(sc)`) and the scenario `sc`. Throws if `ref` does not belong to `sc`.
"""
function reference_note(sc, ref)
    ref.id == sc.id || throw(ArgumentError(
        "reference_note: summary :$(ref.id) does not belong to scenario :$(sc.id)"))
    g = sc.sim.graphs
    graphs = g === :per_run ? "a fresh graph per run" :
             g === :fixed ? "one fixed graph for all runs" :
             g isa Tuple ? "graphs from a pool of $(g[2])" : string(g)
    align = _is_no_alignment(sc.sim.align) ? "" : "; time-aligned by $(condition_label(sc.sim.align))"
    lo, hi = ref.p_major_ci
    runs, prob = kept_label(sc.sim.condition)
    txt = @sprintf("NetworkOutbreaks reference `:%s`: N = %d, %d runs (%s), conditioned on %s%s; %d %s, %s = %.3f (95%% CI %.3f–%.3f).",
                   ref.id, ref.N, ref.nsims, graphs, condition_label(sc.sim.condition), align,
                   ref.n_major, runs, prob, ref.p_major, lo, hi)
    return Markdown.parse(txt)
end

"""
    mdtable(header, rows) -> Markdown.MD

A Markdown table with column names `header` and one row per element of `rows` (each an
iterable of cells). Reals are printed with four significant digits; everything else with
`string`. Use it for every table of numbers a page's prose relies on.
"""
function mdtable(header, rows)
    h = collect(string.(header))
    io = IOBuffer()
    println(io, "| ", join(h, " | "), " |")
    println(io, "|", join(fill("---", length(h)), "|"), "|")
    for r in rows
        cells = [_fmt(c) for c in r]
        length(cells) == length(h) || throw(ArgumentError(
            "mdtable: a row has $(length(cells)) cells for $(length(h)) columns"))
        println(io, "| ", join(cells, " | "), " |")
    end
    return Markdown.parse(String(take!(io)))
end

const _CITABLE_PATH = normpath(joinpath(@__DIR__, "..", "..", "..", "NetworkEpiCore.jl",
                                        "proofs", "CITABLE.txt"))

"""
    citable_names() -> Vector{String}

The Lean theorem names that vignettes may cite: the non-comment lines of
`NetworkEpiCore.jl/proofs/CITABLE.txt`.
"""
function citable_names()
    isfile(_CITABLE_PATH) || error("citable_names: $(_CITABLE_PATH) not found")
    return [strip(l) for l in eachline(_CITABLE_PATH) if !isempty(strip(l)) && !startswith(strip(l), "#")]
end

"""
    lean_cite(name) -> Markdown.MD

The inline citation `` `name` `` of a Lean theorem, after checking that `name` is listed in
CITABLE.txt. An unlisted name throws, so the page fails to render rather than cite it.
"""
function lean_cite(name::AbstractString)
    name in citable_names() || throw(ArgumentError(
        "lean_cite: $(name) is not listed in NetworkEpiCore.jl/proofs/CITABLE.txt; vignettes may cite only listed theorems"))
    return Markdown.parse("Lean: `$(name)`")
end
