# EdgeBasedModels test harness.
#
# Every file `test/suites/*.jl` is a self-contained suite (it loads what it uses). The harness runs
# them in sorted order, each inside its own module and its own top-level testset, so one failing
# suite neither stops the others nor leaks names into them. Each suite file is owned by one work
# package (DESIGN_NetworkEpiCore.md, section G.1); the `00_legacy_<area>.jl` files are the
# pre-refactor tests split by area, and each of them also checks that area's goldens
# (`test/golden/<area>/`, see test/golden/GoldenTools.jl).
#
# Selecting suites: a selector matches a suite when its `_`-separated words occur, consecutively
# and whole, among the words of the suite's file name (a trailing `.jl` is ignored). So `sis`
# selects `00_legacy_sis.jl` but not `00_legacy_analysis.jl`, `legacy_core` selects
# `00_legacy_core.jl`, and `legacy` selects every legacy suite. A selector that matches no suite
# is an error.
#
#     julia --project=. -e 'using Pkg; Pkg.test(test_args = ["legacy_core", "eon"])'
#     EBM_TEST_SUITES=clustered,dynamic julia --project=. -e 'using Pkg; Pkg.test()'
#
# Regenerating goldens (writes only missing files unless `--overwrite` is given; `--metadata-only`
# rewrites only description/issues/notes). Here the arguments are golden AREAS or `area/case`
# names, taken from `test_args` only (EBM_TEST_SUITES is ignored):
#
#     julia --project=. -e 'using Pkg; Pkg.test(test_args = ["--regenerate-goldens", "--overwrite", "dynamic"])'

using Test

const SUITE_DIR = joinpath(@__DIR__, "suites")

_words(s::AbstractString) = split(s, '_'; keepempty = false)

"""
    suite_matches(selector, file) -> Bool

Whether `selector` selects the suite `file`: the `_`-separated words of `selector` (without a
trailing `.jl`) occur consecutively among the words of `file` (without `.jl`).
"""
function suite_matches(selector::AbstractString, file::AbstractString)
    want = _words(endswith(selector, ".jl") ? selector[1:(end - 3)] : selector)
    have = _words(splitext(file)[1])
    n = length(want)
    (n == 0 || n > length(have)) && return false
    return any(i -> have[i:(i + n - 1)] == want, 1:(length(have) - n + 1))
end

"""
    selected_suites(selectors) -> Vector{String}

File names in `test/suites` (sorted) selected by at least one of `selectors` (see
[`suite_matches`](@ref)); all files when `selectors` is empty. Throws if a selector selects
nothing, so that a typo cannot silently skip a suite.
"""
function selected_suites(selectors::AbstractVector{<:AbstractString})
    files = sort!(filter(f -> endswith(f, ".jl"), readdir(SUITE_DIR)))
    isempty(selectors) && return files
    unmatched = [s for s in selectors if !any(f -> suite_matches(s, f), files)]
    isempty(unmatched) ||
        error("no test suite in $SUITE_DIR matches $(join(unmatched, ", ")); suites: $(join(files, ", "))")
    return filter(f -> any(s -> suite_matches(s, f), selectors), files)
end

"""
    run_suite(file)

Include `test/suites/<file>` into a fresh module (with the usual `include` and `eval`).
"""
function run_suite(file::AbstractString)
    mod = Module(Symbol(replace(splitext(file)[1], r"[^A-Za-z0-9_]" => "_")))
    Core.eval(mod, :(include(path) = Base.include($mod, path)))
    Core.eval(mod, :(eval(ex) = Core.eval($mod, ex)))
    Base.include(mod, joinpath(SUITE_DIR, file))
    return nothing
end

const TEST_ARGS = String.(copy(ARGS))
const ENV_SUITES = String.(strip.(split(get(ENV, "EBM_TEST_SUITES", ""), ','; keepempty = false)))

if "--regenerate-goldens" in TEST_ARGS
    isempty(ENV_SUITES) ||
        @warn "EBM_TEST_SUITES selects test suites and is ignored when regenerating goldens; " *
              "pass golden areas in test_args instead" EBM_TEST_SUITES = ENV_SUITES
    include(joinpath(@__DIR__, "golden", "generate.jl"))
    GoldenGenerate.main(filter(!=("--regenerate-goldens"), TEST_ARGS))
else
    const SELECTORS = vcat(TEST_ARGS, ENV_SUITES)
    flags = filter(s -> startswith(s, "--"), SELECTORS)
    isempty(flags) || error("unknown test option(s) $(join(flags, ", ")); the only option is --regenerate-goldens")
    const SUITES = selected_suites(SELECTORS)
    @info "EdgeBasedModels test suites" SUITES
    @testset "EdgeBasedModels" verbose = true begin
        for file in SUITES
            @testset "$file" begin
                run_suite(file)
            end
        end
    end
end
