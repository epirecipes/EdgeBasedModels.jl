# Regenerate the EdgeBasedModels golden files (test/golden/<area>/<case>.{toml,csv}).
#
# Goldens freeze EdgeBasedModels 0.1 behaviour, bugs included (DESIGN_NetworkEpiCore.md, WP1). A golden
# is replaced only by the work package that owns its area, in a bug-fix change accompanied by a
# literature or simulation test; so by default this script only writes goldens that are MISSING and
# refuses to touch existing files. Pass `--overwrite` to replace the goldens of the areas (or
# `area/case` names) you list.
#
# `--metadata-only` rewrites only the description, issues and notes of EXISTING goldens from cases.jl
# (for example to record a newly verified issue id). It does not run any case, so every number, the
# CSV and the provenance stay exactly as they are. It cannot be combined with `--overwrite`.
#
# Usage, preferred (runs in the exact test environment of the package):
#
#     cd EdgeBasedModels.jl
#     julia --project=. -e 'using Pkg; Pkg.test(test_args = ["--regenerate-goldens"])'
#     julia --project=. -e 'using Pkg; Pkg.test(test_args = ["--regenerate-goldens", "--overwrite", "dynamic"])'
#     julia --project=. -e 'using Pkg; Pkg.test(test_args = ["--regenerate-goldens", "--overwrite", "core/sir_bim_compact"])'
#     julia --project=. -e 'using Pkg; Pkg.test(test_args = ["--regenerate-goldens", "--metadata-only", "analysis"])'
#
# or directly, from any environment that provides the test dependencies of EdgeBasedModels:
#
#     julia --project=<env> test/golden/generate.jl [--overwrite | --metadata-only] [area | area/case ...]
#
# With no area arguments every area with a `cases.jl` is processed. The EoN references in
# `test/golden/eon/` are external data written by `eon/generate_eon.py`, not by this script.

isdefined(Main, :GoldenTools) || Base.include(Main, joinpath(@__DIR__, "GoldenTools.jl"))

module GoldenGenerate

using Main.GoldenTools

const FLAGS = ("--overwrite", "--metadata-only")

"""
    main(args) -> Vector{Pair{String,Symbol}}

Generate goldens for the areas or `area/case` names in `args` (all areas when none are given).
`--overwrite` replaces existing files; without it existing goldens are left untouched.
`--metadata-only` rewrites only the metadata of existing goldens (see
`GoldenTools.update_golden_metadata`) and runs no case. Returns `"area/case" => status` pairs with
status `:written`, `:overwritten`, `:skipped_existing`, `:metadata_updated` or
`:metadata_unchanged`.
"""
function main(args::AbstractVector{<:AbstractString})
    unknown_flags = [a for a in args if startswith(a, "--") && !(a in FLAGS)]
    isempty(unknown_flags) || error("unknown option(s) $(join(unknown_flags, ", ")); known: $(join(FLAGS, ", "))")
    overwrite = "--overwrite" in args
    metadata_only = "--metadata-only" in args
    (overwrite && metadata_only) && error("--overwrite and --metadata-only cannot be combined")
    selectors = [a for a in args if !startswith(a, "--")]
    areas = golden_areas()
    wanted_areas = isempty(selectors) ? areas : unique([first(split(s, '/')) for s in selectors])
    for a in wanted_areas
        a in areas || error("unknown golden area $a; known areas: $(join(areas, ", "))")
    end
    report = Pair{String, Symbol}[]
    for area in wanted_areas
        cases = load_cases(area)
        case_selectors = [s for s in selectors if occursin('/', s) && first(split(s, '/')) == area]
        if !isempty(case_selectors)
            names = Set(last(split(s, '/')) for s in case_selectors)
            unknown = setdiff(names, Set(c.name for c in cases))
            isempty(unknown) || error("unknown golden cases in $area: $(join(sort!(collect(unknown)), ", "))")
            filter!(c -> c.name in names, cases)
        end
        for case in cases
            key = "$(case.area)/$(case.name)"
            toml_path, _ = golden_paths(case)
            exists = isfile(toml_path)
            if metadata_only
                exists || error("golden $key does not exist; generate it without --metadata-only first")
                status = update_golden_metadata(case) ? :metadata_updated : :metadata_unchanged
                @info "golden $(status)" key
                push!(report, key => status)
                continue
            end
            if exists && !overwrite
                @info "golden exists, left untouched (pass --overwrite to replace it)" key
                push!(report, key => :skipped_existing)
                continue
            end
            t0 = time()
            result = run_case(case)
            write_golden(case, result)
            status = exists ? :overwritten : :written
            @info "golden $(status)" key seconds = round(time() - t0; digits = 1)
            push!(report, key => status)
        end
    end
    return report
end

end # module GoldenGenerate

if abspath(PROGRAM_FILE) == @__FILE__
    GoldenGenerate.main(ARGS)
end
