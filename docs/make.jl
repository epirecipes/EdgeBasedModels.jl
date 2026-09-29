# Build the EdgeBasedModels documentation:
#
#     julia --project=docs docs/make.jl
#
# The docs environment must develop EdgeBasedModels and NetworkEpiCore by path (docs/Project.toml
# with [sources]). The rendered vignette pages (vignettes/E*/index.html, self-contained) are
# published at build/vignettes/<page>/index.html; set DOCS_SKIP_VIGNETTES=1 to leave them out
# (the links on the Vignettes page then warn), and DOCS_BUILD=<dir> to build somewhere other than
# docs/build.
using Documenter
using EdgeBasedModels

const DOCS = @__DIR__
const ROOT = dirname(DOCS)
const REMOTE = Documenter.Remotes.GitHub("epirecipes", "EdgeBasedModels.jl")

DocMeta.setdocmeta!(EdgeBasedModels, :DocTestSetup, :(using EdgeBasedModels); recursive = true)

# docs/src plus the package's MIGRATION.md, assembled in a temporary source directory so that the
# build never writes into docs/src.
const SRC = mktempdir()
const BUILD = get(ENV, "DOCS_BUILD", joinpath(DOCS, "build"))   # override to build elsewhere
cp(joinpath(DOCS, "src"), SRC; force = true)
cp(joinpath(ROOT, "MIGRATION.md"), joinpath(SRC, "migration.md"); force = true)

# The rendered vignette pages (self-contained html) go into the source tree as assets, which
# Documenter copies to build/vignettes/<page>/index.html, where docs/src/vignettes.md links.
if get(ENV, "DOCS_SKIP_VIGNETTES", "0") != "1"
    vdir = joinpath(ROOT, "vignettes")
    for page in sort(readdir(vdir))
        html = joinpath(vdir, page, "index.html")
        (startswith(page, "E") && isfile(html)) || continue
        mkpath(joinpath(SRC, "vignettes", page))
        cp(html, joinpath(SRC, "vignettes", page, "index.html"); force = true)
    end
end

makedocs(;
    source    = SRC,
    build     = BUILD,
    sitename  = "EdgeBasedModels.jl",
    modules   = [EdgeBasedModels],
    authors   = "Simon Frost",
    # The package directory need not be a git checkout: name its remote explicitly (source links
    # point at the main branch). Pages are built from a temporary copy, so they get no edit link.
    remotes   = Dict(ROOT => (REMOTE, "main")),
    format    = Documenter.HTML(;
        canonical      = "https://epirecip.es/EdgeBasedModels.jl/",
        edit_link      = nothing,
        repolink       = "https://github.com/epirecipes/EdgeBasedModels.jl",
        assets         = String[],
        prettyurls     = false,
        size_threshold = nothing,
        size_threshold_warn = nothing,
    ),
    pages     = [
        "Home"                    => "index.md",
        "Morphisms and validation" => "validation.md",
        "Vignettes"               => "vignettes.md",
        "Migrating from 0.1"      => "migration.md",
        "API"                     => "api.md",
    ],
    checkdocs = :exports,
    # MIGRATION.md links to repository files outside the manual.
    warnonly  = [:missing_docs, :cross_references],
)
