using Documenter
using EdgeBasedModels

DocMeta.setdocmeta!(EdgeBasedModels, :DocTestSetup, :(using EdgeBasedModels);
                    recursive = true)

makedocs(
    sitename = "EdgeBasedModels.jl",
    modules  = [EdgeBasedModels],
    authors  = "Simon Frost",
    repo     = "https://github.com/epirecipes/EdgeBasedModels.jl/blob/{commit}{path}#{line}",
    format   = Documenter.HTML(;
        canonical    = "https://epirecip.es/EdgeBasedModels.jl/",
        edit_link    = "main",
        assets       = String[],
        prettyurls   = false,
        size_threshold = nothing,
    ),
    pages = [
        "Home"      => "index.md",
        "Vignettes" => "vignettes.md",
        "API"       => "api.md",
    ],
    checkdocs = :none,
    warnonly  = true,
)
