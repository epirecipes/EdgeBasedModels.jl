# WP17: seeding and generated names of assembled systems (DESIGN §A.3, §E.2, §J.6).
#
# - The seed fraction of every node species X is the parameter `seed_X` (ebm-core #14 / verified
#   issue E26): a rate or network parameter named ρ is an ordinary parameter. The legacy builders
#   called their seed parameter ρ and silently merged it with a user's ρ (E26), which WP14 turned
#   into an error; with the assembler the model simply works, and the seed is not touched by p.
# - A name the assembler generates (θ, ξ, the φ_/pop_ coordinates, cumulative, q_<s>, the
#   observables) cannot be a parameter name.
# - default_initial_conditions(sys; initial): any node species may be seeded (θ(0) = ξ(0) = 1,
#   φ_X(0) = pop_X(0) = ρ_X, q = 1 − Σρ); the default is the unique entry state (§E.2).

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using OrdinaryDiffEq: Vern9
using Test

import Catalyst

const TOL = (solver = Vern9(), reltol = 1e-12, abstol = 1e-14)

@testset "lift: seeds and generated names" begin
    net = ConfigurationNetwork(PoissonDegree(5.0))

    @testset "seed_<X> parameters (E26): a parameter named ρ is an ordinary parameter" begin
        sys = edge_based(seir_model(), net)
        seeds = sys.metadata[:seed_params]
        @test Set(keys(seeds)) == Set([:E, :I, :R])
        @test Set(Symbol(Symbolics.getname(v)) for v in values(seeds)) == Set([:seed_E, :seed_I, :seed_R])
        @test Set(Symbol.(ModelingToolkit.parameters(sys.system))) == Set([:τ, :σ, :γ, :seed_E, :seed_I, :seed_R])
        # the seed is set with `initial`, not with p
        @test_throws ArgumentError solve_epidemic(sys; p = Dict(:τ => 0.3, :σ => 0.2, :γ => 0.1, :seed_E => 0.5),
                                                  tspan = (0.0, 10.0))
        # rates named ρ (per contact) and a network parameter named ρ: before, E26 (merged with the
        # seed) and then an ArgumentError (WP14's guard); now ordinary parameters
        ref = build_sir(PoissonDegree(5.0), 0.3, 0.1)
        sref = solve_epidemic(ref; tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        @test compartment(ref, sref, :R)[end] ≈ 0.8805791478 atol = 1e-8        # the E10 report's R(30)
        sysρ = build_sir(PoissonDegree(5.0), :ρ, :γ)
        @test :ρ in Symbol.(ModelingToolkit.parameters(sysρ.system))
        for ρv in (0.3, 0.9)                        # the rate changes, the seed (1e-3) does not
            sol = solve_epidemic(sysρ; p = Dict(:ρ => ρv, :γ => 0.1), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
            @test compartment(sysρ, sol, :S)[1] ≈ 1 - 1e-3 atol = 1e-15
            ρv == 0.3 && @test compartment(sysρ, sol, :R) ≈ compartment(ref, sref, :R) rtol = 1e-10
        end
        @parameters ρ
        symρ = build_sir(poisson_pgf(5.0), 0.3, ρ)
        sol = solve_epidemic(symρ; p = Dict(ρ => 0.1), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        @test compartment(symρ, sol, :R) ≈ compartment(ref, sref, :R) rtol = 1e-10
        pgfρ = build_sir(poisson_pgf(ρ), 0.3, 0.1)                                 # a PGF parameter ρ
        sol = solve_epidemic(pgfρ; p = Dict(:ρ => 5.0), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        @test compartment(pgfρ, sol, :R) ≈ compartment(ref, sref, :R) rtol = 1e-10
        rnρ = Catalyst.@reaction_network begin
            β, S + I --> 2I
            ρ, I --> R
        end
        sysc = edge_based(rnρ, net)
        sol = solve_epidemic(sysc; p = Dict(:β => 0.3, :ρ => 0.1), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        @test compartment(sysc, sol, :R) ≈ compartment(ref, sref, :R) rtol = 1e-10
    end

    @testset "generated names cannot be parameter names" begin
        for bad in (:θ, :ξ, :cumulative, :q_S, :φ_I, :pop_R, :edge_hazard, :infectious)
            @test_throws ArgumentError edge_based(sir_model(τ = bad, γ = :γ), net)
        end
        @test_throws ArgumentError edge_based(sir_model(τ = :τ, γ = :θ), WellMixed(5.0))
        @parameters q_S
        @test_throws ArgumentError edge_based(sir_model(τ = 0.3, γ = 0.1), ConfigurationNetwork(PoissonDegree(q_S)))
        st = strata([:a, :b])
        mnet = sbm_network(st; mean_contacts = [3.0 1.0; 1.0 3.0])
        @test_throws ArgumentError edge_based(stratify(sir_model(τ = :θ_a_b, γ = :γ), st), mnet)
        @test_throws ArgumentError edge_based(stratify(sir_model(τ = :τ, γ = :q_S_a), st), mnet)
        # names with underscores are fine unless the generated names really collide
        sts = strata([:child, :adult])
        ok = edge_based(stratify(sir_model(τ = 0.1, γ = 0.2), sts), sbm_network(sts; mean_contacts = [3.0 1.0; 1.0 3.0]))
        @test haskey(ok.variables, :θ_child_adult) && haskey(ok.variables, :φ_I_adult_child)
        # a seed parameter name is reserved by the ContactModel constructor itself
        @test_throws ArgumentError sir_model(τ = :seed_I, γ = :γ)
        # a node species named S next to the susceptible U (E26 C: the legacy builders named the
        # susceptible edge variable φ_S, which that stage shadowed, and WP14 refused the model):
        # here φ_S and pop_S are the node species S, and U's observables are U and φ_U
        cmU = ContactModel(:u; contacts = [Contact(:U, :S, :S, 0.5)], transitions = [NodeTransition(:S, :R, 0.25)])
        sysU = edge_based(cmU, net)
        @test haskey(sysU.variables, :φ_S) && haskey(sysU.variables, :pop_S)
        @test haskey(sysU.observables, :U) && haskey(sysU.observables, :φ_U) && !haskey(sysU.observables, :S)
        ref = edge_based(sir_model(τ = 0.5, γ = 0.25), net)
        solU = solve_epidemic(sysU; initial = SeedFraction(:S => 0.01), tspan = (0.0, 40.0), saveat = 1.0, TOL...)
        solr = solve_epidemic(ref; initial = SeedFraction(:I => 0.01), tspan = (0.0, 40.0), saveat = 1.0, TOL...)
        @test compartment(sysU, solU, :U) ≈ compartment(ref, solr, :S) rtol = 1e-12
        @test compartment(sysU, solU, :pop_S) ≈ compartment(ref, solr, :pop_I) rtol = 1e-12
        @test compartment(sysU, solU, :φ_U) ≈ compartment(ref, solr, :φ_S) rtol = 1e-12
        # the same model in the compact form: the aliases :S and :φ_S are not U's either (they
        # were, silently, before: compartment(c, sol, :S) returned U's curve), and the infector's
        # population is pop_S = 1 − U − R, as in the expanded form
        cU = edge_based(cmU, net; form = :compact)
        @test !haskey(cU.observables, :S) && !haskey(cU.observables, :φ_S) && !haskey(cU.variables, :S)
        @test haskey(cU.observables, :U) && haskey(cU.observables, :φ_U) && haskey(cU.variables, :pop_S)
        refc = edge_based(sir_model(τ = 0.5, γ = 0.25), net; form = :compact)
        solcU = solve_epidemic(cU; initial = SeedFraction(:S => 0.01), tspan = (0.0, 40.0), saveat = 1.0, TOL...)
        solrc = solve_epidemic(refc; initial = SeedFraction(:I => 0.01), tspan = (0.0, 40.0), saveat = 1.0, TOL...)
        @test compartment(cU, solcU, :U) ≈ compartment(refc, solrc, :S) rtol = 1e-12
        @test compartment(cU, solcU, :pop_S) ≈ compartment(refc, solrc, :pop_I) rtol = 1e-12
        @test compartment(cU, solcU, :φ_U) ≈ compartment(refc, solrc, :φ_S) rtol = 1e-12
        @test maximum(abs.(compartment(cU, solcU, :pop_S) .- compartment(sysU, solU, :pop_S))) < 1e-10
        @test model_curves(cU, solcU)[:S] ≈ compartment(sysU, solU, :pop_S) atol = 1e-10      # the infector S
    end

    @testset "the variable :R never names another species (E26)" begin
        # I → R → D: the recovered class (left by no transition) is D, but :R is the species R.
        # Before, :R was pop_D, so compartment(sys, sol, :R) silently returned D.
        cm = ContactModel(:rd; contacts = [Contact(:S, :I, :I, 0.3)],
                          transitions = [NodeTransition(:I, :R, 0.2), NodeTransition(:R, :D, 0.05)])
        sys = edge_based(cm, net)
        @test isequal(sys.variables[:R], sys.variables[:pop_R])
        sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 30.0), saveat = 1.0, TOL...)
        @test compartment(sys, sol, :R) == compartment(sys, sol, :pop_R)
        @test compartment(sys, sol, :R) != compartment(sys, sol, :pop_D)
        @test model_curves(sys, sol)[:R] ≈ compartment(sys, sol, :R) atol = 1e-12
        # without a species R, :R is the unique recovered class (I → D here) ...
        cmD = ContactModel(:d; contacts = [Contact(:S, :I, :I, 0.3)], transitions = [NodeTransition(:I, :D, 0.2)])
        for form in (:expanded, :compact)
            @test isequal(edge_based(cmD, net; form).variables[:R], edge_based(cmD, net; form).variables[:pop_D])
        end
        # ... and an infector called R owns the name in both forms (S + R → 2R, R → D)
        cmR = ContactModel(:rr; contacts = [Contact(:S, :R, :R, 0.5)], transitions = [NodeTransition(:R, :D, 0.25)])
        ref = edge_based(sir_model(τ = 0.5, γ = 0.25), net)
        solr = solve_epidemic(ref; initial = SeedFraction(:I => 0.01), tspan = (0.0, 40.0), saveat = 1.0, TOL...)
        for form in (:expanded, :compact)
            sysR = edge_based(cmR, net; form)
            @test isequal(sysR.variables[:R], sysR.variables[:pop_R])
            solR = solve_epidemic(sysR; initial = SeedFraction(:R => 0.01), tspan = (0.0, 40.0), saveat = 1.0, TOL...)
            @test maximum(abs.(compartment(sysR, solR, :R) .- compartment(ref, solr, :pop_I))) < 1e-10
            @test maximum(abs.(compartment(sysR, solR, :pop_D) .- compartment(ref, solr, :pop_R))) < 1e-10
        end
        # a susceptible called R: its node-S is the observable :R, and no variable shadows it
        cmS = ContactModel(:sr; contacts = [Contact(:R, :I, :I, 0.5)], transitions = [NodeTransition(:I, :D, 0.25)])
        for form in (:expanded, :compact)
            sysS = edge_based(cmS, net; form)
            @test !haskey(sysS.variables, :R) && haskey(sysS.observables, :R)
        end
        # a susceptible called I: the species name wins over the legacy :I, in both forms
        cmI = ContactModel(:ii; contacts = [Contact(:I, :X, :X, 0.5)], transitions = [NodeTransition(:X, :R, 0.25)])
        for form in (:expanded, :compact)
            sysI = edge_based(cmI, net; form)
            solI = solve_epidemic(sysI; initial = SeedFraction(:X => 0.01), tspan = (0.0, 40.0), saveat = 1.0, TOL...)
            @test maximum(abs.(compartment(sysI, solI, :I) .- compartment(ref, solr, :S))) < 1e-10
            @test maximum(abs.(compartment(sysI, solI, :infectious) .- compartment(ref, solr, :pop_I))) < 1e-10
        end
    end

    @testset "default_initial_conditions: the entry state by default; any node species" begin
        sys = edge_based(sir_model(τ = 0.3, γ = 0.1), net)
        @test default_initial_conditions(sys) == default_initial_conditions(sys; seed_fraction = 1e-3)
        @test default_initial_conditions(sys; initial = SeedFraction(:I => 0.01)) ==
              default_initial_conditions(sys; seed_fraction = 0.01)
        @test default_initial_conditions(sys; initial = SeedFraction(:I => 0.01; default = :S)) ==
              default_initial_conditions(sys; seed_fraction = 0.01)
        @test default_initial_conditions(sys; initial = SeedFraction(:S => 0.99, :I => 0.01)) ==
              default_initial_conditions(sys; seed_fraction = 0.01)
        @test default_initial_conditions(sys; initial = SeedCount(:I => 10), N = 1000) ==
              default_initial_conditions(sys; seed_fraction = 0.01)
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedCount(:I => 10))           # needs N
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedFraction(:I => 0.01), seed_fraction = 0.01)
        @test_throws ArgumentError default_initial_conditions(sys; initial = 0.01)
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedFraction(:X => 0.01))      # not a species
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedFraction(:I => 0.7, :R => 0.5))
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedFraction(:S => 0.5, :I => 0.01))
        # pre-immune nodes: R seeded as well as I (q = 1 − ρ_I − ρ_R)
        init = SeedFraction(:I => 0.01, :R => 0.2)
        sol = solve_epidemic(sys; initial = init, tspan = (0.0, 600.0), TOL...)
        @test compartment(sys, sol, :S)[1] ≈ 0.79 atol = 1e-15
        @test compartment(sys, sol, :φ_R)[1] ≈ 0.2 && compartment(sys, sol, :pop_R)[1] ≈ 0.2
        @test compartment(sys, sol, :cumulative)[1] ≈ 0.01 atol = 1e-15             # R is not infected (J.8)
        S = compartment(sys, sol, :S)
        @test maximum(abs.(S .+ compartment(sys, sol, :pop_I) .+ compartment(sys, sol, :pop_R) .- 1)) < 1e-12
        @test compartment(sys, sol, :cumulative)[end] ≈ 1 - S[end] - 0.2 atol = 1e-10
        # several entry states: an explicit initial is required
        two = edge_based(twostrain_model(τ1 = 0.2, τ2 = 0.3, γ = 0.25), net)
        @test_throws ArgumentError default_initial_conditions(two)
        @test !haskey(two.metadata, :entry)
        ic = default_initial_conditions(two; initial = SeedFraction(:I1 => 0.005, :I2 => 0.005))
        @test ic[two.metadata[:seed_params][:I1]] == 0.005 && ic[two.variables[:cumulative]] ≈ 0.01
    end
end
