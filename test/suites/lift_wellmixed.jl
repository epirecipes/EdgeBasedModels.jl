# WP17 acceptance 7: the WellMixed(κ) closure equals mass_action(cm; κ) through the well-mixed
# unit M1 (DESIGN §D.5): (θ; x) ↦ (S = q e^{κ(θ−1)}, x) is a conjugacy onto the mass-action ODE
# of c_κ P for exit-free models, and a quotient semiconjugacy with exits (ξ) or removals (the
# sink). It is checked with NetworkEpiCore's `verify` (symbolic residual 0) and by comparing
# trajectories with the mass-action ODE integrated by a hand-written RK4 in this file. With a
# FrequencyDependent model (β S I on fractions) the lift is the model's mass-action ODE for
# every κ (the unit law, design §B.6).

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using LinearAlgebra
using OrdinaryDiffEq: Vern9
using Test

const EBM = EdgeBasedModels
const TOL = (solver = Vern9(), reltol = 1e-12, abstol = 1e-14)

# A hand-written RK4 of the mass-action SEIR ODE with contact rate β (per unit time, on fractions).
function ma_seir(β, σ, γ, x0, T; h = 1e-3, every = 1000)
    f(x) = (-β * x[1] * x[3], β * x[1] * x[3] - σ * x[2], σ * x[2] - γ * x[3], γ * x[3])
    x = x0
    out = [x]
    for n in 1:round(Int, T / h)
        k1 = f(x); k2 = f(x .+ h / 2 .* k1); k3 = f(x .+ h / 2 .* k2); k4 = f(x .+ h .* k3)
        x = x .+ h / 6 .* (k1 .+ 2 .* k2 .+ 2 .* k3 .+ k4)
        n % every == 0 && push!(out, x)
    end
    return out
end

numval(e, at) = Float64(Symbolics.value(Symbolics.substitute(e, at; fold = Val(true))))

@testset "lift: WellMixed (the unit M1)" begin
    @testset "M1 verifies symbolically: SIR, SEIR, SEAIR, two strains, exits, removals" begin
        for (cm, κ) in ((sir_model(), 5.0), (seir_model(), 3.0), (seair_model(), 5.0), (twostrain_model(), 4.0),
                        (sirv_model(), 5.0),
                        (ContactModel(:rem; contacts = [Contact(:S, :I, :I, :τ)], transitions = [NodeTransition(:I, nothing, :γ)]), 2.0))
            sys = edge_based(cm, WellMixed(κ))
            @test sys.metadata[:closure] === :well_mixed
            m = EBM._well_mixed_unit(sys)
            exact = !haskey(sys.variables, :ξ) && isempty(sys.metadata[:sinks])
            @test m.kind === (exact ? :conjugacy : :semiconjugacy)
            r = verify(m)
            @test r.ok
            @test r.method === :symbolic && r.max_residual == 0
        end
        # a perturbed map (S without the seed factor q) fails
        sys = edge_based(sir_model(), WellMixed(5.0))
        m = EBM._well_mixed_unit(sys)
        coords = sys.metadata[:coords]
        bad = Semiconjugacy(:bad, m.source, m.target,
                            Pair{Any,Any}[m.target.states[1] => exp(5.0 * (coords[:θ] - 1)),
                                          m.target.states[2] => coords[:pop_I], m.target.states[3] => coords[:pop_R]],
                            Pair{Any,Any}[], :conjugacy, :exact, Evidence[])
        @test !verify(bad).ok
    end

    @testset "the unit law: a frequency-dependent SEIR is its mass-action ODE for every κ" begin
        cm = ContactModel(:seir_fd; contacts = [Contact(:S, :I, :E, :β)],
                          transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)],
                          convention = FrequencyDependent())
        p = Dict(:β => 0.6, :σ => 0.3, :γ => 0.2)
        ref = ma_seir(0.6, 0.3, 0.2, (0.99, 0.0, 0.01, 0.0), 60.0)
        for κ in (1.0, 5.0, 40.0)
            sys = edge_based(cm, WellMixed(κ))
            sol = solve_epidemic(sys; p, initial = SeedFraction(:I => 0.01), tspan = (0.0, 60.0), saveat = 1.0, TOL...)
            for (k, X) in enumerate((:S, :pop_E, :pop_I, :pop_R))
                @test maximum(abs.(compartment(sys, sol, X) .- getindex.(ref, k))) < 1e-9
            end
            @test compartment(sys, sol, :cumulative) ≈ 1 .- compartment(sys, sol, :S) atol = 1e-12
        end
    end

    @testset ":sir_wm5: NetworkEpiCore's final size and growth rate (the hub for every road back to MA)" begin
        sc = scenario(:sir_wm5)
        sys = edge_based(sc)
        sol = solve_epidemic(sys; p = sc.params, initial = sc.initial, tspan = (0.0, 800.0), TOL...)
        @test compartment(sys, sol, :cumulative)[end] ≈ sc.expected[:final_size] atol = 1e-8   # MA(1/2, 1/4): 0.8002
        S = compartment(sys, sol, :S)
        @test maximum(abs.(S .+ compartment(sys, sol, :pop_I) .+ compartment(sys, sol, :pop_R) .- 1)) < 1e-12
        # linearisation at the disease-free state (θ = 1, q = 1, x = 0): r = κτ − γ
        raw = symbolic_ode(sys)
        J = Symbolics.jacobian(Num.(raw.rhs), Num.(raw.states))
        at = Dict{Any,Any}(x => (Symbol(Symbolics.getname(x)) === :θ ? 1.0 : 0.0) for x in raw.states)
        for q in raw.parameters
            n = Symbol(Symbolics.getname(q))
            at[q] = n === :q_S ? 1.0 : sc.params[n]
        end
        M = [numval(J[i, j], at) for i in axes(J, 1), j in axes(J, 2)]
        @test maximum(real.(eigvals(M))) ≈ sc.expected[:r] rtol = 1e-10
    end

    @testset "exits on WellMixed: ξ, conservation, the accumulator" begin
        sys = edge_based(sirv_model(τ = 0.1, γ = 0.25, ν = 0.02), WellMixed(5.0))
        @test haskey(sys.variables, :ξ) && !haskey(sys.variables, :φ_I)
        sol = solve_epidemic(sys; initial = SeedFraction(:I => 0.01), tspan = (0.0, 100.0), saveat = 1.0, TOL...)
        S = compartment(sys, sol, :S)
        V = compartment(sys, sol, :pop_V)
        @test maximum(abs.(S .+ compartment(sys, sol, :pop_I) .+ compartment(sys, sol, :pop_R) .+ V .- 1)) < 1e-12
        @test compartment(sys, sol, :cumulative)[end] ≈ 1 - S[end] - V[end] atol = 1e-12
        @test_throws ArgumentError edge_based(sir_model(), WellMixed(5.0); form = :compact)
    end
end
