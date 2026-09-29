# WP18: the reverse maps of an edge-based system and their morphisms (DESIGN §D.5 M1–M6, Λ1,
# calibrations; §G.2 WP18; verified issue E08).
#
# `mass_action(sys; form)` returns the target reaction network, its ODE and the semiconjugacy π
# from the uncompiled edge-based field; `verify` (NetworkEpiCore) checks Dπ·F = G∘π. Acceptance:
#
# - `verify` of M1, M2, M3, M4 and M6 gives residual 0 (or < 1e-10): SIR, SEIR and SEAIR on
#   Poisson for M2/M3; :sir_nb4 for M4; :sir_bim and :sir_vax_pois5 for M6;
# - perturbed maps fail;
# - Rempała's S(t) matches along the Poisson(5) trajectories to 1e-9;
# - the Λ1 ladder error ratio is ≈ μ₂/μ₁;
# - the error texts of to_mass_action and compare_models.
#
# E08 (VERIFIED_ISSUES.md; skeptic's corrected fix): the old to_mass_action map MA(τψ''(1)/ψ'(1), γ)
# with the MA "I" read as φ_I (or as the prevalence) is not a semiconjugacy — `verify` fails with the
# residual −τφ_I in dI/dt — and its trajectories are far from the network's (max|ΔS| = 0.2777 on
# the vignette parameters), while Rempała's MA(μτ, γ + τ) is exact for S(t), with I = φ_I, and the
# node copies of D_μ give the prevalence.
#
# Independent references in this file: mass-action and pairwise fields transcribed by hand from
# Rempała 2023 (papers/2310.13866v1.md:69) and from the S-anchored pairwise equations with the
# closure K_ψ = ψψ''/ψ'² (Kiss, Kenah & Rempała 2023), plain-Julia ODEs, NetworkEpiCore's R₀ /
# growth-rate / final-size engine, and exact stochastic simulation (NetworkOutbreaks).

using EdgeBasedModels
using NetworkEpiCore
using Symbolics
using Statistics
using OrdinaryDiffEq: ODEProblem, solve, Vern9
using Test

import Graphs
import NetworkOutbreaks as NO

const EBM = EdgeBasedModels
const TOL = (solver = Vern9(), reltol = 1e-12, abstol = 1e-14)
const POIS5 = ConfigurationNetwork(PoissonDegree(5.0))
const BIM = ConfigurationNetwork(EmpiricalDegree(2 => 5 / 6, 10 => 1 / 6))
const NB4 = ConfigurationNetwork(NegBinDegree(mean = 4, var = 8))

name(x) = Symbol(Symbolics.getname(Symbolics.unwrap(x)))

err(f) = try
    f()
    "no error"
catch e
    sprint(showerror, e)
end

# Integrate a SymbolicODE (autonomous) with parameter values `p` (by name) from `u0` (by state
# name) and return the states on `tgrid` by name.
function integrate(ode::SymbolicODE, p::AbstractDict, u0::AbstractDict, tgrid)
    names = state_names(ode)
    xs = [Symbolics.variable(Symbol(:u_, i)) for i in eachindex(names)]
    sub = Dict{Any,Any}(Symbolics.unwrap(x) => Symbolics.unwrap(y) for (x, y) in zip(ode.states, xs))
    for q in ode.parameters
        sub[Symbolics.unwrap(q)] = Float64(p[name(q)])
    end
    rhs = [Symbolics.substitute(Symbolics.wrap(f), sub; fold = Val(true)) for f in ode.rhs]
    f = Symbolics.build_function(rhs, xs; expression = Val(false))[1]
    prob = ODEProblem((u, _, _) -> collect(f(u)), Float64[u0[n] for n in names], (first(tgrid), last(tgrid)))
    sol = solve(prob, Vern9(); reltol = 1e-12, abstol = 1e-14, saveat = tgrid)
    return Dict(n => sol[i, :] for (i, n) in enumerate(names))
end

# Solve an edge-based system on the time grid.
function eb_solve(sys, p, initial, tgrid)
    return solve_epidemic(sys; p, initial, tspan = (first(tgrid), last(tgrid)), saveat = tgrid, TOL...)
end

# The target's initial state: π of the edge-based initial state (by name).
target_initial(img_or_m, sys, sol) = Dict(k => v[1] for (k, v) in pushforward(img_or_m, sys, sol, [0.0]))

# A plain Float64 RK4 of u̇ = f(u) (for the hand-written mass-action SIR models).
function rk4(f, u0, h, n)
    u = collect(Float64, u0)
    out = [copy(u)]
    for _ in 1:n
        k1 = f(u); k2 = f(u .+ (h / 2) .* k1); k3 = f(u .+ (h / 2) .* k2); k4 = f(u .+ h .* k3)
        u = u .+ (h / 6) .* (k1 .+ 2 .* k2 .+ 2 .* k3 .+ k4)
        push!(out, copy(u))
    end
    return out
end

@testset "reverse maps: back to mass action and to pairwise (M1–M6, Λ1, calibrations)" begin

    @testset "M1: the well-mixed unit (form = :exact on WellMixed)" begin
        rem = ContactModel(:rem; contacts = [Contact(:S, :I, :I, :τ)], transitions = [NodeTransition(:I, nothing, :γ)])
        for (cm, κ) in ((sir_model(), 5.0), (seir_model(), 3.0), (seair_model(), 5.0), (twostrain_model(), 4.0),
                        (sirv_model(), 5.0), (rem, 2.0))
            sys = edge_based(cm, WellMixed(κ))
            img = mass_action(sys; form = :exact)
            @test img isa MassActionImage
            @test img.form === :exact && img.kind === :mass_action && img.exactness === :exact
            @test img.ode === img.morphism.target
            @test img.morphism.source === symbolic_ode(sys)
            r = verify(img.morphism)
            @test r.ok && r.method === :symbolic && r.max_residual == 0
            exact = !haskey(sys.variables, :ξ) && isempty(sys.metadata[:sinks])
            @test img.morphism.kind === (exact ? :conjugacy : :semiconjugacy)
            # the target is MA(c_κ P) (NetworkEpiCore's mass_action(cm; κ), also WP17's M1 target)
            @test vector_fields_equal(img.ode, mass_action(cm; κ))
            @test vector_fields_equal(img.ode, EBM._well_mixed_unit(sys).target)
            @test vector_fields_equal(img.ode, mass_action(img.model))
            @test vector_fields_equal(img.ode, mass_action(img.reaction_data))
        end
        # the unit law: a frequency-dependent SEIR is its own mass-action ODE on WellMixed(κ) for every κ
        fd = ContactModel(:seir_fd; contacts = [Contact(:S, :I, :E, :β)],
                          transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)],
                          convention = FrequencyDependent())
        for κ in (1.0, 5.0)
            img = mass_action(edge_based(fd, WellMixed(κ)); form = :exact)
            @test verify(img.morphism).ok
            @test vector_fields_equal(img.ode, mass_action(fd))
        end
        # a perturbed map (S without the seed factor q) fails
        sys = edge_based(sir_model(), WellMixed(5.0))
        m = mass_action(sys; form = :exact).morphism
        c = sys.metadata[:coords]
        bad = Semiconjugacy(:bad, m.source, m.target,
                            [m.target.states[1] => exp(5.0 * (c[:θ] - 1)), m.target.states[2] => c[:pop_I],
                             m.target.states[3] => c[:pop_R]])
        @test !verify(bad).ok
    end

    @testset "M2: the Poisson isomorphism (form = :exact on Poisson(μ))" begin
        for id in (:sir_pois5, :seir_pois5, :seair_pois5, :twostrain_pois5, :sir_vax_pois5)
            sc = scenario(id)
            sys = edge_based(sc)
            img = mass_action(sys; form = :exact)
            @test img.morphism.name === :poisson_iso && img.kind === :mass_action && img.model === nothing
            r = verify(img.morphism)
            @test r.ok && r.max_residual <= 1e-10
            @test r.method === :symbolic
            s = only(susceptible_species(sc.model))
            others = [x for x in species_names(sc.model) if x !== s]
            @test state_names(img.ode) == vcat(s, Symbol.(:Φ_, others), others)
            @test img.morphism.kind === (id === :sir_vax_pois5 ? :semiconjugacy : :conjugacy)   # ξ forgotten
        end
        # the SIR target is the hand-written D_μ: S' = −μτSΦ_I, Φ_I' = μτSΦ_I − (τ + γ)Φ_I, Φ_R' = γΦ_I,
        # I' = μτSΦ_I − γI, R' = γI
        sys = edge_based(sir_model(), POIS5)
        img = mass_action(sys; form = :exact)
        τ, γ = as_parameter.((:τ, :γ))
        @variables S Φ_I Φ_R I R
        hand = SymbolicODE(:hand_D5; states = [S, Φ_I, Φ_R, I, R],
                           rhs = [-5τ * S * Φ_I, 5τ * S * Φ_I - (τ + γ) * Φ_I, γ * Φ_I, 5τ * S * Φ_I - γ * I, γ * I])
        @test vector_fields_equal(img.ode, hand)
        # perturbed maps: the node and edge copies swapped; the seed factor q dropped
        m = img.morphism
        c = sys.metadata[:coords]
        q = sys.metadata[:q][:S].param
        swap = Dict(:S => q * exp(5.0 * (c[:θ] - 1)), :Φ_I => c[:pop_I], :Φ_R => c[:pop_R], :I => c[:φ_I], :R => c[:φ_R])
        @test !verify(Semiconjugacy(:swap, m.source, m.target, [x => swap[n] for (x, n) in zip(m.target.states, state_names(m.target))])).ok
        noq = merge(swap, Dict(:S => exp(5.0 * (c[:θ] - 1)), :Φ_I => c[:φ_I], :Φ_R => c[:φ_R], :I => c[:pop_I], :R => c[:pop_R]))
        @test !verify(Semiconjugacy(:noq, m.source, m.target, [x => noq[n] for (x, n) in zip(m.target.states, state_names(m.target))])).ok
        # along trajectories: the node copies are the prevalences (SEIR seeded in E, SEAIR)
        for id in (:seir_pois5, :seair_pois5)
            sc = scenario(id)
            sys = edge_based(sc)
            tg = collect(0.0:1.0:150.0)
            sol = eb_solve(sys, sc.params, sc.initial, tg)
            img = mass_action(sys; form = :exact)
            ma = integrate(img.ode, merge(sc.params, Dict(:q_S => 0.99)), target_initial(img, sys, sol), tg)
            @test maximum(abs.(ma[:S] .- compartment(sys, sol, :S))) < 1e-9
            for X in species_names(sc.model)
                X === :S && continue
                @test maximum(abs.(ma[X] .- compartment(sys, sol, Symbol(:pop_, X)))) < 1e-9
                @test maximum(abs.(ma[Symbol(:Φ_, X)] .- compartment(sys, sol, Symbol(:φ_, X)))) < 1e-9
            end
        end
    end

    @testset "M3: Rempała's quotient (form = :edge); the old to_mass_action map fails verify (E08)" begin
        for cm in (sir_model(), seir_model(), seair_model(), twostrain_model(), sirv_model())
            sys = edge_based(cm, POIS5)
            img = mass_action(sys; form = :edge)
            @test img.morphism.name === :rempala && img.morphism.kind === :semiconjugacy
            @test img.form === :edge && img.exactness === :exact
            r = verify(img.morphism)
            @test r.ok && r.method === :symbolic && r.max_residual == 0
            @test state_names(img.ode) == species_names(cm)                  # the model's own species
            @test vector_fields_equal(img.ode, mass_action(rempala_reduction(cm, 5.0)))
            @test vector_fields_equal(img.ode, mass_action(img.reaction_data))
            # the Lean theorem is cited for SIR only (NEP.rempala is the SIR instance)
            @test (Evidence(:lean, "NEP.rempala") in img.morphism.evidence) == (cm.name === :sir)
            @test any(n -> occursin("EDGE variable φ_X", n), img.notes)
        end
        # for every mean degree μ (a symbolic mean; the Lean theorem NEP.rempala is stated for all μ),
        # M2, M3 and M5 hold symbolically
        μ = as_parameter(:μ)
        sysμ = edge_based(seir_model(), ConfigurationNetwork(PoissonDegree(μ)))
        for form in (:exact, :edge, :general)
            r = verify(mass_action(sysμ; form).morphism)
            @test r.ok && r.method === :symbolic
        end
        # SIR: exactly Rempała's MA(β = μτ, γ_MA = γ + τ) (Thm 1), on (S, I = φ_I, R = φ_R)
        sys = edge_based(sir_model(), POIS5)
        img = mass_action(sys; form = :edge)
        τ, γ = as_parameter.((:τ, :γ))
        @variables S I R
        rempala = SymbolicODE(:rempala_thm1; states = [S, I, R],
                              rhs = [-5τ * S * I, 5τ * S * I - (γ + τ) * I, γ * I])
        @test vector_fields_equal(img.ode, rempala)
        c = sys.metadata[:coords]
        q = sys.metadata[:q][:S].param
        @test isequal(Dict(n => v for (n, v) in zip(state_names(img.ode), last.(img.morphism.map)))[:I], c[:φ_I])
        # E08: the old map MA(τψ''(1)/ψ'(1), γ) = MA(5τ, γ), with the MA "I" read as φ_I
        # (compare_models) — not a semiconjugacy; the residual of dI/dt is exactly −τφ_I
        κ_old = excess_degree(PoissonDegree(5.0))                       # ψ''(1)/ψ'(1) = 5
        old_target = mass_action(sir_model(); κ = κ_old)
        src = symbolic_ode(sys)
        old = Semiconjugacy(:old_to_mass_action, src, old_target,
                            [old_target.states[1] => q * exp(5.0 * (c[:θ] - 1)), old_target.states[2] => c[:φ_I],
                             old_target.states[3] => c[:φ_R]])
        ro = verify(old)
        @test !ro.ok
        @test ro.max_residual > 1e-2
        @test occursin(r"residual of dI/dt: -(τ\*φ_I|φ_I\*τ)\s*$"m, ro.details)
        ros = verify(old; method = :symbolic)
        @test !ros.ok && occursin("does not simplify to 0 in component(s) I", ros.details)
        # … nor with I read as the prevalence pop_I (to_mass_action's docstring), nor onto E_μ
        prev = Semiconjugacy(:old_prevalence, src, old_target,
                             [old_target.states[1] => q * exp(5.0 * (c[:θ] - 1)), old_target.states[2] => c[:pop_I],
                              old_target.states[3] => c[:pop_R]])
        @test !verify(prev).ok
        @test !verify(Semiconjugacy(:prevalence, src, img.ode,
                                    [img.ode.states[1] => q * exp(5.0 * (c[:θ] - 1)), img.ode.states[2] => c[:pop_I],
                                     img.ode.states[3] => c[:pop_R]])).ok
        # the old SEIR map dropped σ (an SIR MA(5τ, γ) on S, I = φ_I, R = φ_R): not a semiconjugacy
        sysE = edge_based(seir_model(), POIS5)
        cE = sysE.metadata[:coords]
        qE = sysE.metadata[:q][:S].param
        oldE = mass_action(sir_model(); κ = 5.0)
        @test !verify(Semiconjugacy(:old_seir, symbolic_ode(sysE), oldE,
                                    [oldE.states[1] => qE * exp(5.0 * (cE[:θ] - 1)), oldE.states[2] => cE[:φ_I],
                                     oldE.states[3] => cE[:φ_R]])).ok
    end

    @testset "Rempała along the :sir_pois5 trajectories: S(t) to 1e-9; the MA I is φ_I (E08)" begin
        sc = scenario(:sir_pois5)
        p = sc.params
        sys = edge_based(sc)
        h = 0.01
        tg = collect(0.0:h:60.0)
        sol = eb_solve(sys, p, sc.initial, tg)
        S_eb, φI, prev = compartment(sys, sol, :S), compartment(sys, sol, :φ_I), compartment(sys, sol, :pop_I)
        img = mass_action(sys; form = :edge)
        u0 = target_initial(img, sys, sol)
        @test u0[:S] ≈ 0.99 atol = 1e-14
        @test u0[:I] ≈ 0.01 atol = 1e-14
        @test u0[:R] == 0
        ma = integrate(img.ode, p, u0, tg)
        @test maximum(abs.(ma[:S] .- S_eb)) < 1e-9
        @test maximum(abs.(ma[:I] .- φI)) < 1e-9
        # a hand-written RK4 of Rempała's MA(μτ, γ + τ) (independent of the package)
        μ, τ, γ = 5.0, p[:τ], p[:γ]
        fma(β, g) = u -> [-β * u[1] * u[2], β * u[1] * u[2] - g * u[2]]
        rk = rk4(fma(μ * τ, γ + τ), [0.99, 0.01], h, length(tg) - 1)
        @test maximum(abs.(first.(rk) .- S_eb)) < 1e-9
        # the MA "I" is φ_I, not the prevalence (Rempała: I = x_D/μ); the maximal gap is 0.084
        gap = maximum(abs.(ma[:I] .- prev))
        @test gap ≈ 0.084 atol = 1e-3
        # the old map MA(μτ, γ): max|ΔS| = 0.2777 and S(40) = 0.0406 against 0.2000 (E08)
        old = rk4(fma(μ * τ, γ), [0.99, 0.01], h, length(tg) - 1)
        k40 = findfirst(==(40.0), tg)
        @test maximum(abs.(first.(old) .- S_eb)) ≈ 0.2777 atol = 1e-3
        @test first(old[k40]) ≈ 0.0406 atol = 5e-4
        @test S_eb[k40] ≈ 0.2000 atol = 5e-4
        # pushforward along the solution is the same curve
        pf = pushforward(img, sys, sol, tg)
        @test maximum(abs.(pf[:S] .- S_eb)) < 1e-12
        @test maximum(abs.(pf[:I] .- φI)) < 1e-12
        # the prevalence: the node copy I of D_μ (form = :exact), i.e. Rempała's corrected
        # dI_node/dt = β S φ_I − γ I_node (eq. 15)
        imgE = mass_action(sys; form = :exact)
        maE = integrate(imgE.ode, p, target_initial(imgE, sys, sol), tg)
        @test maximum(abs.(maE[:I] .- prev)) < 1e-9
        @test maximum(abs.(maE[:S] .- S_eb)) < 1e-9
        # the compact form (M9) gives the same S(t) through its embedding
        sysC = edge_based(sir_model(), POIS5; form = :compact)
        solC = eb_solve(sysC, p, sc.initial, tg)
        imgC = mass_action(sysC; form = :edge)
        @test imgC.morphism.kind === :semiconjugacy
        @test verify(imgC.morphism).ok
        pfC = pushforward(imgC, sysC, solC, tg)
        @test maximum(abs.(pfC[:S] .- S_eb)) < 1e-9
        @test maximum(abs.(pfC[:I] .- φI)) < 1e-9
    end

    @testset "M4: power-law kinetics on Poisson-type networks (form = :exact)" begin
        for (id, κ) in ((:sir_nb4, 5 / 4), (:sir_reg6, 5 / 6))
            sc = scenario(id)
            sys = edge_based(sc)
            img = mass_action(sys; form = :exact)
            @test img.kind === :power_law && img.morphism.name === :power_law && img.model === nothing
            @test img.morphism.kind === :conjugacy
            r = verify(img.morphism)
            @test r.ok && r.max_residual <= 1e-10
            @test any(n -> occursin("κ = $(float(κ))", n), img.notes)
            # along the trajectory: S and the prevalence to 1e-9
            tg = collect(0.0:0.5:60.0)
            sol = eb_solve(sys, sc.params, sc.initial, tg)
            ma = integrate(img.ode, merge(sc.params, Dict(:q_S => 0.99)), target_initial(img, sys, sol), tg)
            @test maximum(abs.(ma[:S] .- compartment(sys, sol, :S))) < 1e-9
            @test maximum(abs.(ma[:I] .- compartment(sys, sol, :pop_I))) < 1e-9
            # perturbed: the Poisson reduction (D_μ with μ = ⟨k⟩) on this network is not exact
            k̄ = mean_degree(sc.network)
            dμ = mass_action(edge_doubling(sc.model, k̄))
            byname = Dict(name(x) => v for (x, v) in img.morphism.map)
            @test !verify(Semiconjugacy(:poisson_on_pt, img.morphism.source, dμ,
                                        [x => byname[n] for (x, n) in zip(dμ.states, state_names(dμ))])).ok
        end
        # SEIR and vaccination (exits: the auxiliary Ξ = ξ carries the factor (qξ)^{1−κ})
        for cm in (seir_model(), sirv_model())
            img = mass_action(edge_based(cm, NB4); form = :exact)
            @test img.kind === :power_law
            @test (:Ξ in state_names(img.ode)) == (cm.name === :sirv)
            @test verify(img.morphism).ok
        end
    end

    @testset "M5: general kinetics for any ψ (form = :general, as_reaction_system)" begin
        rem = ContactModel(:rem; contacts = [Contact(:S, :I, :I, :τ)], transitions = [NodeTransition(:I, nothing, :γ)])
        pl = ConfigurationNetwork(PowerLawDegree(2.5; kmin = 2, kmax = 60))
        for net in (BIM, pl, NB4), cm in (sir_model(), seair_model(), sirv_model(), rem)
            sys = edge_based(cm, net)
            img = mass_action(sys; form = :general)
            @test img.kind === :general && img.morphism.kind === :conjugacy && img.exactness === :exact
            r = verify(img.morphism)
            @test r.ok && r.max_residual <= 1e-10
            @test first(state_names(img.ode)) === :Θ
            @test (:Ξ in state_names(img.ode)) == (cm.name === :sirv)
            @test (:removed in state_names(img.ode)) == (cm.name === :rem)       # the sink is a species
        end
        sc = scenario(:sir_pl)
        sys = edge_based(sc)
        data = as_reaction_system(sys)
        @test data isa ReactionNetworkData
        @test data.species == [:Θ, :Φ_I, :Φ_R, :I, :R]
        @test vector_fields_equal(mass_action(data), mass_action(sys; form = :general).ode)
        tg = collect(0.0:0.5:80.0)
        sol = eb_solve(sys, sc.params, sc.initial, tg)
        img = mass_action(sys; form = :general)
        ma = integrate(img.ode, merge(sc.params, Dict(:q_S => 0.99)), target_initial(img, sys, sol), tg)
        @test maximum(abs.(ma[:I] .- compartment(sys, sol, :pop_I))) < 1e-9
        @test maximum(abs.(ma[:Θ] .- compartment(sys, sol, :θ))) < 1e-9
        # the reaction network of the other forms
        sysP = edge_based(sir_model(), POIS5)
        @test as_reaction_system(sysP; form = :edge).species == [:S, :I, :R]
        @test as_reaction_system(sysP; form = :exact).species == [:S, :Φ_I, :Φ_R, :I, :R]
    end

    @testset "M6: EB → S-anchored pairwise with K_ψ = ψψ''/ψ'² (pairwise_image)" begin
        rem = ContactModel(:rem; contacts = [Contact(:S, :I, :I, :τ)], transitions = [NodeTransition(:I, nothing, :γ)])
        for (cm, net) in ((sir_model(), BIM), (sirv_model(), POIS5), (seair_model(), POIS5),
                          (sir_model(), ConfigurationNetwork(RegularDegree(6))), (rem, BIM), (sirv_model(), BIM),
                          (seir_model(), BIM))
            sys = edge_based(cm, net)
            pw = pairwise_image(sys)
            @test pw.ode === pw.morphism.target
            @test pw.morphism.name === :eb_to_pws && pw.morphism.kind === :semiconjugacy
            r = verify(pw.morphism)
            @test r.ok && r.max_residual <= 1e-10
        end
        # :sir_bim and :sir_vax_pois5 (the acceptance scenarios)
        for id in (:sir_bim, :sir_vax_pois5)
            r = verify(pairwise_image(edge_based(scenario(id))).morphism)
            @test r.ok && r.max_residual <= 1e-10
        end
        # an independent transcription of PW^S for SIR (ordered pairs; [Z s J] = K[Zs][sJ]/[s]; the
        # auxiliary θ̇ = −τ[sI]ψ(θ)/([s]ψ'(θ))); with K = K_ψ(θ) it is the image, with the constant
        # closure K = ψ''(1)/ψ'(1)² it is exact iff ψ is Poisson type (M8)
        function pws_sir(d, K)
            τ, γ = as_parameter.((:τ, :γ))
            @variables t θ(t) S(t) SI(t) SR(t) SS(t) I(t) R(t)
            k = K === :psi ? pgf(d, θ) * pgf_derivative(d, θ, 2) / pgf_derivative(d, θ, 1)^2 : K
            return SymbolicODE(:hand_pws; states = [θ, S, SI, SR, SS, I, R],
                               rhs = [-τ * SI * pgf(d, θ) / (S * pgf_derivative(d, θ, 1)),
                                      -τ * SI,
                                      -τ * SI - τ * k * SI^2 / S + τ * k * SS * SI / S - γ * SI,
                                      -τ * k * SI * SR / S + γ * SI,
                                      -2τ * k * SS * SI / S,
                                      τ * SI - γ * I,
                                      γ * I],
                               domain = [θ => (0.05, 1.0)])
        end
        for (net, pt) in ((BIM, false), (ConfigurationNetwork(RegularDegree(6)), true), (POIS5, true))
            sys = edge_based(sir_model(), net)
            pw = pairwise_image(sys)
            @test state_names(pw.ode) == [:θ, :S, :SI, :SR, :SS, :I, :R]
            @test vector_fields_equal(pw.ode, pws_sir(net.degrees, :psi); rename = :none)
            K = closure_constant(net.degrees)
            cst = pws_sir(net.degrees, K)
            mc = Semiconjugacy(:constant_closure, pw.morphism.source, cst,
                               [x => v for (x, (_, v)) in zip(cst.states, pw.morphism.map)])
            @test verify(mc).ok == pt
        end
        # perturbed map: [ss] without the division by ψ'(1)
        sys = edge_based(sir_model(), BIM)
        pw = pairwise_image(sys)
        c = sys.metadata[:coords]
        q = sys.metadata[:q][:S].param
        bad = [x => (name(x) === :SS ? (q * pgf_derivative(BIM.degrees, c[:θ], 1))^2 : v) for (x, v) in pw.morphism.map]
        @test !verify(Semiconjugacy(:bad_ss, pw.morphism.source, pw.ode, bad)).ok
        # along the :sir_bim trajectory: [s] = S, [X] = pop_X, [sI] = qψ'(θ)φ_I to 1e-8
        sc = scenario(:sir_bim)
        sys = edge_based(sc)
        tg = collect(0.0:0.5:60.0)
        sol = eb_solve(sys, sc.params, sc.initial, tg)
        pw = pairwise_image(sys)
        u = integrate(pw.ode, sc.params, target_initial(pw.morphism, sys, sol), tg)
        @test maximum(abs.(u[:S] .- compartment(sys, sol, :S))) < 1e-8
        @test maximum(abs.(u[:I] .- compartment(sys, sol, :pop_I))) < 1e-8
        pf = pushforward(pw.morphism, sys, sol, tg)
        @test maximum(abs.(u[:SI] .- pf[:SI])) < 1e-8
        # the compact form
        @test verify(pairwise_image(edge_based(sir_model(), BIM; form = :compact)).morphism).ok
    end

    @testset "Λ1: the dense ladder (form = :limit); the error ratio ≈ μ₂/μ₁" begin
        tg = collect(0.0:0.25:60.0)
        errs = Dict{Int,Float64}()
        for μ in (5, 20, 100, 1000)
            # :sir_dense_pois<μ> (μτ = 1/2, γ = 1/4, 1% seeded in I), and μ = 1000 beyond the registry
            net = ConfigurationNetwork(PoissonDegree(Float64(μ)))
            p = Dict(:τ => 1 / (2μ), :γ => 1 / 4)
            initial = SeedFraction(:I => 0.01)
            if μ != 1000
                sc = scenario(Symbol(:sir_dense_pois, μ))
                @test sc.params == p && sc.initial == initial && mean_degree(sc.network) == μ
            end
            sys = edge_based(sir_model(), net)
            img = mass_action(sys; form = :limit)
            @test img.exactness === :limit && img.morphism.exactness === :limit
            @test vector_fields_equal(img.ode, mass_action(sir_model(); κ = Float64(μ)))   # MA(μτ, γ)
            sol = eb_solve(sys, p, initial, tg)
            ma = integrate(img.ode, p, target_initial(img, sys, sol), tg)
            @test ma[:S][end] < ma[:S][1]
            errs[μ] = maximum(abs.(ma[:S] .- compartment(sys, sol, :S)))
        end
        @info "WP18 Λ1 ladder: max_t |S_EB − S_MA(μτ = 1/2, γ = 1/4)|" errs
        @test errs[5] > errs[20] > errs[100] > errs[1000]
        @test errs[20] / errs[100] ≈ 100 / 20 rtol = 0.05                  # O(1/μ)
        @test errs[100] / errs[1000] ≈ 1000 / 100 rtol = 0.02
        # the κ sweep of verified issue E08 (independent plain ODEs of the E08 verifier, which the old
        # to_mass_action map MA(κτ, γ) equals on Poisson(κ)): κτ = 1.5, γ = 0.1, ρ = 10⁻³, t ∈ [0, 80]:
        # max|ΔS| = 3.515e-1, 8.729e-2, 1.730e-2, 1.726e-3 at κ = 5, 20, 100, 1000
        tg80 = collect(range(0, 80; length = 2001))
        for (κ, ref) in ((5, 3.515e-1), (20, 8.729e-2), (100, 1.730e-2), (1000, 1.726e-3))
            p = Dict(:τ => 1.5 / κ, :γ => 0.1)
            sys = edge_based(sir_model(), ConfigurationNetwork(PoissonDegree(Float64(κ))))
            sol = eb_solve(sys, p, SeedFraction(:I => 1e-3), tg80)
            img = mass_action(sys; form = :limit)
            ma = integrate(img.ode, p, target_initial(img, sys, sol), tg80)
            @test maximum(abs.(ma[:S] .- compartment(sys, sol, :S))) ≈ ref rtol = 2e-3
        end
        # a limit is not a morphism
        @test !verify(mass_action(edge_based(scenario(:sir_dense_pois5)); form = :limit).morphism).ok
    end

    @testset "calibrations (form = :calibrated): not morphisms" begin
        # the R₀-matched MA of :sir_pois5 is MA(1/2, 1/4): the same final size (0.8002), peak at
        # t ≈ 17.5 instead of 11.35 (design §D.5)
        sc = scenario(:sir_pois5)
        sys = edge_based(sc)
        img = mass_action(sys; form = :calibrated, p = sc.params)
        @test img.exactness === :calibration && img.morphism.exactness === :calibration
        c = only(contacts(img.model))
        @test rate_value(c.rate, sc.params) ≈ 1 / 2 rtol = 1e-10
        @test !verify(img.morphism).ok
        tg = collect(0.0:0.01:400.0)
        sol = eb_solve(sys, sc.params, sc.initial, tg)
        ma = integrate(img.ode, sc.params, target_initial(img, sys, sol), tg)
        @test 1 - ma[:S][end] ≈ sc.expected[:final_size] atol = 1e-6
        @test compartment(sys, sol, :cumulative)[end] ≈ sc.expected[:final_size] atol = 1e-6
        @test tg[argmax(ma[:I])] ≈ 17.5 atol = 0.1
        @test tg[argmax(compartment(sys, sol, :pop_I))] ≈ 11.35 atol = 0.05
        # growth-rate and final-size calibrations on the bimodal network (NetworkEpiCore's engine)
        scb = scenario(:sir_bim)
        sysb = edge_based(scb)
        g = mass_action(sysb; form = :calibrated, p = scb.params, target = :growth)
        @test early_growth_rate(g.model, WellMixed(1.0), scb.params) ≈
              early_growth_rate(scb.model, scb.network, scb.params) rtol = 1e-9
        z = mass_action(sysb; form = :calibrated, p = scb.params, target = :final_size, initial = scb.initial)
        @test final_size(z.model, WellMixed(1.0), scb.params; initial = scb.initial) ≈
              final_size(scb.model, scb.network, scb.params; initial = scb.initial) rtol = 1e-8
        r0 = mass_action(sysb; form = :calibrated, p = scb.params)
        @test basic_reproduction_number(r0.model, WellMixed(1.0), scb.params) ≈ 2.0 rtol = 1e-10
        @test occursin("target must be :R0", err(() -> mass_action(sysb; form = :calibrated, p = scb.params, target = :peak)))
    end

    @testset "natural transformations M1–M6 are registered" begin
        mine = (:well_mixed_unit, :poisson_iso, :rempala, :power_law, :general_kinetics, :eb_to_pws)
        names_ = [η.name for η in transformations(; source = :edge_based)]
        for n in mine
            @test n in names_
        end
        ours(cm, net) = Set(η.name for η in transformations(cm, net; source = :edge_based) if η.name in mine)
        @test transformation(:rempala).target === :mass_action
        @test transformation(:eb_to_pws).target === :s_anchored
        @test transformation(:power_law).target === :power_law_kinetics
        wm = WellMixed(5.0)
        @test ours(sir_model(), POIS5) == Set([:poisson_iso, :rempala, :general_kinetics, :eb_to_pws])
        @test ours(sir_model(), NB4) == Set([:power_law, :general_kinetics, :eb_to_pws])
        @test ours(sir_model(), wm) == Set([:well_mixed_unit])
        @test isempty(ours(sis_model(), POIS5))                                      # not a T_EB model
        for (n, cm, net) in ((:well_mixed_unit, seir_model(), wm), (:poisson_iso, seair_model(), POIS5),
                             (:rempala, seir_model(), POIS5), (:power_law, seir_model(), NB4),
                             (:general_kinetics, sirv_model(), BIM), (:eb_to_pws, seir_model(), BIM))
            m = transformation(n)(cm, net)
            @test m isa Semiconjugacy && verify(m).ok
        end
        @test_throws ArgumentError transformation(:rempala)(sir_model(), BIM)
        # naturality of Rempała's quotient under gluing two strains on S and R (H1 for E_μ)
        A = open_model(ContactModel(:a; contacts = [Contact(:S, :I1, :I1, :τ1)], transitions = [NodeTransition(:I1, :R, :γ)]);
                       legs = [[:S, :R]])
        B = open_model(ContactModel(:b; contacts = [Contact(:S, :I2, :I2, :τ2)], transitions = [NodeTransition(:I2, :R, :γ)]);
                       legs = [[:S, :R]])
        rn = check_naturality(transformation(:rempala), A, B; network = POIS5, on = [:S, :R])
        @test rn.ok
    end

    @testset "errors, and the migration texts of to_mass_action and compare_models" begin
        sys = edge_based(sir_model(), BIM)
        msg = err(() -> mass_action(sys))
        @test startswith(msg, "ArgumentError: mass_action(sys; form): choose the sense")
        for f in EBM.MASS_ACTION_FORMS
            @test occursin(":$f", msg)
        end
        @test occursin("unknown form", err(() -> mass_action(sys; form = :approximate)))
        @test occursin("Rempała's quotient (form = :edge, M3) needs a Poisson degree distribution",
                       err(() -> mass_action(sys; form = :edge)))
        e = err(() -> mass_action(sys; form = :exact))
        @test occursin("Poisson-type", e) && occursin("form = :general", e)
        wm = edge_based(sir_model(), WellMixed(5.0))
        for f in (:edge, :general, :limit, :calibrated)
            @test occursin("use form = :exact", err(() -> mass_action(wm; form = f, p = Dict(:τ => 0.1, :γ => 0.25))))
        end
        @test occursin("WellMixed network has no network pairs", err(() -> pairwise_image(wm)))
        # a system not built by edge_based (the 0.1 builders, deleted by WP29, recorded :legacy)
        legacy = EdgeModelSystem(sys.system, sys.variables, sys.observables, Dict{Symbol,Any}(:kind => :legacy))
        @test occursin("not built by edge_based", err(() -> mass_action(legacy; form = :general)))
        @test occursin("not built by edge_based", err(() -> pairwise_image(legacy)))
        st = strata([:a, :b]; sizes = [0.5, 0.5])
        mt = edge_based(stratify(sir_model(τ = 0.2, γ = 0.25), st), unstructured(POIS5, st))
        @test occursin("ConfigurationNetwork or a WellMixed network", err(() -> mass_action(mt; form = :general)))
        # the removed functions (src/deprecated.jl) error with the migration message: γ must become
        # γ + τ (Rempała), I is φ_I, and every form it lists is a form of mass_action
        for f in (() -> to_mass_action(StaticConfigurationModel(poisson_pgf(5.0), DiseaseProgression(sir_model()))),
                  () -> compare_models(StaticConfigurationModel(poisson_pgf(5.0), DiseaseProgression(sir_model()))),
                  () -> to_mass_action(sys))
            m = err(f)
            @test startswith(m, "to_mass_action and compare_models are removed (verified issue E08)")
            @test occursin("MA(β = μτ, γ + τ)", m) && occursin("γ + τ", m) && occursin("φ_I", m)
            @test occursin("mass_action(sys; form)", m)
            for f in EBM.MASS_ACTION_FORMS
                @test occursin(":$f", m)
            end
        end
        @test_throws ErrorException to_mass_action(sys)
        @test_throws ErrorException compare_models(sys)
    end

    @testset "E08 against NetworkOutbreaks: Rempała's S(t) and D_μ's prevalence (ER, N = 10⁴)" begin
        # Protocol (DESIGN §E.2, §J.7): a fresh Erdős–Rényi graph G(N, 5/(N − 1)) per run from
        # NetworkOutbreaks.stable_rng(base + r), the SSA from stable_rng(base + 2³² + r), 1% seeded in
        # I uniformly, NextReaction, runs conditioned on a major outbreak (ever infected minus seeds
        # ≥ 0.05 N). The SE is that of the conditioned mean at the time of the largest difference.
        sc = scenario(:sir_pois5)
        p = sc.params
        N, runs, base = 10_000, 40, 20260926
        tg = collect(0.0:0.5:60.0)
        sys = edge_based(sc)
        sol = eb_solve(sys, p, sc.initial, tg)
        edge = integrate(mass_action(sys; form = :edge).ode, p, Dict(:S => 0.99, :I => 0.01, :R => 0.0), tg)
        imgE = mass_action(sys; form = :exact)
        node = integrate(imgE.ode, p, target_initial(imgE, sys, sol), tg)
        old = integrate(mass_action(sir_model(); κ = 5.0), p, Dict(:S => 0.99, :I => 0.01, :R => 0.0), tg)
        model = NO.OutbreakModel([:S, :I, :R], [false, true, false],
                                 [NO.OutbreakTransition(:S, :I, p[:τ], :infection),
                                  NO.OutbreakTransition(:I, :R, p[:γ], :spontaneous)])
        Ss, Is = Vector{Vector{Float64}}(), Vector{Vector{Float64}}()
        for r in 1:runs
            g = Graphs.erdos_renyi(N, 5.0 / (N - 1); rng = NO.stable_rng(base + r))
            spec = NO.OutbreakSpec(; model, network = g, initial = NO.SeedFraction(:I => 0.01),
                                   tspan = (0.0, tg[end]))
            traj = NO.simulate(spec; algorithm = NO.NextReaction(), rng = NO.stable_rng(base + 2^32 + r))
            states = [NO.state_at(traj, t) for t in tg]
            ever = states[end][2] + states[end][3]
            ever - 0.01N >= 0.05N || continue
            push!(Ss, [c[1] / N for c in states])
            push!(Is, [c[2] / N for c in states])
        end
        @test length(Ss) >= runs - 2
        S_sim, I_sim = mean(Ss), mean(Is)
        se(xs, k) = std(getindex.(xs, k)) / sqrt(length(xs))
        dS, kS = findmax(abs.(S_sim .- edge[:S]))
        dI, kI = findmax(abs.(I_sim .- node[:I]))
        dold = maximum(abs.(S_sim .- old[:S]))
        dφ = maximum(abs.(I_sim .- edge[:I]))
        @info("WP18 E08 vs NetworkOutbreaks (:sir_pois5 on ER graphs)", N, runs, major = length(Ss),
              max_abs_dS_rempala = dS, se_S = se(Ss, kS), max_abs_dI_prevalence = dI,
              se_I = se(Is, kI), max_abs_dS_old_map = dold, max_abs_dI_if_I_were_φ_I = dφ)
        @test dS <= 0.01                           # Rempała's S(t) is the network's
        @test dI <= 0.01                           # D_μ's node copy I is the prevalence
        @test dold >= 0.2                          # the old map MA(μτ, γ) is far off (0.28)
        @test dφ >= 0.05                           # Rempała's I (φ_I) is not the prevalence
    end
end
