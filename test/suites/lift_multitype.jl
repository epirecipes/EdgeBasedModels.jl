# WP17: the multitype lift (DESIGN §C.3 MultitypeNetwork, §D.5 M10, §J.6; Miller & Volz 2013 §3.3).
#
# - Scenarios :sir_sbm2, :sir_unstr2, :sir_age2: conservation (node, and per edge class
#   θ_{b→a} = φ_{s_b,a} + Σ_Y φ_{Y,a}), NetworkEpiCore's multitype final size (its own
#   fixed point, with the §J.6 seeding convention) and growth rate.
# - Acceptance 5, structural zeros (verified issues E11, E32; ebm-core #11): absent edge classes
#   produce no coordinates, no NaN and no phantom θ → −∞; the bipartite values of E11/E32
#   (hand-coded Miller–Volz EBCM and NetworkOutbreaks simulation); a symbolic block mean that is 0
#   at solve time gives the block-diagonal model, not NaN.
# - Acceptance 6, the M10 unit law: on unstructured(net, st) with seeds proportional to the sizes
#   the stratified lift is the untyped one (θ_{b→a} = θ, φ_{X_b,a} = φ_X, pop_{X_b} = n_b pop_X),
#   and with one stratum the two fields are equal up to renaming.
# - §J.6: SeedFraction(:I_a => ρ) is a fraction of ALL nodes (within-type ρ/n_a).

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using LinearAlgebra
using OrdinaryDiffEq: Vern9
using Test

const TOL = (solver = Vern9(), reltol = 1e-12, abstol = 1e-14)

curve(sys, sol, X) = compartment(sys, sol, X)

# Node conservation Σ_a S_a + Σ pop = 1 and edge conservation per class, max over time.
function multitype_conservation(sys, sol)
    Σ = sys.metadata[:susceptible]
    Σ = Σ isa Symbol ? [Σ] : Σ
    pops = [k for k in keys(sys.variables) if startswith(string(k), "pop_")]
    node = maximum(abs.(sum(curve(sys, sol, s) for s in Σ) .+ sum(curve(sys, sol, k) for k in pops) .- 1))
    info = sys.metadata[:contributions].coordinate_info
    cm = sys.metadata[:model]
    edge = 0.0
    for θ in info
        θ.role === :θ || continue
        b, a = θ.types                                             # partner type b, test type a
        s_b = only(s for s in Σ if species_labels(cm)[s].stratum === b)
        total = curve(sys, sol, Symbol(:φ_, s_b, :_, a))
        for x in info
            (x.role === :φ && x.types == (b, a)) && (total = total .+ curve(sys, sol, x.name))
        end
        edge = max(edge, maximum(abs.(curve(sys, sol, θ.name) .- total)))
    end
    return node, edge
end

numval(e, at) = Float64(Symbolics.value(Symbolics.substitute(e, at; fold = Val(true))))

function early_growth(ode::SymbolicODE, p)
    J = Symbolics.jacobian(Num.(ode.rhs), Num.(ode.states))
    at = Dict{Any,Any}()
    for x in ode.states
        n = string(Symbolics.getname(x))
        at[x] = (startswith(n, "θ") || startswith(n, "ξ")) ? 1.0 : 0.0
    end
    for q in ode.parameters
        n = Symbol(Symbolics.getname(q))
        at[q] = startswith(string(n), "q_") ? 1.0 : p[n]
    end
    M = [numval(J[i, j], at) for i in axes(J, 1), j in axes(J, 2)]
    return maximum(real.(eigvals(M)))
end

@testset "lift: MultitypeNetwork" begin
    @testset "scenarios: conservation, NetworkEpiCore's final size and growth rate" begin
        for id in (:sir_sbm2, :sir_unstr2, :sir_age2)
            sc = scenario(id)
            @testset "$id" begin
                sys = edge_based(sc)
                @test sys.metadata[:closure] === :multitype
                sol = solve_epidemic(sys; p = sc.params, initial = sc.initial, tspan = (0.0, 800.0), saveat = 5.0, TOL...)
                @test string(sol.retcode) == "Success"
                node, edge = multitype_conservation(sys, sol)
                @test node < 1e-10 && edge < 1e-10
                @test curve(sys, sol, :cumulative)[1] ≈ sum(last, seed_fractions(sc.initial)) atol = 1e-14
                @test curve(sys, sol, :cumulative)[end] ≈ sc.expected[:final_size] atol = 1e-7
                @test early_growth(symbolic_ode(sys), sc.params) ≈ sc.expected[:r] rtol = 1e-6
            end
        end
    end

    @testset "structural zeros: no coordinates, no NaN, the E11/E32 bipartite values" begin
        # E11: a-nodes with Poisson(4) b-neighbours, b-nodes with Poisson(2) a-neighbours
        # (N_a = 10⁴, N_b = 2·10⁴: sizes 1/3, 2/3), β = γ = 1, 1% of each type seeded. A
        # hand-coded Miller–Volz bipartite EBCM gives final attacks 0.6049679080 (a) and
        # 0.4593689680 (b); NetworkOutbreaks 0.6057 ± 0.0018 and 0.4612 ± 0.0014 (25 runs). The
        # legacy builder had phantom classes whose θ fell to −18.75 by t = 40.
        net = MultitypeNetwork([:a, :b], [1 / 3, 2 / 3],
                               [IndependentDegrees(:b => PoissonDegree(4.0)), IndependentDegrees(:a => PoissonDegree(2.0))])
        @test net.structural_zero == [true false; false true]
        st = strata([:a, :b]; sizes = [1 / 3, 2 / 3])
        cm = stratify(sir_model(τ = 1.0, γ = 1.0), st)
        sys = edge_based(cm, net)
        ks = Set(keys(sys.variables))
        @test !(:θ_a_a in ks) && !(:θ_b_b in ks) && :θ_a_b in ks && :θ_b_a in ks
        @test !(:φ_I_a_a in ks) && !(:φ_I_b_b in ks) && :φ_I_a_b in ks && :φ_I_b_a in ks
        sol = solve_epidemic(sys; initial = SeedFraction(:I_a => 0.01 / 3, :I_b => 0.02 / 3), tspan = (0.0, 200.0),
                             saveat = 1.0, TOL...)
        @test all(k -> all(isfinite, curve(sys, sol, k)), ks)
        @test all(k -> all(x -> 0 <= x <= 1 + 1e-12, curve(sys, sol, k)), [:θ_a_b, :θ_b_a])
        # the legacy hazards exist for the edge classes only, and edge_hazard_<b>_<a> = −θ̇_{b→a}
        os = Set(keys(sys.observables))
        @test :edge_hazard_b_a in os && :edge_hazard_a_b in os && :excess_hazard_a_b in os && :excess_hazard_b_a in os
        @test !(:edge_hazard_a_a in os) && !(:edge_hazard_b_b in os) && !(:excess_hazard_a_a in os) && !(:excess_hazard_b_b in os)
        @test all(k -> all(isfinite, curve(sys, sol, k)), os)
        @test curve(sys, sol, :edge_hazard_b_a) ≈ curve(sys, sol, :φ_I_b_a) rtol = 1e-14      # τ = 1
        fld = symbolic_ode(sys)
        iθ = findfirst(x -> Symbol(Symbolics.getname(x)) === :θ_b_a, fld.states)
        @test isequal(fld.rhs[iθ], -sys.variables[:φ_I_b_a]) || isequal(fld.rhs[iθ], -1.0 * sys.variables[:φ_I_b_a])
        @test 1 - curve(sys, sol, :S_a)[end] * 3 ≈ 0.6049679080 atol = 1e-8
        @test 1 - curve(sys, sol, :S_b)[end] * 1.5 ≈ 0.4593689680 atol = 1e-8
        node, edge = multitype_conservation(sys, sol)
        @test node < 1e-12 && edge < 1e-12
        # E32's bipartite case: κ_AB = 6, κ_BA = 4 (sizes 0.4, 0.6), β = 0.7, γ = 1, 0.5% of each
        # type seeded; NetworkOutbreaks (N = 10⁵, 100 runs): R_A(30) = 0.8454 ± 0.0003,
        # R_B(30) = 0.7528 ± 0.0002; the EBCM 0.8450 and 0.7526.
        netB = MultitypeNetwork([:A, :B], [0.4, 0.6],
                                [IndependentDegrees(:B => PoissonDegree(6.0)), IndependentDegrees(:A => PoissonDegree(4.0))])
        stB = strata([:A, :B]; sizes = [0.4, 0.6])
        sysB = edge_based(stratify(sir_model(τ = 0.7, γ = 1.0), stB), netB)
        solB = solve_epidemic(sysB; initial = SeedFraction(:I_A => 0.002, :I_B => 0.003), tspan = (0.0, 30.0),
                              saveat = 1.0, TOL...)
        @test curve(sysB, solB, :pop_R_A)[end] / 0.4 ≈ 0.8450 atol = 5e-4
        @test curve(sysB, solB, :pop_R_B)[end] / 0.6 ≈ 0.7526 atol = 5e-4
        @test curve(sysB, solB, :φ_S_A_B)[1] ≈ 0.995 atol = 1e-14            # legacy: 1 (phantom)
        # the final sizes are NetworkEpiCore's multitype fixed point
        solL = solve_epidemic(sys; initial = SeedFraction(:I_a => 0.01 / 3, :I_b => 0.02 / 3), tspan = (0.0, 500.0), TOL...)
        @test curve(sys, solL, :cumulative)[end] ≈
              final_size(cm, net, Dict{Symbol,Float64}(); initial = SeedFraction(:I_a => 0.01 / 3, :I_b => 0.02 / 3)) atol = 1e-8
    end

    @testset "E32: a symbolic block mean that is 0 at solve time gives the block-diagonal model" begin
        # The cross blocks are Poisson mixtures with symbolic means k₁, k₂ (Symbolics cannot cancel
        # (k₁e^… + k₂e^…)/(k₁ + k₂)); at k₁ = k₂ = 0 the network is block diagonal. The legacy
        # builder stopped with DtNaN on such a model; here the κ → 0 limit is selected.
        @parameters k1 k2
        cross = MixtureDegree([0.5, 0.5], [PoissonDegree(k1), PoissonDegree(k2)])
        netS = MultitypeNetwork([:a, :b], [0.5, 0.5],
                                [IndependentDegrees(:a => PoissonDegree(4.0), :b => cross),
                                 IndependentDegrees(:a => cross, :b => PoissonDegree(3.0))])
        st = strata([:a, :b]; sizes = [0.5, 0.5])
        cm = stratify(sir_model(τ = 0.4, γ = 0.3), st)
        sys = edge_based(cm, netS)
        init = SeedFraction(:I_a => 0.005, :I_b => 0.005)
        ic = default_initial_conditions(sys; initial = init)
        sol0 = solve_epidemic(sys; init = merge(ic, Dict(k1 => 0.0, k2 => 0.0)), tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        @test string(sol0.retcode) == "Success"
        @test all(k -> all(isfinite, curve(sys, sol0, k)), keys(sys.variables))
        # the observables too: at k₁ = k₂ = 0 the cross excess hazard is the κ → 0 limit of E11,
        # Σ_c h_{c→a}∂_cψ_a/ψ_a, not 0/0. It is the rate at which the limit φ_{S_a,b} = q_aψ_a(θ)
        # decays: here 4·edge_hazard_a_a for type a (ψ_a = e^{4(x_a−1)}, ∂_bψ_a ≡ 0) and
        # 3·edge_hazard_b_b for type b, continuous with a tiny positive cross mean.
        @test all(k -> all(isfinite, curve(sys, sol0, k)), keys(sys.observables))
        @test curve(sys, sol0, :excess_hazard_a_b) ≈ 4 .* curve(sys, sol0, :edge_hazard_a_a) rtol = 1e-12
        @test curve(sys, sol0, :excess_hazard_b_a) ≈ 3 .* curve(sys, sol0, :edge_hazard_b_b) rtol = 1e-12
        @test all(>(0), curve(sys, sol0, :excess_hazard_a_b))
        φSab = curve(sys, sol0, :φ_S_a_b)
        @test φSab ≈ 0.99 .* exp.(4 .* (curve(sys, sol0, :θ_a_a) .- 1)) rtol = 1e-12
        solε = solve_epidemic(sys; init = merge(ic, Dict(k1 => 1e-9, k2 => 1e-9)), tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        for k in (:excess_hazard_a_b, :excess_hazard_b_a, :excess_hazard_a_a, :φ_S_a_b, :S_a)
            @test maximum(abs.(curve(sys, solε, k) .- curve(sys, sol0, k))) < 1e-8
        end
        diag = MultitypeNetwork([:a, :b], [0.5, 0.5], [IndependentDegrees(:a => PoissonDegree(4.0)),
                                                        IndependentDegrees(:b => PoissonDegree(3.0))])
        sysd = edge_based(cm, diag)
        sold = solve_epidemic(sysd; initial = init, tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        for X in (:S_a, :S_b, :pop_I_a, :pop_R_b, :cumulative)
            @test maximum(abs.(curve(sys, sol0, X) .- curve(sysd, sold, X))) < 1e-10
        end
        # and at positive means it is the numeric mixture network
        sol1 = solve_epidemic(sys; init = merge(ic, Dict(k1 => 1.0, k2 => 3.0)), tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        crossn = MixtureDegree([0.5, 0.5], [PoissonDegree(1.0), PoissonDegree(3.0)])
        netn = MultitypeNetwork([:a, :b], [0.5, 0.5], [IndependentDegrees(:a => PoissonDegree(4.0), :b => crossn),
                                                        IndependentDegrees(:a => crossn, :b => PoissonDegree(3.0))])
        sysn = edge_based(cm, netn)
        soln = solve_epidemic(sysn; initial = init, tspan = (0.0, 60.0), saveat = 1.0, TOL...)
        @test maximum(abs.(curve(sys, sol1, :S_a) .- curve(sysn, soln, :S_a))) < 1e-10
    end

    @testset "M10: the unit law of unstructured stratification" begin
        # bimodal degrees (not Poisson type), unequal sizes, SEIR; seeds proportional to the sizes
        d = EmpiricalDegree(Dict(2 => 5 / 6, 10 => 1 / 6))
        base = ConfigurationNetwork(d)
        seir = seir_model(τ = 1 / 6, σ = 1 / 5, γ = 1 / 4)
        st = strata([:a, :b]; sizes = [0.3, 0.7])
        sys = edge_based(stratify(seir, st), unstructured(base, st))
        ref = edge_based(seir, base)
        sol = solve_epidemic(sys; initial = SeedFraction(:E_a => 0.003, :E_b => 0.007), tspan = (0.0, 150.0),
                             saveat = 1.0, TOL...)
        solr = solve_epidemic(ref; initial = SeedFraction(:E => 0.01), tspan = (0.0, 150.0), saveat = 1.0, TOL...)
        for b in (:a, :b), a in (:a, :b)
            @test maximum(abs.(curve(sys, sol, Symbol(:θ_, b, :_, a)) .- curve(ref, solr, :θ))) < 1e-10
            for X in (:E, :I, :R)
                @test maximum(abs.(curve(sys, sol, Symbol(:φ_, X, :_, b, :_, a)) .- curve(ref, solr, Symbol(:φ_, X)))) < 1e-10
            end
        end
        for (b, n) in ((:a, 0.3), (:b, 0.7)), X in (:E, :I, :R)
            @test maximum(abs.(curve(sys, sol, Symbol(:pop_, X, :_, b)) .- n .* curve(ref, solr, Symbol(:pop_, X)))) < 1e-10
        end
        @test maximum(abs.(curve(sys, sol, :S) .- curve(ref, solr, :S))) < 1e-10
        @test maximum(abs.(curve(sys, sol, :cumulative) .- curve(ref, solr, :cumulative))) < 1e-10
        # one stratum is literally the identity: the same field up to renaming
        one = strata([:a])
        sys1 = edge_based(stratify(seir, one), unstructured(base, one))
        rename = Dict(:θ_a_a => :θ, :φ_E_a => :φ_E, :φ_I_a => :φ_I, :φ_R_a => :φ_R)
        @test vector_fields_equal(symbolic_ode(sys1), symbolic_ode(ref); rename)
        @test Set(keys(sys1.variables)) == Set([:θ_a_a, :φ_E_a, :φ_I_a, :φ_R_a, :pop_E, :pop_I, :pop_R, :cumulative, :R])
    end

    @testset "§J.6: seeds are fractions of all nodes; exits in one stratum" begin
        st = strata([:y, :o]; sizes = [0.2, 0.8])
        net = sbm_network(st; mean_contacts = [6.0 2.0; 0.5 4.0])        # 0.2·2 = 0.8·0.5
        cm = stratify(sir_model(τ = 0.1, γ = 0.25), st)
        sys = edge_based(cm, net)
        init = SeedFraction(:I_y => 0.01)
        ic = default_initial_conditions(sys; initial = init)
        v = sys.variables
        @test ic[v[:pop_I_y]] == 0.01 && ic[v[:pop_I_o]] == 0.0
        @test ic[v[:φ_I_y_y]] ≈ 0.05 && ic[v[:φ_I_y_o]] ≈ 0.05                 # within-type 0.01/0.2
        sol = solve_epidemic(sys; initial = init, tspan = (0.0, 600.0), TOL...)
        @test curve(sys, sol, :S_y)[1] ≈ 0.19 atol = 1e-14
        @test curve(sys, sol, :S_o)[1] ≈ 0.8 atol = 1e-14
        @test curve(sys, sol, :cumulative)[end] ≈ final_size(cm, net, Dict{Symbol,Float64}(); initial = init) atol = 1e-8
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedFraction(:I_y => 0.3))   # > n_y
        @test_throws ArgumentError default_initial_conditions(sys; initial = SeedFraction(:I_y => 0.01, :S_y => 0.5))
        @test_throws ArgumentError default_initial_conditions(sys)          # no unique entry state
        # vaccination of the old only: ξ_S_o, V_o not infected, conservation
        vcm = ContactModel(:v; contacts = contacts(cm), transitions = vcat(node_transitions(cm), [NodeTransition(:S_o, :V_o, 0.01)]),
                           species = vcat(species_names(cm), [:V_o]),
                           labels = merge(species_labels(cm), Dict(:V_o => SpeciesLabel(:V, :o, 0, 0))))
        sysv = edge_based(vcm, net)
        @test haskey(sysv.variables, :ξ_S_o) && !haskey(sysv.variables, :ξ_S_y)
        solv = solve_epidemic(sysv; initial = init, tspan = (0.0, 200.0), saveat = 1.0, TOL...)
        node, edge = multitype_conservation(sysv, solv)
        @test node < 1e-10 && edge < 1e-10
        @test curve(sysv, solv, :cumulative)[end] ≈
              1 - curve(sysv, solv, :S_y)[end] - curve(sysv, solv, :S_o)[end] - curve(sysv, solv, :pop_V_o)[end] atol = 1e-10
    end

    @testset "node types are fixed" begin
        st = strata([:a, :b])
        net = sbm_network(st; mean_contacts = [3.0 1.0; 1.0 3.0])
        cm = stratify(sir_model(), st)
        move = ContactModel(:move; contacts = contacts(cm),
                            transitions = vcat(node_transitions(cm), [NodeTransition(:R_a, :R_b, 0.1)]),
                            species = species_names(cm), labels = species_labels(cm))
        @test_throws ArgumentError edge_based(move, net)
        @test_throws ArgumentError edge_based(cm, net; form = :compact)
        @test_throws AdmissibilityError edge_based(sir_model(), net)        # an unstratified model
    end
end
