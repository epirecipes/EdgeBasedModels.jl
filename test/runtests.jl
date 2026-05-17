using EdgeBasedModels
using ModelingToolkit
using Symbolics
using Test

import Catalyst

@testset "EdgeBasedModels" begin
    @testset "PGFs" begin
        pgf = polynomial_pgf([0.2, 0.3, 0.5])
        @test isequal(Symbolics.value(mean_degree(pgf)), 1.3)

        @parameters κ
        poisson = poisson_pgf(κ)
        d1 = pgf_derivative(poisson, 1)
        @test string(d1) == string(κ * exp(κ * (poisson.variable - 1)))

        # Second derivative
        d2 = pgf_derivative(poisson, 2)
        @test occursin("κ", string(d2))
    end

    @testset "Multivariate PGFs" begin
        @parameters κ_A κ_B

        # Multivariate Poisson
        pgf = multivariate_poisson_pgf([:A, :B], Dict(:A => κ_A, :B => κ_B))
        @test length(pgf.types) == 2
        @test pgf.types == [:A, :B]

        # Partial derivative contains κ_A
        d_A = partial_derivative(pgf, :A)
        @test occursin("κ_A", string(d_A))

        # Mixed partial contains both parameters
        d_AB = mixed_partial(pgf, :A, :B)
        @test occursin("κ_A", string(d_AB)) && occursin("κ_B", string(d_AB))

        # Mean degree: ⟨k_A⟩ = κ_A (after exp(0) cleanup)
        m_A = mean_degree(pgf, :A)
        @test isequal(m_A, κ_A)

        # Evaluation at symbolic point
        @variables θ_A θ_B
        val = eval_multivariate_pgf(pgf, Dict(:A => θ_A, :B => θ_B))
        @test occursin("θ_A", string(val))

        # Independent PGF from univariate Poissons
        pgf_a = poisson_pgf(κ_A; varname = :za)
        pgf_b = poisson_pgf(κ_B; varname = :zb)
        indep = independent_pgf(:A => pgf_a, :B => pgf_b)
        @test length(indep.types) == 2
        @test isequal(mean_degree(indep, :A), κ_A)
    end

    @testset "Catalyst progression adapter" begin
        @parameters γ
        rn = Catalyst.@reaction_network begin
            γ, I --> R
        end

        progression = progression_from_catalyst(
            rn;
            transmission_rates = Dict(:I => 1, :R => 0),
        )

        @test progression.entry == :I
        @test [stage.name for stage in progression.stages] == [:I, :R]
        @test length(progression.transitions) == 1
        @test progression.transitions[1].source == :I
        @test progression.transitions[1].target == :R
    end

    @testset "Disease model factories" begin
        @parameters β σ γ κ

        sir = sir_model(; β = β, γ = γ)
        @test sir.susceptible == :S
        @test sir.entry == :I
        @test [stage.name for stage in sir.stages] == [:I, :R]
        @test length(sir.transitions) == 1
        @test sir.transitions[1].source == :I
        @test sir.transitions[1].target == :R

        seir = seir_model(; σ = σ, β = β, γ = γ)
        @test seir.susceptible == :S
        @test seir.entry == :E
        @test [stage.name for stage in seir.stages] == [:E, :I, :R]
        @test length(seir.transitions) == 2
        @test seir.transitions[1].source == :E
        @test seir.transitions[1].target == :I
        @test seir.transitions[2].source == :I
        @test seir.transitions[2].target == :R

        sis = sis_model(; β = β, γ = γ)
        @test sis.susceptible == :S
        @test sis.entry == :I
        @test [stage.name for stage in sis.stages] == [:I]
        @test length(sis.transitions) == 1
        @test sis.transitions[1].source == :I
        @test sis.transitions[1].target == :S

        pgf = poisson_pgf(κ)
        built_sir = build_sir(pgf, β, γ; form = :expanded)
        factory_sir = build_edge_system(StaticConfigurationModel(pgf, sir); form = :expanded)
        @test keys(built_sir.variables) == keys(factory_sir.variables)
        @test keys(built_sir.observables) == keys(factory_sir.observables)
        @test length(ModelingToolkit.equations(built_sir.system)) == length(ModelingToolkit.equations(factory_sir.system))

        built_seir = build_seir(pgf, σ, β, γ; form = :expanded)
        factory_seir = build_edge_system(StaticConfigurationModel(pgf, seir); form = :expanded)
        @test keys(built_seir.variables) == keys(factory_seir.variables)
        @test keys(built_seir.observables) == keys(factory_seir.observables)
        @test length(ModelingToolkit.equations(built_seir.system)) == length(ModelingToolkit.equations(factory_seir.system))

        built_sis = build_sis(pgf, β, γ)
        factory_sis = build_edge_system(StaticConfigurationModel(pgf, sis))
        @test keys(built_sis.variables) == keys(factory_sis.variables)
        @test keys(built_sis.observables) == keys(factory_sis.observables)
        @test length(ModelingToolkit.equations(built_sis.system)) == length(ModelingToolkit.equations(factory_sis.system))
    end

    @testset "Expanded SIR builder" begin
        @parameters β γ κ
        model = build_sir(poisson_pgf(κ), β, γ; form = :expanded)
        eqs = ModelingToolkit.equations(model.system)

        @test length(eqs) >= 3
        @test haskey(model.observables, :S)
        @test haskey(model.observables, :I)
        @test haskey(model.observables, :edge_hazard)
        @test haskey(model.observables, :excess_hazard)
        @test haskey(model.variables, :θ)
        @test haskey(model.variables, :R)
    end

    @testset "Expanded SIR runs and matches compact" begin
        # Regression: prior to seeding φ_I from θ via the algebraic relation
        # φ_S = ψ'(θ)/ψ'(1), the expanded-form ICs left φ_I(0) = 0 and the
        # epidemic never started (θ stayed at 1 - ε). Now both forms must
        # agree on the final attack rate within numerical tolerance.
        using OrdinaryDiffEqDefault
        β_v, γ_v, κ_v = 0.10, 0.10, 5.0
        m_exp = build_sir(poisson_pgf(κ_v), β_v, γ_v; form = :expanded)
        m_cmp = build_sir(poisson_pgf(κ_v), β_v, γ_v; form = :compact)
        sol_exp = solve(ODEProblem(m_exp.system,
                                   default_initial_conditions(m_exp),
                                   (0.0, 200.0));
                        abstol = 1e-9, reltol = 1e-9)
        sol_cmp = solve(ODEProblem(m_cmp.system,
                                   default_initial_conditions(m_cmp),
                                   (0.0, 200.0));
                        abstol = 1e-9, reltol = 1e-9)
        R_exp = compartment(m_exp, sol_exp, :R)[end]
        R_cmp = compartment(m_cmp, sol_cmp, :R)[end]
        @test R_exp > 0.5                 # epidemic actually took off
        @test isapprox(R_exp, R_cmp; atol = 5e-3)
    end

    @testset "Compact SIR builder" begin
        @parameters β γ κ
        model = build_sir(poisson_pgf(κ), β, γ; form = :compact)
        eqs = ModelingToolkit.equations(model.system)

        @test length(eqs) == 2
        @test haskey(model.variables, :θ)
        @test haskey(model.variables, :R)
        @test haskey(model.observables, :S)
        @test haskey(model.observables, :I)
    end

    @testset "SEIR builder" begin
        @parameters σ β γ κ
        model = build_seir(poisson_pgf(κ), σ, β, γ)
        eqs = ModelingToolkit.equations(model.system)

        # Expanded SEIR now keeps stage-population variables in the compiled system.
        @test length(eqs) == 7
        @test haskey(model.variables, :θ)
        @test haskey(model.variables, :φ_E)
        @test haskey(model.variables, :φ_I)
        @test haskey(model.variables, :φ_R)
        @test haskey(model.variables, :R)
        @test haskey(model.observables, :S)
        @test haskey(model.observables, :I)
    end

    @testset "SIS builder" begin
        @parameters β γ κ
        model = build_sis(poisson_pgf(κ), β, γ)
        eqs = ModelingToolkit.equations(model.system)

        # SIS: just θ (1 ODE), S and I observed
        @test length(eqs) == 1
        @test haskey(model.variables, :θ)
        @test haskey(model.observables, :S)
        @test haskey(model.observables, :I)
    end

    @testset "Convenience wrappers" begin
        model = build_sir(poisson_pgf(5.0), 0.3, 0.1; form = :compact)
        ic = default_initial_conditions(model)
        manual = solve(ODEProblem(model.system, ic, (0.0, 20.0)); abstol = 1e-8, reltol = 1e-8)
        wrapped = solve_epidemic(model; tspan = (0.0, 20.0), init = ic, abstol = 1e-8, reltol = 1e-8)

        S = compartment(wrapped, model, :S)
        I = compartment(wrapped, model, :I)
        bundle = compartments(wrapped, model, [:S, :I, :R])

        @test length(S) == length(wrapped.t)
        @test length(I) == length(wrapped.t)
        @test haskey(bundle, :S)
        @test haskey(bundle, :I)
        @test haskey(bundle, :R)
        @test population_fraction(wrapped, model, :I) == I
        @test_throws ArgumentError compartment(wrapped, model, :X)
        @test isapprox(S[end], manual[model.observables[:S]][end]; atol = 1e-8)
        @test isapprox(I[end], manual[model.observables[:I]][end]; atol = 1e-8)

        ic_seed = default_initial_conditions(model; seed_fraction = 0.02)
        ic_eps = default_initial_conditions(model; ε = 0.02)
        @test ic_seed[model.variables[:θ]] ≈ 1.0
        @test ic_seed[model.variables[:R]] ≈ 0.0
        @test ic_seed == ic_eps
    end

    @testset "R₀ computation" begin
        @parameters β γ κ
        pgf = poisson_pgf(κ)

        # SIR R₀ = βκ/(β+γ)
        prog = DiseaseProgression(
            [DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
            [DiseaseTransition(:I, :R, γ)];
            entry = :I,
        )
        scm = StaticConfigurationModel(pgf, prog)
        R0 = basic_reproduction_number(scm)
        R0_str = string(Symbolics.simplify(R0))
        @test occursin("β", R0_str)
        @test occursin("κ", R0_str)
        @test occursin("γ", R0_str)

        R0_numeric = Symbolics.value(Symbolics.substitute(R0, Dict(β => 0.1, γ => 0.05, κ => 5.0)))
        @test R0_numeric ≈ 10.0 / 3.0 atol = 1e-10

        # SEIR R₀ should equal SIR R₀ (E stage is non-infectious)
        @parameters σ
        seir_prog = DiseaseProgression(
            [DiseaseStage(:E; transmission_rate = 0), DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R)],
            [DiseaseTransition(:E, :I, σ), DiseaseTransition(:I, :R, γ)];
            entry = :E,
        )
        R0_seir = basic_reproduction_number(StaticConfigurationModel(pgf, seir_prog))
        R0_seir_val = Symbolics.value(Symbolics.substitute(R0_seir, Dict(β => 0.1, γ => 0.05, σ => 0.2, κ => 5.0)))
        @test R0_seir_val ≈ 10.0 / 3.0 atol = 1e-10

        # Two-stage infectious: T = 1 - [γ₁/(β₁+γ₁)]·[γ₂/(β₂+γ₂)]
        @parameters β₁ β₂ γ₁ γ₂
        twostage = DiseaseProgression(
            [DiseaseStage(:I1; transmission_rate = β₁), DiseaseStage(:I2; transmission_rate = β₂), DiseaseStage(:R)],
            [DiseaseTransition(:I1, :I2, γ₁), DiseaseTransition(:I2, :R, γ₂)];
            entry = :I1,
        )
        R0_2 = basic_reproduction_number(StaticConfigurationModel(pgf, twostage))
        R0_2_val = Symbolics.value(Symbolics.substitute(R0_2, Dict(β₁ => 0.1, γ₁ => 0.5, β₂ => 0.2, γ₂ => 0.3, κ => 5.0)))
        expected_T = 1 - (0.5 / 0.6) * (0.3 / 0.5)
        @test R0_2_val ≈ expected_T * 5.0 atol = 1e-10
    end

    @testset "Multi-type SIR (2 types)" begin
        @parameters β γ κ_AA κ_AB κ_BA κ_BB

        pgf_A = multivariate_poisson_pgf([:A, :B], Dict(:A => κ_AA, :B => κ_AB))
        pgf_B = multivariate_poisson_pgf([:A, :B], Dict(:A => κ_BA, :B => κ_BB))

        progression = DiseaseProgression(
            [DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
            [DiseaseTransition(:I, :R, γ)];
            entry = :I,
        )

        model = MultiTypeConfigurationModel(
            types = [:A, :B],
            pgfs = Dict(:A => pgf_A, :B => pgf_B),
            progression = progression,
        )
        result = build_edge_system(model)
        eqs = ModelingToolkit.equations(result.system)

        # Multi-type systems now retain stage-population dynamics explicitly.
        @test length(eqs) == 16

        # Check θ variables for all type pairs
        for j in [:A, :B], l in [:A, :B]
            @test haskey(result.variables, Symbol("θ_", j, "_", l))
        end

        # Check φ variables for each stage and type pair
        for stage in [:I, :R], j in [:A, :B], l in [:A, :B]
            @test haskey(result.variables, Symbol("φ_", stage, "_", j, "_", l))
        end

        # Population-level variables per type
        @test haskey(result.variables, :R_A) && haskey(result.variables, :R_B)
        @test haskey(result.observables, :S_A) && haskey(result.observables, :S_B)
        @test haskey(result.observables, :I_A) && haskey(result.observables, :I_B)

        # Check cross-type edge hazards and excess hazards
        for j in [:A, :B], l in [:A, :B]
            @test haskey(result.observables, Symbol("edge_hazard_", j, "_", l))
            @test haskey(result.observables, Symbol("excess_hazard_", j, "_", l))
            @test haskey(result.observables, Symbol("φ_S_", j, "_", l))
        end

        # Default initial conditions should set all θ to 1
        ic = default_initial_conditions(result)
        @test length(ic) == 18
        theta_vars = [v for (k, v) in result.variables if startswith(string(k), "θ")]
        @test all(ic[v] ≈ 1.0 for v in theta_vars)
        @test ic[result.variables[:pop_I_A]] ≈ 1e-3
        @test ic[result.variables[:pop_I_B]] ≈ 1e-3
    end

    @testset "Multi-type SIR runs (φ-seeding regression)" begin
        # Regression: like the single-type expanded form, the multi-type
        # builder must seed φ_entry from the algebraic relation
        # φ_S = ∂ψ/∂x_l(θ) / ∂ψ/∂x_l(1). Without the seed, all φ_I(0) = 0,
        # all edge hazards vanish, and the epidemic never starts.
        using OrdinaryDiffEqDefault
        pgf_A = multivariate_poisson_pgf([:A, :B], Dict(:A => 4.0, :B => 1.0))
        pgf_B = multivariate_poisson_pgf([:A, :B], Dict(:A => 1.0, :B => 4.0))
        progression = DiseaseProgression(
            [DiseaseStage(:I; transmission_rate = 0.2), DiseaseStage(:R; transmission_rate = 0)],
            [DiseaseTransition(:I, :R, 0.1)]; entry = :I,
        )
        model = MultiTypeConfigurationModel(
            types = [:A, :B], pgfs = Dict(:A => pgf_A, :B => pgf_B),
            progression = progression,
        )
        result = build_edge_system(model)
        ic = default_initial_conditions(result)
        sol = solve(ODEProblem(result.system, ic, (0.0, 200.0));
                    abstol = 1e-9, reltol = 1e-9)
        @test sol.retcode == ReturnCode.Success
        # With β/γ=2 on degree-5 networks, the epidemic should infect a
        # substantial fraction of each type.
        R_A = sol[result.variables[:R_A]][end]
        R_B = sol[result.variables[:R_B]][end]
        @test R_A > 0.4
        @test R_B > 0.4
    end

    @testset "Multi-type SEIR (3 types)" begin
        @parameters σ β γ
        types = [:Y, :M, :O]

        pgf_Y = multivariate_poisson_pgf(types, Dict(:Y => 5, :M => 2, :O => 1))
        pgf_M = multivariate_poisson_pgf(types, Dict(:Y => 2, :M => 4, :O => 2))
        pgf_O = multivariate_poisson_pgf(types, Dict(:Y => 1, :M => 2, :O => 3))

        progression = DiseaseProgression(
            [DiseaseStage(:E; transmission_rate = 0), DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
            [DiseaseTransition(:E, :I, σ), DiseaseTransition(:I, :R, γ)];
            entry = :E,
        )

        model = MultiTypeConfigurationModel(
            types = types,
            pgfs = Dict(:Y => pgf_Y, :M => pgf_M, :O => pgf_O),
            progression = progression,
        )
        result = build_edge_system(model)
        eqs = ModelingToolkit.equations(result.system)

        @test length(eqs) == 45
        @test length(result.variables) == 48
    end

    @testset "Multi-type with contact matrix" begin
        @parameters β γ κ

        # Two types, assortative mixing (prefer same type)
        pgf_A = multivariate_poisson_pgf([:A, :B], Dict(:A => κ, :B => κ))
        pgf_B = multivariate_poisson_pgf([:A, :B], Dict(:A => κ, :B => κ))

        progression = DiseaseProgression(
            [DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
            [DiseaseTransition(:I, :R, γ)];
            entry = :I,
        )

        # Cross-type transmission at half rate
        model = MultiTypeConfigurationModel(
            types = [:A, :B],
            pgfs = Dict(:A => pgf_A, :B => pgf_B),
            progression = progression,
            contact_matrix = Dict((:A, :A) => 1, (:B, :B) => 1, (:A, :B) => Symbolics.Num(1) // 2, (:B, :A) => Symbolics.Num(1) // 2),
        )
        result = build_edge_system(model)
        eqs = ModelingToolkit.equations(result.system)
        @test length(eqs) == 16

        # θ equations for cross-type should have halved β
        eq_strs = [string(eq) for eq in eqs]
        # Verify the system built without error and has the expected structure
        @test haskey(result.variables, :θ_A_B)
        @test haskey(result.variables, :θ_B_A)
    end

    @testset "Dynamic network SIR" begin
        @parameters β γ κ η₁ η₂

        pgf = poisson_pgf(κ)
        progression = DiseaseProgression(
            [DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
            [DiseaseTransition(:I, :R, γ)];
            entry = :I,
        )

        model = DynamicConfigurationModel(pgf, progression, η₁, η₂)
        result = build_edge_system(model)
        eqs = ModelingToolkit.equations(result.system)

        # Volz-Meyers formulation: θ, P₁, P_S, M₁, pop_I, pop_R + 2 observables
        @test length(eqs) >= 6
        @test haskey(result.variables, :θ)
        @test haskey(result.variables, :P₁)
        @test haskey(result.variables, :P_S)
        @test haskey(result.variables, :M₁)
        @test haskey(result.variables, :R)
        @test haskey(result.observables, :S)
        @test haskey(result.observables, :I)

        # Verify η₂ (swap rate) appears in the equations
        eq_strs = join(string.(eqs), " ")
        @test occursin("η₂", eq_strs)
    end

    @testset "Dynamic network SEIR" begin
        @parameters σ β γ κ η₁ η₂

        # SEIR is not yet supported by the Volz-Meyers dynamic model
        @test_throws ArgumentError DynamicConfigurationModel(
            poisson_pgf(κ),
            DiseaseProgression(
                [DiseaseStage(:E; transmission_rate = 0), DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
                [DiseaseTransition(:E, :I, σ), DiseaseTransition(:I, :R, γ)];
                entry = :E,
            ),
            η₁,
            η₂,
        ) |> build_edge_system
    end

    @testset "Method of Stages" begin
        @testset "ErlangStage construction" begin
            es = ErlangStage(:I, 5, 0.1; transmission_rate = 0.5)
            @test es.name == :I
            @test es.n_substages == 5
            @test es.total_rate == 0.1
            @test es.transmission_rate == 0.5
        end

        @testset "GammaApproxStage" begin
            gs = GammaApproxStage(:I, 10.0, 0.3; transmission_rate = 0.5)
            # n = round(1/0.3²) = round(11.11) = 11
            @test gs isa ErlangStage
            @test gs.n_substages == 11
            @test gs.total_rate ≈ 1 / 10.0
            @test gs.transmission_rate == 0.5
        end

        @testset "expand_erlang_stages basics" begin
            @parameters γ_mos β_mos
            erlang_I = ErlangStage(:I, 3, γ_mos; transmission_rate = β_mos)
            prog = expand_erlang_stages(
                [erlang_I, DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, γ_mos)];
                entry = :I,
            )
            # 3 sub-stages of I + R = 4 stages total
            @test length(prog.stages) == 4
            @test prog.stages[1].name == :I_1
            @test prog.stages[2].name == :I_2
            @test prog.stages[3].name == :I_3
            @test prog.stages[4].name == :R
            @test prog.entry == :I_1
        end

        @testset "Sub-stage rate" begin
            n = 3
            γ_val = 0.3
            erlang_I = ErlangStage(:I, n, γ_val; transmission_rate = 0.5)
            prog = expand_erlang_stages(
                [erlang_I, DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, γ_val)];
                entry = :I,
            )
            # Internal chain transitions: I_1→I_2 and I_2→I_3 should have rate = n * γ
            chain_transitions = [tr for tr in prog.transitions if tr.source in (:I_1, :I_2) && tr.target in (:I_2, :I_3)]
            @test length(chain_transitions) == 2
            for tr in chain_transitions
                @test tr.rate ≈ n * γ_val  # 3 * 0.3 = 0.9
            end
        end

        @testset "Transmission inherited" begin
            @parameters β_inh
            erlang_I = ErlangStage(:I, 3, 0.5; transmission_rate = β_inh)
            prog = expand_erlang_stages(
                [erlang_I, DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, 0.5)];
                entry = :I,
            )
            # All I sub-stages should have the transmission rate
            for i in 1:3
                stage = prog.stages[i]
                @test stage.name == Symbol(:I, "_", i)
                @test isequal(stage.transmission_rate, β_inh)
            end
            # R should have zero transmission
            @test prog.stages[4].transmission_rate == 0
        end

        @testset "Erlang(1) = exponential" begin
            @parameters γ_e1 β_e1
            # Erlang with 1 sub-stage
            erlang1 = ErlangStage(:I, 1, γ_e1; transmission_rate = β_e1)
            prog_erlang = expand_erlang_stages(
                [erlang1, DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, γ_e1)];
                entry = :I,
            )
            # Should produce 2 stages: I_1 and R
            @test length(prog_erlang.stages) == 2
            @test prog_erlang.stages[1].name == :I_1
            # The transition from I_1 → R should have rate γ_e1 (1 * γ_e1)
            exit_tr = [tr for tr in prog_erlang.transitions if tr.source == :I_1 && tr.target == :R]
            @test length(exit_tr) == 1
            @test isequal(exit_tr[1].rate, γ_e1)
        end

        @testset "Model builds and solves" begin
            @parameters β_ms γ_ms κ_ms
            pgf = poisson_pgf(κ_ms)
            erlang_I = ErlangStage(:I, 3, γ_ms; transmission_rate = β_ms)
            prog = expand_erlang_stages(
                [erlang_I, DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, γ_ms)];
                entry = :I,
            )
            scm = StaticConfigurationModel(pgf, prog)
            result = build_edge_system(scm)
            eqs = ModelingToolkit.equations(result.system)
            @test length(eqs) == 9
            @test haskey(result.variables, :θ)
            @test haskey(result.variables, :R)
            @test haskey(result.observables, :S)
        end

        @testset "Same mean, different dynamics" begin
            @parameters κ_sd
            γ_val = 0.1
            β_val = 0.05
            κ_val = 10.0

            # Erlang(1, γ) — exponential
            erlang1 = ErlangStage(:I, 1, γ_val; transmission_rate = β_val)
            prog1 = expand_erlang_stages(
                [erlang1, DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, γ_val)];
                entry = :I,
            )
            scm1 = StaticConfigurationModel(poisson_pgf(κ_sd), prog1)
            r1 = build_edge_system(scm1; name = :erlang1)
            eqs1 = ModelingToolkit.equations(r1.system)

            # Erlang(5, 5γ) — sharper distribution, same mean
            erlang5 = ErlangStage(:I, 5, 5 * γ_val; transmission_rate = β_val)
            prog5 = expand_erlang_stages(
                [erlang5, DiseaseStage(:R)],
                [DiseaseTransition(:I, :R, 5 * γ_val)];
                entry = :I,
            )
            scm5 = StaticConfigurationModel(poisson_pgf(κ_sd), prog5)
            r5 = build_edge_system(scm5; name = :erlang5)
            eqs5 = ModelingToolkit.equations(r5.system)

            @test length(eqs1) == 5
            @test length(eqs5) == 13

            # Both models should build without error (sizes differ)
            @test length(eqs5) > length(eqs1)
        end

        @testset "SEIR with Erlang stages" begin
            @parameters σ_se β_se γ_se κ_se
            erlang_E = ErlangStage(:E, 2, σ_se; transmission_rate = 0)
            erlang_I = ErlangStage(:I, 3, γ_se; transmission_rate = β_se)
            prog = expand_erlang_stages(
                [erlang_E, erlang_I, DiseaseStage(:R)],
                [DiseaseTransition(:E, :I, σ_se), DiseaseTransition(:I, :R, γ_se)];
                entry = :E,
            )
            # E_1, E_2, I_1, I_2, I_3, R = 6 stages
            @test length(prog.stages) == 6
            @test prog.entry == :E_1

            scm = StaticConfigurationModel(poisson_pgf(κ_se), prog)
            result = build_edge_system(scm)
            eqs = ModelingToolkit.equations(result.system)
            @test length(eqs) == 13
            @test haskey(result.variables, :θ)
            @test haskey(result.variables, :R)
            @test haskey(result.observables, :S)
        end
    end

    @testset "Clustering" begin
        using OrdinaryDiffEqDefault

        _numval(x) = Float64(Symbolics.value(
            Symbolics.substitute(x, Dict(exp(Symbolics.Num(0.0)) => 1, exp(Symbolics.Num(0)) => 1))))

        @testset "ClusteredPGF construction" begin
            cpgf = clustered_poisson_pgf(3.0, 1.0)
            @test cpgf isa ClusteredPGF
            @test _numval(mean_single_degree(cpgf)) ≈ 3.0
            @test _numval(mean_triangle_degree(cpgf)) ≈ 1.0
        end

        @testset "Clustering coefficient" begin
            cpgf = clustered_poisson_pgf(3.0, 1.0)
            cc = _numval(clustering_coefficient(cpgf))
            @test 0.0 ≤ cc ≤ 1.0
            # C = 2t/(2t+s) = 2·1/(2·1+3) = 2/5 = 0.4
            @test cc ≈ 0.4 atol = 1e-10
        end

        @testset "Zero clustering = standard model" begin
            @parameters β γ
            # No triangle edges → should behave like standard model
            cpgf_zero = clustered_poisson_pgf(5.0, 0.0)
            @test _numval(clustering_coefficient(cpgf_zero)) ≈ 0.0 atol = 1e-10

            clustered_model = ClusteredConfigurationModel(
                cpgf_zero,
                DiseaseProgression(
                    [DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
                    [DiseaseTransition(:I, :R, γ)]; entry = :I),
            )
            R0_clustered = basic_reproduction_number(clustered_model)
            R0_val = _numval(Symbolics.substitute(R0_clustered, Dict(β => 0.1, γ => 0.05)))

            # Standard Poisson SIR: R₀ = β·κ/(β+γ) = 0.1·5/(0.15) = 10/3
            std_pgf = poisson_pgf(5.0)
            std_model = StaticConfigurationModel(
                std_pgf,
                DiseaseProgression(
                    [DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
                    [DiseaseTransition(:I, :R, γ)]; entry = :I),
            )
            R0_std = basic_reproduction_number(std_model)
            R0_std_val = _numval(Symbolics.substitute(R0_std, Dict(β => 0.1, γ => 0.05)))

            @test R0_val ≈ R0_std_val atol = 1e-8
        end

        @testset "Clustered SIR builds" begin
            @parameters β γ
            cpgf = clustered_poisson_pgf(3.0, 1.0)
            result = @test_nowarn build_clustered_sir(cpgf, β, γ)
            @test result isa EdgeModelSystem

            # Variables: θ₂, θ₃, φ2_I, φ2_R, φ3_I, φ3_R, R
            @test haskey(result.variables, :θ₂)
            @test haskey(result.variables, :θ₃)
            @test haskey(result.variables, :φ2_I)
            @test haskey(result.variables, :φ2_R)
            @test haskey(result.variables, :φ3_I)
            @test haskey(result.variables, :φ3_R)
            @test haskey(result.variables, :R)

            # Observables
            @test haskey(result.observables, :S)
            @test haskey(result.observables, :I)
            @test haskey(result.observables, :φ2_S)
            @test haskey(result.observables, :φ3_S)
        end

        @testset "Clustered SIR solves" begin
            cpgf = clustered_poisson_pgf(3.0, 1.0)
            model = build_clustered_sir(cpgf, 0.5, 0.1)
            ic = default_initial_conditions(model)
            prob = ODEProblem(model.system, ic, (0.0, 100.0))
            sol = solve(prob; abstol = 1e-8, reltol = 1e-8)

            @test sol.retcode == ReturnCode.Success

            # Extract final values — epidemic should complete
            S_final = sol[model.observables[:S]][end]
            I_final = sol[model.observables[:I]][end]
            R_final = sol[model.variables[:R]][end]

            @test 0.0 < S_final < 1.0
            @test I_final ≈ 0.0 atol = 1e-4     # epidemic should die out
            @test R_final > 0.0                   # some recovered
            @test isapprox(S_final + I_final + R_final, 1.0; atol = 1e-4)
            # Regression: φ-seeding must drive a real epidemic on both
            # single and triangle edges. Without seeding both φ2_I(0)
            # and φ3_I(0) from θ - φ_S, epidemic stalls and R_final ≈ ε.
            @test R_final > 0.1
        end

        @testset "Clustering reduces R₀" begin
            @parameters β γ
            # Same total mean degree = 5, but different clustering
            cpgf_low = clustered_poisson_pgf(4.5, 0.25)   # low clustering
            cpgf_high = clustered_poisson_pgf(3.0, 1.0)   # high clustering

            prog = DiseaseProgression(
                [DiseaseStage(:I; transmission_rate = β), DiseaseStage(:R; transmission_rate = 0)],
                [DiseaseTransition(:I, :R, γ)]; entry = :I)

            R0_low = basic_reproduction_number(ClusteredConfigurationModel(cpgf_low, prog))
            R0_high = basic_reproduction_number(ClusteredConfigurationModel(cpgf_high, prog))

            R0_low_val = _numval(Symbolics.substitute(R0_low, Dict(β => 0.1, γ => 0.05)))
            R0_high_val = _numval(Symbolics.substitute(R0_high, Dict(β => 0.1, γ => 0.05)))

            @test R0_low_val > R0_high_val
        end

        @testset "Clustered SEIR builds and solves" begin
            cpgf = clustered_poisson_pgf(3.0, 1.0)
            model = @test_nowarn build_clustered_seir(cpgf, 0.2, 0.5, 0.1)
            @test model isa EdgeModelSystem

            # SEIR has 3 stages (E, I, R) so more φ variables
            @test haskey(model.variables, :θ₂)
            @test haskey(model.variables, :θ₃)
            @test haskey(model.variables, :φ2_E)
            @test haskey(model.variables, :φ2_I)
            @test haskey(model.variables, :φ2_R)
            @test haskey(model.variables, :φ3_E)
            @test haskey(model.variables, :φ3_I)
            @test haskey(model.variables, :φ3_R)

            ic = default_initial_conditions(model)
            prob = ODEProblem(model.system, ic, (0.0, 100.0))
            sol = solve(prob; abstol = 1e-8, reltol = 1e-8)
            @test sol.retcode == ReturnCode.Success

            S_final = sol[model.observables[:S]][end]
            @test 0.0 < S_final < 1.0
        end

        @testset "Custom ClusteredPGF from coefficient matrix" begin
            # Simple bivariate distribution: p(0,0)=0.1, p(1,0)=0.3, p(0,1)=0.2, p(1,1)=0.4
            joint = [0.1 0.2; 0.3 0.4]
            cpgf = @test_nowarn clustered_pgf(joint)
            @test cpgf isa ClusteredPGF

            # mean single degree = 0·(0.1+0.2) + 1·(0.3+0.4) = 0.7
            @test _numval(mean_single_degree(cpgf)) ≈ 0.7 atol = 1e-10
            # mean triangle degree = 0·(0.1+0.3) + 1·(0.2+0.4) = 0.6
            @test _numval(mean_triangle_degree(cpgf)) ≈ 0.6 atol = 1e-10

            cc = _numval(clustering_coefficient(cpgf))
            @test 0.0 ≤ cc ≤ 1.0
            # C = 2·0.6/(2·0.6+0.7) = 1.2/1.9
            @test cc ≈ 1.2 / 1.9 atol = 1e-10

            # Should also build and solve an SIR model
            model = build_clustered_sir(cpgf, 0.5, 0.1)
            ic = default_initial_conditions(model)
            prob = ODEProblem(model.system, ic, (0.0, 100.0))
            sol = solve(prob; abstol = 1e-8, reltol = 1e-8)
            @test sol.retcode == ReturnCode.Success
        end
    end

    @testset "Degree Correlation" begin
        @testset "neutral_correlated_pgf" begin
            pk = [0.0, 0.2, 0.5, 0.3]  # degrees 0,1,2,3
            cpgf = neutral_correlated_pgf(pk)
            @test cpgf isa CorrelatedPGF
            @test cpgf.max_degree == 3
            # Every row of the mixing matrix must sum to 1
            for k in 1:size(cpgf.mixing_matrix, 1)
                @test sum(cpgf.mixing_matrix[k, :]) ≈ 1.0 atol = 1e-8
            end
        end

        @testset "assortative_correlated_pgf" begin
            pk = [0.0, 0.2, 0.5, 0.3]
            neutral = neutral_correlated_pgf(pk)
            r0_pgf = assortative_correlated_pgf(pk, 0.0)
            # r=0 should match neutral mixing matrix
            @test r0_pgf.mixing_matrix ≈ neutral.mixing_matrix atol = 1e-10

            # r=1 should be identity-like (diagonal dominant)
            r1_pgf = assortative_correlated_pgf(pk, 1.0)
            for k in 1:size(r1_pgf.mixing_matrix, 1)
                @test r1_pgf.mixing_matrix[k, k] ≈ 1.0 atol = 1e-8
            end
        end

        @testset "correlated_R0 neutral = standard" begin
            pk = [0.0, 0.2, 0.5, 0.3]
            T = 0.4
            cpgf = neutral_correlated_pgf(pk)
            R0_corr = correlated_R0(cpgf, T)

            # Standard R₀ = T·(⟨k²⟩-⟨k⟩)/⟨k⟩
            mean_k = sum((k - 1) * pk[k] for k in 1:length(pk))
            mean_k2 = sum((k - 1)^2 * pk[k] for k in 1:length(pk))
            R0_std = T * (mean_k2 - mean_k) / mean_k

            @test R0_corr ≈ R0_std atol = 1e-6
        end

        @testset "Assortativity range" begin
            pk = [0.0, 0.3, 0.4, 0.3]
            T = 0.5
            R0_neutral = correlated_R0(assortative_correlated_pgf(pk, 0.0), T)
            R0_assort = correlated_R0(assortative_correlated_pgf(pk, 1.0), T)
            @test isfinite(R0_neutral)
            @test isfinite(R0_assort)
            @test R0_neutral > 0
            @test R0_assort > 0
        end

        @testset "Poisson neutral" begin
            # For Poisson(κ), ⟨k²⟩-⟨k⟩ = κ², so R₀ = T·κ
            κ = 4.0
            T = 0.3
            # Approximate Poisson with truncated distribution
            max_k = 20
            pk = [exp(-κ) * κ^k / factorial(k) for k in 0:max_k]
            pk ./= sum(pk)  # renormalize after truncation
            cpgf = neutral_correlated_pgf(pk)
            R0_corr = correlated_R0(cpgf, T)
            @test R0_corr ≈ T * κ atol = 0.05
        end

        @testset "Row normalization" begin
            pk = [0.1, 0.3, 0.4, 0.2]
            for r in [0.0, 0.25, 0.5, 0.75, 1.0]
                cpgf = assortative_correlated_pgf(pk, r)
                for k in 1:size(cpgf.mixing_matrix, 1)
                    @test sum(cpgf.mixing_matrix[k, :]) ≈ 1.0 atol = 1e-8
                end
            end
        end
    end

    @testset "Multiplex Networks" begin
        using OrdinaryDiffEqDefault
        using LinearAlgebra: eigvals

        @testset "build_multiplex_sir" begin
            pgf1 = poisson_pgf(3.0)
            pgf2 = poisson_pgf(2.0)
            layers = [
                (:home, pgf1, 0.3, 0.1),
                (:work, pgf2, 0.2, 0.1),
            ]
            sys, u0, tspan, p = @test_nowarn build_multiplex_sir(layers)
            @test sys isa ODESystem
            @test tspan == (0.0, 100.0)
            @test length(ModelingToolkit.equations(sys)) == length(layers) + 1
        end

        @testset "Solves correctly" begin
            pgf1 = poisson_pgf(3.0)
            pgf2 = poisson_pgf(2.0)
            layers = [
                (:home, pgf1, 0.3, 0.1),
                (:work, pgf2, 0.2, 0.1),
            ]
            sys, u0, tspan, p = build_multiplex_sir(layers)
            prob = ODEProblem(sys, u0, tspan, p)
            sol = solve(prob; abstol = 1e-8, reltol = 1e-8)
            @test sol.retcode == ReturnCode.Success
            # All solution values should be finite
            @test all(isfinite, sol.u[end])
        end

        @testset "multiplex_R0" begin
            pgf1 = poisson_pgf(3.0)
            pgf2 = poisson_pgf(2.0)
            layers = [
                (:home, pgf1, 0.3, 0.1),
                (:work, pgf2, 0.2, 0.1),
            ]
            R0 = multiplex_R0(layers)
            # Manual: T₁·excess₁ + T₂·excess₂
            # Poisson(κ): excess = κ, T = β/(β+γ)
            T1 = 0.3 / (0.3 + 0.1)  # 0.75
            T2 = 0.2 / (0.2 + 0.1)  # 2/3
            expected = T1 * 3.0 + T2 * 2.0
            @test R0 ≈ expected atol = 1e-8
        end

        @testset "Single layer = standard" begin
            pgf = polynomial_pgf([0.0, 0.2, 0.5, 0.3])
            β, γ = 0.4, 0.1
            layers = [(:only, pgf, β, γ)]
            R0_mpx = multiplex_R0(layers)

            # Standard formula: T·(⟨k²⟩-⟨k⟩)/⟨k⟩
            pk = [0.0, 0.2, 0.5, 0.3]
            mean_k = sum((k - 1) * pk[k] for k in 1:length(pk))
            mean_k2 = sum((k - 1)^2 * pk[k] for k in 1:length(pk))
            T = β / (β + γ)
            R0_std = T * (mean_k2 - mean_k) / mean_k
            @test R0_mpx ≈ R0_std atol = 1e-8
        end

        @testset "Three layers" begin
            pgf1 = poisson_pgf(2.0)
            pgf2 = poisson_pgf(1.5)
            pgf3 = poisson_pgf(1.0)
            layers = [
                (:home, pgf1, 0.3, 0.1),
                (:work, pgf2, 0.2, 0.1),
                (:community, pgf3, 0.1, 0.1),
            ]
            sys, u0, tspan, p = @test_nowarn build_multiplex_sir(layers)
            @test length(ModelingToolkit.equations(sys)) == length(layers) + 1
            prob = ODEProblem(sys, u0, tspan, p)
            sol = solve(prob; abstol = 1e-8, reltol = 1e-8)
            @test sol.retcode == ReturnCode.Success
            R0 = multiplex_R0(layers)
            @test R0 > 0
            @test isfinite(R0)
        end

        @testset "susceptible_fraction" begin
            pgf1 = poisson_pgf(3.0)
            pgf2 = poisson_pgf(2.0)
            # At θ=1 (no infection), S should be 1
            S_init = susceptible_fraction([pgf1, pgf2], [1.0, 1.0])
            @test S_init ≈ 1.0 atol = 1e-8
            # At intermediate θ, S should be in (0,1)
            S_mid = susceptible_fraction([pgf1, pgf2], [0.8, 0.9])
            @test 0.0 < S_mid < 1.0
        end
    end

    @testset "Categorical composition" begin
        using OrdinaryDiffEqDefault

        # Numeric helper (reused from Clustering tests)
        _cat_numval(x) = Float64(Symbolics.value(
            Symbolics.substitute(x, Dict(exp(Symbolics.Num(0.0)) => 1,
                                         exp(Symbolics.Num(0)) => 1))))

        # ---- §1 OpenEBCM construction ----
        @testset "OpenEBCM auto-ports SIR" begin
            pgf = poisson_pgf(5.0)
            m = open_sir(pgf, 0.3, 0.1)

            @test m isa OpenEBCM
            @test m.name == :sir
            @test m.model isa StaticConfigurationModel

            # SIR → 3 ports: S (susceptible), I (infectious), R (recovered)
            @test length(m.ports) == 3
            types = [p.type for p in m.ports]
            @test :susceptible in types
            @test :infectious in types
            @test :recovered  in types

            names = [p.name for p in m.ports]
            @test :S in names
            @test :I in names
            @test :R in names
        end

        @testset "OpenEBCM auto-ports SEIR" begin
            pgf = poisson_pgf(5.0)
            m = open_seir(pgf, 0.2, 0.3, 0.1)

            @test m.name == :seir
            @test length(m.ports) == 4
            types = [p.type for p in m.ports]
            @test count(==(:susceptible), types) == 1
            @test count(==(:latent),      types) == 1
            @test count(==(:infectious),  types) == 1
            @test count(==(:recovered),   types) == 1
        end

        # ---- §2 tensor() — independent systems ----
        @testset "tensor product" begin
            pgf_a = poisson_pgf(5.0)
            pgf_b = poisson_pgf(3.0)
            m1 = open_sir(pgf_a, 0.3, 0.1; name = :pop_a)
            m2 = open_sir(pgf_b, 0.2, 0.1; name = :pop_b)

            tp = tensor(m1, m2)
            @test tp isa OpenEBCM
            # All ports from both systems preserved (3 + 3)
            @test length(tp.ports) == 6

            # Build the tensor system
            sys = build_edge_system(tp.model)
            @test sys isa EdgeModelSystem

            # Should have variables from both subsystems
            @test haskey(sys.variables, :θ_pop_a)
            @test haskey(sys.variables, :θ_pop_b)
            @test haskey(sys.variables, :R_pop_a)
            @test haskey(sys.variables, :R_pop_b)

            # Solve and verify independence:
            # each θ should settle to a value determined only by its own network
            ic = default_initial_conditions(sys)
            prob = ODEProblem(sys.system, ic, (0.0, 100.0))
            sol = solve(prob; abstol = 1e-8, reltol = 1e-8)
            @test sol.retcode == ReturnCode.Success

            # Solve standalone models for comparison
            sys_a = build_edge_system(m1.model)
            ic_a  = default_initial_conditions(sys_a)
            sol_a = solve(ODEProblem(sys_a.system, ic_a, (0.0, 100.0));
                          abstol = 1e-8, reltol = 1e-8)

            sys_b = build_edge_system(m2.model)
            ic_b  = default_initial_conditions(sys_b)
            sol_b = solve(ODEProblem(sys_b.system, ic_b, (0.0, 100.0));
                          abstol = 1e-8, reltol = 1e-8)

            # θ final values must match standalone systems
            θ_a_tensor = sol[sys.variables[:θ_pop_a]][end]
            θ_a_solo   = sol_a[sys_a.variables[:θ]][end]
            @test θ_a_tensor ≈ θ_a_solo atol = 1e-6

            θ_b_tensor = sol[sys.variables[:θ_pop_b]][end]
            θ_b_solo   = sol_b[sys_b.variables[:θ]][end]
            @test θ_b_tensor ≈ θ_b_solo atol = 1e-6
        end

        # ---- §3 compose() — coupled systems ----
        @testset "compose with coupling" begin
            pgf_a = poisson_pgf(5.0)
            pgf_b = poisson_pgf(3.0)
            m1 = open_sir(pgf_a, 0.3, 0.1; name = :city)
            m2 = open_sir(pgf_b, 0.2, 0.1; name = :rural)

            # Wire infectious from city to susceptible of rural
            cp = EdgeBasedModels.compose(m1, m2, [:I => :S])
            @test cp isa OpenEBCM

            # Ports consumed by wiring are removed
            wired_names = Set([:I, :S])
            for p in cp.ports
                # port names are prefixed, e.g. :city_S, :rural_I
                @test !(p.name in wired_names)
            end

            @test_throws ArgumentError build_edge_system(cp.model)
        end

        # ---- §4 stratify() ----
        @testset "stratify" begin
            pgf = poisson_pgf(5.0)
            base = open_sir(pgf, 0.3, 0.1; name = :base)

            # Two strata with assortative mixing
            mixing = [0.7 0.3;
                      0.3 0.7]
            strat = stratify(base, [:young, :old], mixing)
            @test strat isa OpenEBCM

            # Should have ports for both strata
            @test length(strat.ports) > length(base.ports)

            # Build and verify it produces a multi-type system
            sys = build_edge_system(strat.model)
            @test sys isa EdgeModelSystem

            neqs = length(ModelingToolkit.equations(sys.system))
            @test neqs == 16

            # Solve
            ic = default_initial_conditions(sys)
            prob = ODEProblem(sys.system, ic, (0.0, 100.0))
            sol = solve(prob; abstol = 1e-8, reltol = 1e-8)
            @test sol.retcode == ReturnCode.Success
        end

        # ---- §5 to_mass_action ----
        @testset "to_mass_action" begin
            # Symbolic test
            @parameters β_cat γ_cat κ_cat
            pgf_sym = poisson_pgf(κ_cat)
            prog_sym = DiseaseProgression(
                [DiseaseStage(:I; transmission_rate = β_cat),
                 DiseaseStage(:R; transmission_rate = 0)],
                [DiseaseTransition(:I, :R, γ_cat)]; entry = :I)
            ma_sym = to_mass_action(StaticConfigurationModel(pgf_sym, prog_sym))
            @test occursin("β_cat", string(ma_sym.β_eff))
            @test occursin("κ_cat", string(ma_sym.β_eff))

            # Numeric test: Poisson(5), β=0.3, γ=0.1
            # β_eff = β · ⟨k⟩ = 0.3 · 5 = 1.5
            pgf_num = poisson_pgf(5.0)
            prog_num = DiseaseProgression(
                [DiseaseStage(:I; transmission_rate = 0.3),
                 DiseaseStage(:R; transmission_rate = 0)],
                [DiseaseTransition(:I, :R, 0.1)]; entry = :I)
            ma_num = to_mass_action(StaticConfigurationModel(pgf_num, prog_num))
            @test _cat_numval(ma_num.β_eff) ≈ 1.5 atol = 1e-10
            @test _cat_numval(ma_num.γ) ≈ 0.1 atol = 1e-10

            # Non-Poisson network: β_eff should use the excess degree ratio ψ''(1)/ψ'(1).
            pgf_nonpoisson = polynomial_pgf([0.0, 0.5, 0.0, 0.5])  # degrees 1 and 3
            prog_nonpoisson = DiseaseProgression(
                [DiseaseStage(:I; transmission_rate = 0.3),
                 DiseaseStage(:R; transmission_rate = 0)],
                [DiseaseTransition(:I, :R, 0.1)]; entry = :I)
            ma_nonpoisson = to_mass_action(StaticConfigurationModel(pgf_nonpoisson, prog_nonpoisson))
            @test _cat_numval(ma_nonpoisson.β_eff) ≈ 0.45 atol = 1e-10
        end

        # ---- §6 EBCMFunctor ----
        @testset "EBCMFunctor" begin
            F = EBCMFunctor(:F)
            pgf = poisson_pgf(5.0)
            m = open_sir(pgf, 0.3, 0.1)

            sys = F(m)
            @test sys isa EdgeModelSystem
            @test haskey(sys.variables, :θ)
            @test haskey(sys.observables, :S)

            # Should be solvable
            ic = default_initial_conditions(sys)
            prob = ODEProblem(sys.system, ic, (0.0, 100.0))
            sol = solve(prob; abstol = 1e-8, reltol = 1e-8)
            @test sol.retcode == ReturnCode.Success
            @test 0.0 < sol[sys.observables[:S]][end] < 1.0
        end

        # ---- §7 verify_functoriality ----
        @testset "verify_functoriality" begin
            pgf_a = poisson_pgf(5.0)
            pgf_b = poisson_pgf(3.0)
            m1 = open_sir(pgf_a, 0.3, 0.1; name = :fa)
            m2 = open_sir(pgf_b, 0.2, 0.1; name = :fb)

            # Tensor product: F(m1 ⊗ m2) components should match F(m1), F(m2)
            result = verify_functoriality(m1, m2, Pair{Symbol,Symbol}[];
                                           tspan = (0.0, 100.0), atol = 1e-4)
            @test result.composed_retcode == ReturnCode.Success
            @test all(rc == ReturnCode.Success for rc in result.individual_retcodes)
            @test result.is_functorial
            @test result.max_difference < 1e-4
        end

        # ---- §8 compare_models ----
        @testset "compare_models" begin
            pgf = poisson_pgf(5.0)
            prog = DiseaseProgression(
                [DiseaseStage(:I; transmission_rate = 0.3),
                 DiseaseStage(:R; transmission_rate = 0)],
                [DiseaseTransition(:I, :R, 0.1)]; entry = :I)
            model = StaticConfigurationModel(pgf, prog)

            result = compare_models(model; tspan = (0.0, 80.0))
            @test result.ebcm.retcode == ReturnCode.Success
            @test result.mass_action.retcode == ReturnCode.Success
            @test result.β_eff ≈ 1.5 atol = 1e-10
            @test result.γ ≈ 0.1 atol = 1e-10

            # Access solutions via proper symbolic variables
            S_ebcm = result.ebcm[result.ebcm_system.observables[:S]][end]
            S_ma   = result.mass_action[result.ma_vars.S][end]
            # R₀ ≈ 3.75 → both models should show a substantial epidemic
            @test S_ebcm < 0.5
            @test S_ma   < 0.5
        end

        # ---- §9 NaturalTransformation metadata ----
        @testset "NaturalTransformation" begin
            nt = NaturalTransformation(
                :ebcm_to_mass_action,
                StaticConfigurationModel,
                Nothing,  # mass-action has no dedicated type in this package
                "EBCM → mass-action; valid when network is Poisson")
            @test nt.name == :ebcm_to_mass_action
            @test nt.source_type == StaticConfigurationModel
        end
    end

    # ===== Analytics: final_size, epidemic_probability, confidence_bands =====
    @testset "Analytics on configuration model" begin
        pgf  = poisson_pgf(5.0)
        prog = sir_model(β = 0.3, γ = 0.1)        # R₀ = 0.3/0.4 · 5 = 3.75
        model = StaticConfigurationModel(pgf, prog)

        # final_size
        fs = final_size(model)
        @test 0.7 < fs.R_infinity < 1.0
        @test 0.0 < fs.θ_infinity < 1.0

        # sub-threshold case
        prog_sub = sir_model(β = 0.01, γ = 1.0)   # R₀ ≪ 1
        sub_fs = final_size(StaticConfigurationModel(pgf, prog_sub))
        @test sub_fs.R_infinity == 0.0
        @test sub_fs.θ_infinity == 1.0

        # epidemic_probability
        pep = epidemic_probability(model)
        @test 0.5 < pep < 1.0
        # sub-threshold returns 0
        @test epidemic_probability(StaticConfigurationModel(pgf, prog_sub)) == 0.0

        # confidence_bands: lower < mean < upper, std_error positive
        cb = confidence_bands(model, 1_000)
        @test cb.lower <= cb.mean <= cb.upper
        @test cb.std_error > 0.0
        @test 0.0 <= cb.lower && cb.upper <= 1.0
        # near-zero epidemic returns all-zero bands
        cb0 = confidence_bands(StaticConfigurationModel(pgf, prog_sub), 1_000)
        @test cb0.mean == 0.0 && cb0.std_error == 0.0

        # Empty infectious stages now throws (regression)
        empty_prog = DiseaseProgression(
            [DiseaseStage(:R; transmission_rate = 0)],
            DiseaseTransition[]; entry = :R)
        @test_throws ArgumentError final_size(StaticConfigurationModel(pgf, empty_prog))
    end

    @testset "disease_free_equilibrium" begin
        @parameters β γ
        pgf = poisson_pgf(5.0)
        model = StaticConfigurationModel(pgf, sir_model(β = β, γ = γ))
        dfe = disease_free_equilibrium(model)
        @test dfe[:S] == 1.0 && dfe[:θ] == 1.0
        @test dfe[:I] == 0.0 && dfe[:R] == 0.0
        @test dfe[Symbol("φ_I")] == 0.0
    end

    @testset "sirs_model factory" begin
        @parameters β γ ε
        prog = sirs_model(β = β, γ = γ, ε = ε)
        stage_names = [s.name for s in prog.stages]
        @test :I in stage_names
        @test :R in stage_names
        @test any(tr -> tr.source == :I && tr.target == :R, prog.transitions)
        @test any(tr -> tr.source == :R && tr.target == :S, prog.transitions)
        # build_edge_system does not yet support re-susceptibilisation; the factory
        # itself succeeds, which is what API parity with NodeBasedModels requires.
        @test_throws KeyError build_edge_system(StaticConfigurationModel(poisson_pgf(4.0), prog))
    end

    @testset "basic_reproduction_number compatibility overloads" begin
        # CorrelatedPGF overload
        cpgf = neutral_correlated_pgf([0.0, 0.5, 0.5])
        @test basic_reproduction_number(cpgf, 0.5) == correlated_R0(cpgf, 0.5)

        # Multiplex tuple overload
        layers = [
            (:home, poisson_pgf(3.0), 0.2, 0.1),
            (:work, poisson_pgf(8.0), 0.1, 0.1),
        ]
        @test basic_reproduction_number(layers) ≈ multiplex_R0(layers)
    end

    @testset "epidemic_threshold (analytic, no Nemo)" begin
        # SIR on Poisson(5): κ = 5, threshold β_c = γ/(κ-1) = 0.1/4 = 0.025
        pgf = poisson_pgf(5.0)
        model = StaticConfigurationModel(pgf, sir_model(β = 0.1, γ = 0.1))
        β_c = epidemic_threshold(model)
        @test β_c ≈ 0.1 / 4 atol = 1e-12

        # Sub-critical network (κ ≤ 1) raises
        sparse = StaticConfigurationModel(poisson_pgf(0.5), sir_model(β = 0.1, γ = 0.1))
        @test_throws ArgumentError epidemic_threshold(sparse)

        # Symbolic single-stage SEIR returns a symbolic expression that satisfies
        # R₀ = 1 when β is substituted with β_c.
        @parameters β σ γ
        seir = StaticConfigurationModel(pgf, seir_model(β = β, σ = σ, γ = γ))
        β_c_sym = epidemic_threshold(seir)
        R0_sym = basic_reproduction_number(seir)
        R0_at_threshold = Symbolics.substitute(R0_sym, Dict(β => β_c_sym))
        @test isequal(Symbolics.simplify(R0_at_threshold - 1), 0)
    end

    @testset "generate_* / build_* parity aliases" begin
        # Functional aliases
        @test generate_sir === build_sir
        @test generate_sis === build_sis
        @test generate_seir === build_seir
        # generate_edge_system actually builds (use @parameters to avoid Symbol-arith)
        @parameters β γ
        m1 = build_edge_system(StaticConfigurationModel(poisson_pgf(5.0), sir_model(β = β, γ = γ)))
        m2 = generate_edge_system(StaticConfigurationModel(poisson_pgf(5.0), sir_model(β = β, γ = γ)))
        @test typeof(m1) === typeof(m2)
    end

    @testset "edge_*_model disambiguating aliases" begin
        @test edge_sir_model === sir_model
        @test edge_sis_model === sis_model
        @test edge_seir_model === seir_model
        @test edge_sirs_model === sirs_model
    end

    @testset "Catalyst bimolecular transmission" begin
        # SIR via S + I → 2I (β) and I → R (γ) — fully Catalyst-defined.
        rn = Catalyst.@reaction_network begin
            β, S + I --> 2I
            γ, I --> R
        end
        prog = progression_from_catalyst(rn; susceptible = :S, entry = :I)
        β_idx = findfirst(s -> s.name == :I, prog.stages)
        @test β_idx !== nothing
        # Transmission rate should have been inferred from the bimolecular reaction
        # (i.e., it's symbolic rather than the numeric 0 default).
        rate = prog.stages[β_idx].transmission_rate
        @test !(rate isa Number)
        @test :β in nameof.(Symbolics.get_variables(rate))
        # Progression I → R recorded
        @test any(tr -> tr.source == :I && tr.target == :R, prog.transitions)
        # Bimolecular reaction without susceptible should throw
        rn_bad = Catalyst.@reaction_network begin
            β, I + R --> 2I
        end
        @test_throws ArgumentError progression_from_catalyst(rn_bad; susceptible = :S, entry = :I)
    end

    @testset "Reinfection counting (Keeling et al. 2016, Approx. 1)" begin
        @testset "Structural lift of DiseaseProgression" begin
            sis = sis_model()  # S → I → S
            lifted = with_reinfection_counting(sis, 0)
            @test lifted.susceptible == :S_0
            stage_names = sort([s.name for s in lifted.stages])
            @test stage_names == [:I_0]
            @test lifted.entry == :I_0

            lifted3 = with_reinfection_counting(sis, 3)
            @test lifted3.susceptible == :S_0
            stage_names3 = sort([s.name for s in lifted3.stages])
            # S_1, S_2, S_3, I_1, I_2, I_3 (S_0 is implicit susceptible)
            @test stage_names3 == [:I_1, :I_2, :I_3, :S_1, :S_2, :S_3]
            @test lifted3.entry == :I_1
            # I_p → S_p recovery transitions, p = 1..3
            recoveries = [(tr.source, tr.target) for tr in lifted3.transitions]
            @test (:I_1, :S_1) in recoveries
            @test (:I_2, :S_2) in recoveries
            @test (:I_3, :S_3) in recoveries
        end

        @testset "Structural lift of SIRS" begin
            sirs = sirs_model()  # S → I → R → S
            lifted = with_reinfection_counting(sirs, 2)
            stage_names = sort([s.name for s in lifted.stages])
            # Non-susceptible stages: I_1, I_2, R_1, R_2, S_1, S_2
            @test stage_names == [:I_1, :I_2, :R_1, :R_2, :S_1, :S_2]
            transitions = [(tr.source, tr.target) for tr in lifted.transitions]
            # Recovery I_p → R_p preserves p
            @test (:I_1, :R_1) in transitions
            @test (:I_2, :R_2) in transitions
            # Waning R_p → S_p preserves p
            @test (:R_1, :S_1) in transitions
            @test (:R_2, :S_2) in transitions
        end

        @testset "build_sis_reinfection: edge variables and initialization (L=0)" begin
            β, γ = 0.5, 1.0
            pgf = poisson_pgf(5.0)
            tspan = (0.0, 30.0)

            sys_r = build_sis_reinfection(pgf, β, γ, 0)
            ic_r  = default_initial_conditions(sys_r; ε = 1e-2)
            sol_r = solve_epidemic(sys_r; tspan = tspan, init = ic_r,
                                   abstol = 1e-9, reltol = 1e-9, saveat = 0.5)

            @test haskey(sys_r.variables, :edge_S_0_I_0)
            S0 = 1 - 1e-2
            I0 = 1e-2
            @test ic_r[sys_r.variables[:S_0]] ≈ S0 atol = 1e-12
            @test ic_r[sys_r.variables[:I_0]] ≈ I0 atol = 1e-12
            @test ic_r[sys_r.variables[:edge_S_0_I_0]] ≈ 5.0 * S0 * I0 atol = 1e-12

            totals = reinfection_totals(sys_r, sol_r)
            @test all(abs.(totals[:S] .+ totals[:I] .- 1.0) .< 1e-8)
        end

        @testset "build_sis_reinfection: edge-stratified aggregate differs from scalar SIS (L=3)" begin
            β, γ = 0.5, 1.0
            pgf = poisson_pgf(5.0)
            tspan = (0.0, 50.0)

            sys_std = build_sis(pgf, β, γ)
            ic_std  = default_initial_conditions(sys_std; ε = 1e-2)
            sol_std = solve_epidemic(sys_std; tspan = tspan, init = ic_std,
                                     abstol = 1e-9, reltol = 1e-9, saveat = 0.5)

            sys_r = build_sis_reinfection(pgf, β, γ, 3)
            ic_r  = default_initial_conditions(sys_r; ε = 1e-2)
            sol_r = solve_epidemic(sys_r; tspan = tspan, init = ic_r,
                                   abstol = 1e-9, reltol = 1e-9, saveat = 0.5)

            S_std = compartment(sol_std, sys_std, :S)
            I_std = compartment(sol_std, sys_std, :I)
            S_r   = compartment(sol_r, sys_r, :S)

            totals = reinfection_totals(sys_r, sol_r)
            @test haskey(sys_r.variables, :edge_S_0_I_1)
            @test haskey(sys_r.variables, :edge_S_2_I_3)
            @test maximum(abs.(totals[:I] .- I_std)) > 0.05
            # Stratum sums equal observable S, I
            @test maximum(abs.(totals[:S] .- S_r)) < 1e-7
            @test all(abs.(totals[:S] .+ totals[:I] .- 1.0) .< 1e-8)
        end

        @testset "build_sis_reinfection: conservation and saturation" begin
            β, γ = 0.5, 1.0
            pgf = poisson_pgf(5.0)
            sys_r = build_sis_reinfection(pgf, β, γ, 4)
            ic_r  = default_initial_conditions(sys_r; ε = 1e-2)
            sol_r = solve_epidemic(sys_r; tspan = (0.0, 100.0), init = ic_r,
                                   abstol = 1e-9, reltol = 1e-9, saveat = 1.0)
            totals = reinfection_totals(sys_r, sol_r)
            # Total node mass conserved.
            @test all(abs.(totals[:S] .+ totals[:I] .- 1.0) .< 1e-8)
            # At long times, mass concentrates in the saturated bucket p = L.
            S_L = sol_r[sys_r.variables[:S_4]][end]
            I_L = sol_r[sys_r.variables[:I_4]][end]
            @test S_L + I_L > 0.95
            # Initial: all susceptibles in S_0 (= ψ(θ(0))).
            ψθ0 = sol_r[sys_r.observables[:S]][1]
            @test sol_r[sys_r.variables[:S_0]][1] ≈ ψθ0 atol = 1e-10
            for p in 1:4
                @test sol_r[sys_r.variables[Symbol("S_", p)]][1] == 0.0
            end
        end

        @testset "build_sis_reinfection: L = 1 distinguishes never- vs ever-infected" begin
            # The defining feature of reinfection counting: at L = 1 we can
            # read off the fraction of nodes that have ever been infected as
            # S_1 + I_1 = 1 - S_0.
            β, γ = 0.4, 1.0
            sys = build_sis_reinfection(poisson_pgf(5.0), β, γ, 1)
            ic  = default_initial_conditions(sys; ε = 1e-3)
            sol = solve_epidemic(sys; tspan = (0.0, 50.0), init = ic,
                                 abstol = 1e-9, reltol = 1e-9, saveat = 1.0)
            S_0 = sol[sys.variables[:S_0]]
            S_1 = sol[sys.variables[:S_1]]
            I_1 = sol[sys.variables[:I_1]]
            # Ever-infected fraction is monotone non-decreasing.
            ever = S_1 .+ I_1
            @test all(diff(ever) .>= -1e-10)
            # And equals 1 - S_0.
            @test maximum(abs.(ever .- (1.0 .- S_0))) < 1e-10
        end

        @testset "Lifted-name helpers" begin
            @test base_compartment_of(:S_3) == :S
            @test base_compartment_of(:I_12) == :I
            @test base_compartment_of(:θ) == :θ
            @test infection_count_of(:S_3) == 3
        end
    end

    if Base.find_package("NetworkOutbreaks") === nothing
        @info "Skipping NetworkOutbreaks integration tests; NetworkOutbreaks is not available"
    else
        @testset "NetworkOutbreaks integration" begin
            using NetworkOutbreaks
            using Graphs
            using StableRNGs
            using Statistics: mean

            # Adapter dispatch is provided by the package extension that loads
            # when both NetworkOutbreaks and EdgeBasedModels are present.
            prog = sir_model()
            params = Dict(:β => 1.5, :γ => 1.0)
            model = OutbreakModel(prog, params)
            @test :S in model.compartments
            @test :I in model.compartments
            @test :R in model.compartments
            @test any(t -> t.from == :S && t.to == :I && t.type == :infection,
                      model.transitions)

            # Run a small ensemble on a regular graph and check final size sanity.
            g = random_regular_graph(400, 6; rng = StableRNG(7))
            spec = OutbreakSpec(model = model, network = g,
                                initial = SeedFraction(:I => 0.05),
                                tspan = (0.0, 60.0))
            ens = simulate_ensemble(spec; nsims = 8, seed = 123)
            fs = mean(NetworkOutbreaks.final_size(t; recovered = :R) for t in ens.trajectories)
            @test 0.10 < fs <= 1.0
        end
    end
end

include("test_eon_crossval.jl")
