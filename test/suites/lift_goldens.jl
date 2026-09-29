# WP17 acceptance 1: the per-reaction assembler reproduces every DiseaseProgression-representable
# Phase-0 golden (DESIGN §G.2 WP17; H14 "gated by the Phase-0 goldens to 1e-10"): SIR compact and
# expanded (Poisson(5), bimodal, symbolic κ), SEIR, the multistage progressions and the two-type
# multitype models. The Phase-0 goldens are the frozen outputs of the legacy 0.1 builders, written
# by test/golden/generate.jl at Vern9, reltol 1e-12, abstol 1e-14. WP29 regenerated the goldens of
# these areas for the 0.2 names and kept the 0.1 files in test/golden/<area>/v01/; they are read
# here, never rewritten.
#
# 1. Trajectories: every golden column that the assembled system has (renamed where the name
#    changed) matches to 1e-10 relative (|x − g| ≤ 1e-12 + 1e-10·max(|x|, |g|)), solved with the
#    golden's solver settings. Multitype node fractions are fractions of ALL nodes (design §J.6),
#    so the legacy per-type fractions are compared after dividing by the type size n = 1/2.
# 2. Right-hand sides: the uncompiled field `symbolic_ode(sys)` equals the equations of the legacy
#    builders. Until WP29 they were taken from the 0.1 builders themselves; WP29 deleted those, so
#    they are transcribed here independently (`msv_field`, `msv_field_multitype`: the expanded
#    Miller–Slim–Volz equations the 0.1 builders implemented, with the 0.1 within-type populations
#    and the seed factor q). With the rates and the mean degree κ as symbolic parameters the
#    difference is exactly 0 (constants folded, then expanded and simplified); for the numeric
#    golden builds (Float64 coefficients) vector_fields_equal decides (NetworkEpiCore's rule:
#    coefficients netted to 1e-12 relative, then seeded probes).

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using DelimitedFiles
using OrdinaryDiffEq: Vern9
using Test

const EBM = EdgeBasedModels
const GOLDEN = joinpath(pkgdir(EdgeBasedModels), "test", "golden")
const SOLVE = (solver = Vern9(), reltol = 1e-12, abstol = 1e-14, saveat = 1.0)

function golden_columns(area, case)
    data, header = readdlm(joinpath(GOLDEN, area, "v01", case * ".csv"), ',', Float64, '\n'; header = true)
    names = String.(vec(header))
    return data[:, 1], Dict(names[j] => data[:, j] for j in 2:length(names))
end

# The golden entry criterion at the WP17 tolerance.
function within(x, g; rtol = 1e-10, atol = 1e-12)
    length(x) == length(g) || return false
    return all(abs(a - b) <= atol + rtol * max(abs(a), abs(b)) for (a, b) in zip(x, g))
end
maxrel(x, g) = maximum(abs(a - b) / max(abs(a), abs(b), 1e-300) for (a, b) in zip(x, g))

# Compare `mapping` (golden column => (assembled key, scale)) over the golden's time grid.
function check_trajectories(sys, sol, t, cols, mapping)
    @test sol.t == t
    for (col, (key, scale)) in mapping
        x = compartment(sys, sol, key) ./ scale
        ok = within(x, cols[col])
        ok || @error "golden trajectory mismatch" col key maxrel = maxrel(x, cols[col])
        @test ok
    end
end

const tM = ModelingToolkit.t_nounits
_state(name) = only(@variables $(name)(tM))
_at(e, sub) = Symbolics.substitute(e, sub)
_sum(xs) = isempty(xs) ? 0 : sum(xs)

# The expanded equations of the 0.1 builder for a progression on the configuration network of the
# legacy PGF ψ, with the seed factor q (a symbolic parameter): θ̇ = −h, h = Σ_X τ_X φ_X; the edge
# partner leaves S at rate h ψ''(θ)/ψ'(θ) and so enters the entry state E at q h ψ''(θ)/ψ'(1);
# every φ_X loses τ_X φ_X (the partner transmits to the test node) and follows the transitions;
# pop_E gains the incidence q h ψ'(θ) and the populations follow the transitions.
function msv_field(prog::DiseaseProgression, pgf::DegreePGF, q)
    z = pgf.variable
    d1 = Symbolics.derivative(pgf.expression, z)
    d2 = Symbolics.derivative(d1, z)
    θ = _state(:θ)
    stages = [s.name for s in prog.stages]
    φ = Dict(X => _state(Symbol(:φ_, X)) for X in stages)
    pop = Dict(X => _state(Symbol(:pop_, X)) for X in stages)
    τ = Dict(s.name => s.transmission_rate for s in prog.stages)
    h = _sum([τ[X] * φ[X] for X in stages])
    ins(X, v) = _sum([tr.rate * v[tr.source] for tr in prog.transitions if tr.target === X])
    out(X) = _sum([tr.rate for tr in prog.transitions if tr.source === X])
    states = Any[θ]
    rhs = Any[-h]
    for X in stages
        entry = X === prog.entry
        push!(states, φ[X])
        push!(rhs, (entry ? q * h * _at(d2, Dict(z => θ)) / _at(d1, Dict(z => 1)) : 0) + ins(X, φ) - (τ[X] + out(X)) * φ[X])
    end
    for X in stages
        push!(states, pop[X])
        push!(rhs, (X === prog.entry ? q * h * _at(d1, Dict(z => θ)) : 0) + ins(X, pop) - out(X) * pop[X])
    end
    return SymbolicODE(:msv; states, rhs, parameters = :infer)
end

# The compact equations of the 0.1 builder for SIR (Miller 2011): θ̇ = −τθ + τ q ψ'(θ)/ψ'(1) + γ(1 − θ),
# Ṙ = γ(1 − qψ(θ) − R).
function msv_compact(τ, γ, pgf::DegreePGF, q)
    z = pgf.variable
    d1 = Symbolics.derivative(pgf.expression, z)
    θ, R = _state(:θ), _state(:pop_R)
    return SymbolicODE(:msv_compact; states = Any[θ, R],
                       rhs = Any[-τ * θ + τ * q * _at(d1, Dict(z => θ)) / _at(d1, Dict(z => 1)) + γ * (1 - θ),
                                 γ * (1 - q * _at(pgf.expression, Dict(z => θ)) - R)],
                       parameters = :infer)
end

# The expanded equations of the 0.1 multitype builder (within-type populations): θ_{b→a} is the
# argument x_b of ψ_a; h_{b→a} = Σ_X c(b, a) τ_X φ_{X,b→a} with the contact-matrix multiplier
# c(infector b, infectee a); θ̇_{b→a} = −h_{b→a}; the type-b partner of a type-a test node enters E at
# q_b Σ_k h_{k→b} ∂_a∂_kψ_b(θ_{·→b})/∂_aψ_b(1); pop_{E,a} gains q_a Σ_b h_{b→a} ∂_bψ_a(θ_{·→a}).
function msv_field_multitype(prog::DiseaseProgression, types, ψ::Dict, c, q::Dict)
    xs = Dict(a => only(@variables $(Symbol(:x_, a))) for a in types)
    θ = Dict((b, a) => _state(Symbol(:θ_, b, :_, a)) for b in types, a in types)
    stages = [s.name for s in prog.stages]
    φ = Dict((X, b, a) => _state(Symbol(:φ_, X, :_, b, :_, a)) for X in stages, b in types, a in types)
    pop = Dict((X, a) => _state(Symbol(:pop_, X, :_, a)) for X in stages, a in types)
    τ = Dict(s.name => s.transmission_rate for s in prog.stages)
    ψx(a) = ψ[a](xs)
    ∂(e, b) = Symbolics.derivative(e, xs[b])
    atθ(e, a) = _at(e, Dict(xs[b] => θ[(b, a)] for b in types))
    at1(e) = _at(e, Dict(xs[b] => 1 for b in types))
    h(b, a) = _sum([c(b, a) * τ[X] * φ[(X, b, a)] for X in stages])
    ins(X, f) = _sum([tr.rate * f(tr.source) for tr in prog.transitions if tr.target === X])
    out(X) = _sum([tr.rate for tr in prog.transitions if tr.source === X])
    states, rhs = Any[], Any[]
    for b in types, a in types
        push!(states, θ[(b, a)]); push!(rhs, -h(b, a))
    end
    for X in stages, b in types, a in types
        entry = X === prog.entry ?
            q[b] * _sum([h(k, b) * atθ(∂(∂(ψx(b), a), k), b) for k in types]) / at1(∂(ψx(b), a)) : 0
        push!(states, φ[(X, b, a)])
        push!(rhs, entry + ins(X, Y -> φ[(Y, b, a)]) - (c(b, a) * τ[X] + out(X)) * φ[(X, b, a)])
    end
    for X in stages, a in types
        inc = X === prog.entry ? q[a] * _sum([h(b, a) * atθ(∂(ψx(a), b), a) for b in types]) : 0
        push!(states, pop[(X, a)])
        push!(rhs, inc + ins(X, Y -> pop[(Y, a)]) - out(X) * pop[(X, a)])
    end
    return SymbolicODE(:msv_multitype; states, rhs, parameters = :infer)
end

# The assembled multitype field with pop_<Y>_a rescaled to within-type fractions (n_a = 1/2).
function within_type(A::SymbolicODE)
    ispop(x) = startswith(string(Symbolics.getname(x)), "pop_")
    scale = Dict{Any,Any}(x => 0.5 * x for x in A.states if ispop(x))
    return SymbolicODE(:assembled_rescaled; states = A.states,
                       rhs = Any[(ispop(x) ? 2 : 1) * Symbolics.substitute(f, scale) for (x, f) in zip(A.states, A.rhs)],
                       parameters = :infer)
end

# Expand (and simplify) until nothing changes: a sum of monomials, 0 when the difference is 0.
function _expand_fully(d)
    for _ in 1:10
        e = Symbolics.expand(Symbolics.simplify(Symbolics.expand(d)))
        v = Symbolics.value(e)
        (v isa Number || isequal(e, d)) && return v
        d = e
    end
    return Symbolics.value(d)
end

# Exact symbolic equality of two fields with the same state names.
function fields_symbolically_equal(a::SymbolicODE, b::SymbolicODE)
    na = [Symbol(Symbolics.getname(x)) for x in a.states]
    nb = [Symbol(Symbolics.getname(x)) for x in b.states]
    Set(na) == Set(nb) || return false
    for (i, n) in enumerate(na)
        j = findfirst(==(n), nb)
        d = Symbolics.substitute(Symbolics.wrap(a.rhs[i]) - Symbolics.wrap(b.rhs[j]), Dict{Any,Any}();
                                 fold = Val(true))
        d = _expand_fully(d)
        (d isa Number && iszero(d)) || (@error "symbolic difference" n d; return false)
    end
    return true
end

qparam(sys, s = :S) = sys.metadata[:q][s].param

const τ = 1 / 6
const γ = 1 / 4
const σ = 1 / 5
const ρ0 = 0.01
const P_BIMODAL = [k == 2 ? 5 / 6 : k == 10 ? 1 / 6 : 0.0 for k in 0:10]

# The untyped expanded columns: the legacy name (golden column and unknown) => the assembled key.
untyped_mapping(stages) = merge(
    Dict("S" => (:S, 1.0), "I" => (:I, 1.0), "θ" => (:θ, 1.0), "φ_S" => (:φ_S, 1.0),
         "edge_hazard" => (:edge_hazard, 1.0), "excess_hazard" => (:excess_hazard, 1.0)),
    Dict("φ_$X" => (Symbol(:φ_, X), 1.0) for X in stages),
    Dict("pop_$X" => (Symbol(:pop_, X), 1.0) for X in stages))

@testset "lift: the Phase-0 goldens (acceptance 1)" begin
    @testset "core: SIR expanded and compact" begin
        for (case, pgf) in (("sir_pois5", () -> poisson_pgf(5.0)), ("sir_bim", () -> polynomial_pgf(P_BIMODAL)))
            # expanded, through the factory (which now lowers through the assembler) and through
            # edge_based on the NetworkEpiCore distribution
            t, cols = golden_columns("core", case * "_expanded")
            d = case == "sir_pois5" ? PoissonDegree(5.0) : EmpiricalDegree(P_BIMODAL)
            for sys in (build_sir(pgf(), τ, γ), edge_based(sir_model(τ = τ, γ = γ), ConfigurationNetwork(d)))
                @test sys.metadata[:kind] === :assembled
                sol = solve_epidemic(sys; initial = SeedFraction(:I => ρ0), tspan = (0.0, 60.0), SOLVE...)
                check_trajectories(sys, sol, t, cols, merge(untyped_mapping([:I, :R]), Dict("R" => (:R, 1.0))))
            end
            # compact
            t, cols = golden_columns("core", case * "_compact")
            sysc = build_sir(pgf(), τ, γ; form = :compact)
            solc = solve_epidemic(sysc; initial = SeedFraction(:I => ρ0), tspan = (0.0, 60.0), SOLVE...)
            check_trajectories(sysc, solc, t, cols, Dict("S" => (:S, 1.0), "I" => (:I, 1.0), "R" => (:R, 1.0),
                                                        "θ" => (:θ, 1.0), "ψ_θ" => (:ψ_θ, 1.0)))
            # right-hand sides of the numeric builds: expanded and compact against the 0.1 equations
            for form in (:expanded, :compact)
                sys = build_sir(pgf(), τ, γ; form)
                A = symbolic_ode(sys)
                L = form === :expanded ? msv_field(EBM._legacy_sir_model(β = τ, γ = γ), pgf(), qparam(sys)) :
                    msv_compact(τ, γ, pgf(), qparam(sys))
                @test vector_fields_equal(A, L)
            end
        end
        # exact symbolic equality with symbolic rates and mean degree
        @parameters τs γs κs
        for form in (:expanded, :compact)
            sys = build_sir(poisson_pgf(κs), τs, γs; form)
            A = symbolic_ode(sys)
            L = form === :expanded ? msv_field(EBM._legacy_sir_model(β = τs, γ = γs), poisson_pgf(κs), qparam(sys)) :
                msv_compact(τs, γs, poisson_pgf(κs), qparam(sys))
            @test fields_symbolically_equal(A, L)
            @test vector_fields_equal(A, L)
        end
        # symbolic mean degree κ (= 5 at solve time) equals the numeric golden
        @parameters κ
        t, cols = golden_columns("core", "sir_pois5_symkappa_expanded")
        sys = build_sir(poisson_pgf(κ), τ, γ)
        ic = merge(default_initial_conditions(sys; initial = SeedFraction(:I => ρ0)), Dict(κ => 5.0))
        sol = solve_epidemic(sys; init = ic, tspan = (0.0, 60.0), SOLVE...)
        check_trajectories(sys, sol, t, cols, merge(untyped_mapping([:I, :R]), Dict("R" => (:R, 1.0))))
        @test vector_fields_equal(symbolic_ode(sys), msv_field(EBM._legacy_sir_model(β = τ, γ = γ), poisson_pgf(κ), qparam(sys)))
    end

    @testset "seir_multistage: SEIR, Erlang stages and heterogeneous infectivity" begin
        cases = [
            ("seir_pois5", () -> EBM._legacy_seir_model(σ = σ, β = τ, γ = γ), :E, 150, [:E, :I, :R]),
            ("sir_erlang3_pois5",
             () -> expand_erlang_stages([ErlangStage(:I, 3, γ; transmission_rate = τ), DiseaseStage(:R)],
                                        [DiseaseTransition(:I, :R, 3γ)]; entry = :I), :I_1, 60, [:I_1, :I_2, :I_3, :R]),
            ("seir_erlang_pois5",
             () -> expand_erlang_stages([ErlangStage(:E, 2, σ; transmission_rate = 0), ErlangStage(:I, 3, γ; transmission_rate = τ),
                                         DiseaseStage(:R)], [DiseaseTransition(:E, :I, 2σ), DiseaseTransition(:I, :R, 3γ)]; entry = :E),
             :E_1, 150, [:E_1, :E_2, :I_1, :I_2, :I_3, :R]),
            ("seir_twostage_pois5",
             () -> DiseaseProgression([DiseaseStage(:E; transmission_rate = 0), DiseaseStage(:I1; transmission_rate = τ),
                                       DiseaseStage(:I2; transmission_rate = τ / 2), DiseaseStage(:R; transmission_rate = 0)],
                                      [DiseaseTransition(:E, :I1, σ), DiseaseTransition(:I1, :I2, 2γ), DiseaseTransition(:I2, :R, 2γ)];
                                      entry = :E), :E, 150, [:E, :I1, :I2, :R]),
        ]
        for (case, prog, X, T, stages) in cases
            @testset "$case" begin
                t, cols = golden_columns("seir_multistage", case)
                sys = case == "seir_pois5" ? build_seir(poisson_pgf(5.0), σ, τ, γ) :
                      build_edge_system(StaticConfigurationModel(poisson_pgf(5.0), prog()); form = :expanded)
                @test sys.metadata[:kind] === :assembled && sys.metadata[:entry] === X
                sol = solve_epidemic(sys; initial = SeedFraction(X => ρ0), tspan = (0.0, Float64(T)), SOLVE...)
                check_trajectories(sys, sol, t, cols, merge(untyped_mapping(stages), Dict("R" => (:R, 1.0))))
                @test vector_fields_equal(symbolic_ode(sys), msv_field(prog(), poisson_pgf(5.0), qparam(sys)))
            end
        end
        # exact symbolic equality with symbolic rates and mean degree
        @parameters τs γs σs κs
        symbolic = [
            (EBM._legacy_seir_model(σ = σs, β = τs, γ = γs), [:E, :I, :R]),
            (expand_erlang_stages([ErlangStage(:I, 3, γs; transmission_rate = τs), DiseaseStage(:R)],
                                  [DiseaseTransition(:I, :R, 3γs)]; entry = :I), [:I_1, :I_2, :I_3, :R]),
            (DiseaseProgression([DiseaseStage(:E; transmission_rate = 0), DiseaseStage(:I1; transmission_rate = τs),
                                 DiseaseStage(:I2; transmission_rate = τs / 2), DiseaseStage(:R; transmission_rate = 0)],
                                [DiseaseTransition(:E, :I1, σs), DiseaseTransition(:I1, :I2, 2γs), DiseaseTransition(:I2, :R, 2γs)];
                                entry = :E), [:E, :I1, :I2, :R]),
        ]
        for (prog, stages) in symbolic
            sys = build_edge_system(StaticConfigurationModel(poisson_pgf(κs), prog))
            A = symbolic_ode(sys)
            L = msv_field(prog, poisson_pgf(κs), qparam(sys))
            @test fields_symbolically_equal(A, L)
            @test vector_fields_equal(A, L)
        end
    end

    @testset "multitype: two types, Poisson means [6 2; 2 4], equal sizes" begin
        # The legacy MultiTypeConfigurationModel had no type sizes and seeded ρ within every type;
        # the equivalent here is stratify on sbm_network(strata(sizes = [1/2, 1/2])) with
        # SeedFraction(:X_a => ρ/2, :X_b => ρ/2) (fractions of all nodes, design §J.6). Its
        # contact_matrix (infector, infectee) multiplier is the stratified contact rate.
        st = strata([:a, :b]; sizes = [0.5, 0.5])
        net = sbm_network(st; mean_contacts = [6.0 2.0; 2.0 4.0])
        τm = 0.0955
        sir = sir_model(τ = τm, γ = γ)
        seir = seir_model(τ = τm, σ = σ, γ = γ)
        cases = [("multitype_sir_2type", stratify(sir, st), :I, 60, [:I, :R]),
                 ("multitype_sir_2type_cm", stratify(sir, st; contact_rates = (a, b) -> a == b ? τm : τm / 2), :I, 60, [:I, :R]),
                 ("multitype_seir_2type", stratify(seir, st), :E, 150, [:E, :I, :R])]
        types = [:a, :b]
        for (case, cm, X, T, stages) in cases
            @testset "$case" begin
                t, cols = golden_columns("multitype", case)
                sys = edge_based(cm, net)
                @test sys.metadata[:closure] === :multitype
                sol = solve_epidemic(sys; initial = SeedFraction(Symbol(X, :_a) => ρ0 / 2, Symbol(X, :_b) => ρ0 / 2),
                                     tspan = (0.0, Float64(T)), SOLVE...)
                mapping = Dict{String,Tuple{Symbol,Float64}}()
                for b in types, a in types
                    mapping["θ_$(b)_$(a)"] = (Symbol(:θ_, b, :_, a), 1.0)            # partner b → test a
                    mapping["φ_S_$(b)_$(a)"] = (Symbol(:φ_S_, b, :_, a), 1.0)
                    mapping["edge_hazard_$(b)_$(a)"] = (Symbol(:edge_hazard_, b, :_, a), 1.0)
                    mapping["excess_hazard_$(b)_$(a)"] = (Symbol(:excess_hazard_, b, :_, a), 1.0)
                    for Y in stages
                        mapping["φ_$(Y)_$(b)_$(a)"] = (Symbol(:φ_, Y, :_, b, :_, a), 1.0)
                    end
                end
                for a in types
                    mapping["S_$a"] = (Symbol(:S_, a), 0.5)                            # all nodes → type a
                    for Y in stages
                        mapping["pop_$(Y)_$(a)"] = (Symbol(:pop_, Y, :_, a), 0.5)
                    end
                end
                check_trajectories(sys, sol, t, cols, mapping)
                # right-hand sides against the 0.1 multitype equations (within-type populations)
                prog = X === :I ? EBM._legacy_sir_model(β = τm, γ = γ) : EBM._legacy_seir_model(σ = σ, β = τm, γ = γ)
                means = Dict(:a => Dict(:a => 6.0, :b => 2.0), :b => Dict(:a => 2.0, :b => 4.0))
                ψ = Dict(a => (x -> exp(sum(means[a][b] * (x[b] - 1) for b in types))) for a in types)
                c = case == "multitype_sir_2type_cm" ? ((b, a) -> b == a ? 1.0 : 0.5) : ((b, a) -> 1.0)
                L = msv_field_multitype(prog, types, ψ, c, Dict(a => qparam(sys, Symbol(:S_, a)) for a in types))
                As = within_type(symbolic_ode(sys))
                @test vector_fields_equal(As, L)
            end
        end
        # exact symbolic equality with symbolic rates and means (reciprocity is not checked for
        # symbolic means; these are reciprocal for equal sizes when κab = κba)
        @parameters τs γs σs κaa κab κbb
        netS = MultitypeNetwork([:a, :b], [0.5, 0.5],
                                [IndependentDegrees(:a => PoissonDegree(κaa), :b => PoissonDegree(κab)),
                                 IndependentDegrees(:a => PoissonDegree(κab), :b => PoissonDegree(κbb))])
        for (cm, prog, stages) in ((stratify(sir_model(τ = τs, γ = γs), st), EBM._legacy_sir_model(β = τs, γ = γs), [:I, :R]),
                                   (stratify(seir_model(τ = τs, σ = σs, γ = γs), st),
                                    EBM._legacy_seir_model(σ = σs, β = τs, γ = γs), [:E, :I, :R]))
            sys = edge_based(cm, netS)
            meansS = Dict(:a => Dict(:a => κaa, :b => κab), :b => Dict(:a => κab, :b => κbb))
            ψS = Dict(a => (x -> exp(sum(meansS[a][b] * (x[b] - 1) for b in types))) for a in types)
            L = msv_field_multitype(prog, types, ψS, (b, a) -> 1, Dict(a => qparam(sys, Symbol(:S_, a)) for a in types))
            As = within_type(symbolic_ode(sys))
            @test fields_symbolically_equal(As, L)
            @test vector_fields_equal(As, L)
        end
    end
end
