# WP17 acceptance 2 (H1) and the composition laws of the per-reaction lift (DESIGN §D.3, §D.6):
#
# - H1: symbolic_ode(edge_based(glue(A, B), net)) equals sum_contributions of the parts'
#   lift_contributions (the EB lift is strict under gluing; Lean NEP.lift_glue), with exits,
#   namespaced gluings (pushforward along the inclusions), on WellMixed and on MultitypeNetwork;
# - naturality in species maps: relabel(lift_contributions(P), f) = lift_contributions(relabel(P, f))
#   (Lean NEP.lift_map), including a merge of species;
# - H8: disjoint_union on a block-diagonal MultitypeNetwork is block diagonal (no cross
#   coordinates) and each block is the untyped lift of its part;
# - stratification commutes with gluing (stratify(glue(A, B)) = glue of the stratified parts).
#
# Equality of fields is checked two ways: exactly (the difference of the right-hand sides,
# constants folded, expands to 0) and with NetworkEpiCore's vector_fields_equal.

using EdgeBasedModels
using NetworkEpiCore
using ModelingToolkit
using Symbolics
using OrdinaryDiffEq: Vern9
using Test

const TOL = (solver = Vern9(), reltol = 1e-12, abstol = 1e-14)

function _expand_fully(d)
    for _ in 1:10
        e = Symbolics.expand(Symbolics.simplify(Symbolics.expand(d)))
        v = Symbolics.value(e)
        (v isa Number || isequal(e, d)) && return v
        d = e
    end
    return Symbolics.value(d)
end

# The two fields have the same state names and exactly the same right-hand sides.
function same_field(a::SymbolicODE, b::SymbolicODE)
    Set(state_names(a)) == Set(state_names(b)) || (@error "states differ" state_names(a) state_names(b); return false)
    nb = state_names(b)
    for (n, fa) in zip(state_names(a), a.rhs)
        fb = b.rhs[findfirst(==(n), nb)]
        d = Symbolics.substitute(Symbolics.wrap(fa) - Symbolics.wrap(fb), Dict{Any,Any}(); fold = Val(true))
        v = _expand_fully(d)
        (v isa Number && iszero(v)) || (@error "the fields differ" n v; return false)
    end
    return vector_fields_equal(a, b)
end

@testset "lift: composition (H1, naturality, H8)" begin
    net = ConfigurationNetwork(NegBinDegree(mean = 4, var = 8))       # a non-Poisson PGF
    tr = open_model(ContactModel(:tr; contacts = [Contact(:S, :I, :E, :τ)]); legs = [[:S], [:E, :I]])
    pr = open_model(ContactModel(:pr; transitions = [NodeTransition(:E, :I, :σ), NodeTransition(:I, :R, :γ)]);
                    legs = [[:E, :I, :R]])

    @testset "H1: glue(tr, pr) (design §B.8) is the sum of the parts' contributions" begin
        seir2 = glue(tr, pr; on = [:E, :I])
        @test isequivalent(seir2.model, seir_model())
        glued = symbolic_ode(edge_based(seir2, net))
        parts = sum_contributions(lift_contributions(tr, net), lift_contributions(pr, net))
        @test parts isa LiftContributions && length(parts) == 3
        @test same_field(glued, symbolic_ode(parts))
        @test vector_fields_equal(glued, parts)                          # the B.8 call itself
        # the transition-only part has no susceptible class and no θ: it is lifted anyway
        prt = lift_contributions(pr, net)
        @test first.(prt.coordinates) == [:φ_E, :φ_I, :φ_R, :pop_E, :pop_I, :pop_R] && isempty(prt.seed_factors)
        # and the glued SEIR is the canned SEIR
        @test same_field(glued, symbolic_ode(edge_based(seir_model(), net)))
    end

    @testset "H1 with an exit part (vaccination, the ξ factor)" begin
        vx = ContactModel(:vx; transitions = [NodeTransition(:S, :V, :ν)])
        sirv = glue(open_model(sir_model(); legs = [[:S, :I, :R]]), open_model(vx; legs = [[:S]]); on = [:S])
        @test isequivalent(sirv.model, sirv_model())
        glued = symbolic_ode(edge_based(sirv, net))
        @test :ξ in state_names(glued)
        parts = sum_contributions(lift_contributions(sir_model(), net), lift_contributions(vx, net; susceptible = [:S]))
        @test same_field(glued, symbolic_ode(parts))
        # the contact part alone drops ξ (nothing exits), but inside the sum it is kept
        @test :ξ ∉ state_names(symbolic_ode(lift_contributions(sir_model(), net)))
        # a part with a contact whose recipient is not susceptible is not an EB part
        bad = ContactModel(:bad; contacts = [Contact(:E, :I, :Q, :α)])
        @test_throws ArgumentError lift_contributions(bad, net; susceptible = Symbol[])
        @test_throws ArgumentError lift_contributions(ContactModel(:re; transitions = [NodeTransition(:I, :S, :γ)]),
                                                     net; susceptible = [:S])      # resus
    end

    @testset "H1 for a namespaced gluing: push the parts along the inclusions" begin
        g2 = glue(tr, pr; on = [:E, :I], namespace = true)
        @test length(g2.inclusions) == 2
        glued = symbolic_ode(edge_based(g2, net))
        pushed = sum_contributions(relabel(lift_contributions(tr, net), g2.inclusions[1]),
                                   relabel(lift_contributions(pr, net), g2.inclusions[2]))
        @test same_field(glued, symbolic_ode(pushed))
        # without the pushforward the names do not match
        @test !vector_fields_equal(glued, sum_contributions(lift_contributions(tr, net), lift_contributions(pr, net));
                                   rename = :none)
    end

    @testset "naturality: relabel(lift(P), f) = lift(relabel(P, f)), with a merge" begin
        # merging the two strains I1, I2 ↦ I adds the rates of the merged contacts (τ1 + τ2)
        two = twostrain_model()
        f = Dict(:I1 => :I, :I2 => :I, :R => :R)
        pushed = relabel(lift_contributions(two, net), f)
        @test same_field(symbolic_ode(pushed), symbolic_ode(lift_contributions(relabel(two, f), net)))
        # a bijection that renames the susceptible class renames q_<s> too
        g = Dict(:S => :U, :I => :J)
        pushed = relabel(lift_contributions(sir_model(), net), g)
        @test first.(pushed.seed_factors) == [:U]
        @test same_field(symbolic_ode(pushed), symbolic_ode(lift_contributions(relabel(sir_model(), g), net)))
        # Tables whose susceptible classes differ share the name θ but not the class, and an
        # untyped network has one susceptible class: the sum is refused (it would keep both q_S
        # and q_U on one θ); pushing one table onto the other's class first makes it a sum.
        sir = lift_contributions(sir_model(), net)
        uj = lift_contributions(ContactModel(:uj; contacts = [Contact(:U, :I, :I, :τ2)]), net)
        @test_throws ArgumentError sum_contributions(sir, uj)
        @test_throws ArgumentError sum_contributions(sir, relabel(sir, Dict(:S => :U)))
        both = sum_contributions(sir, relabel(uj, Dict(:U => :S)))
        @test first.(both.seed_factors) == [:S] && length(both) == 3
        # the same on a MultitypeNetwork: θ_<b>_<a> belongs to the susceptible class of type a
        st = strata([:a, :b]; sizes = [0.4, 0.6])
        mnet = sbm_network(st; mean_contacts = [6.0 3.0; 2.0 4.0])
        sa = lift_contributions(stratify(sir_model(), st), mnet)
        @test_throws ArgumentError sum_contributions(sa, relabel(sa, Dict(:S_a => :U_a)))
    end

    @testset "H1 on WellMixed and on a MultitypeNetwork (stratify commutes with glue)" begin
        wm = WellMixed(5.0)
        seir2 = glue(tr, pr; on = [:E, :I])
        @test same_field(symbolic_ode(edge_based(seir2, wm)),
                         symbolic_ode(sum_contributions(lift_contributions(tr, wm), lift_contributions(pr, wm))))
        st = strata([:a, :b]; sizes = [0.4, 0.6])
        mnet = sbm_network(st; mean_contacts = [6.0 3.0; 2.0 4.0])
        whole = symbolic_ode(edge_based(stratify(seir2.model, st), mnet))
        parts = sum_contributions(lift_contributions(stratify(tr.model, st), mnet),
                                  lift_contributions(stratify(pr.model, st), mnet))
        @test same_field(whole, symbolic_ode(parts))
        # different networks do not sum (F5)
        @test_throws ArgumentError sum_contributions(lift_contributions(tr, net), lift_contributions(pr, wm))
    end

    @testset "H8: disjoint_union on a block-diagonal network is block diagonal" begin
        A = sir_model(τ = 0.3, γ = 0.2)
        B = seir_model(τ = 0.25, σ = 0.5, γ = 0.2)
        du = disjoint_union(:a => A, :b => B)
        st = strata([:a, :b]; sizes = [0.4, 0.6])
        mnet = sbm_network(st; mean_contacts = [4.0 0.0; 0.0 3.0])
        @test mnet.structural_zero == [false true; true false]
        sys = edge_based(du, mnet)
        # structural zeros produce no coordinates: no θ_b_a, θ_a_b, φ_<X_b>_a, …
        ks = Set(keys(sys.variables))
        @test :θ_a_a in ks && :θ_b_b in ks && !(:θ_a_b in ks) && !(:θ_b_a in ks)
        @test !any(k -> occursin("_b_a", string(k)) || occursin("_a_b", string(k)), ks)
        sol = solve_epidemic(sys; initial = SeedFraction(:I_a => 0.004, :E_b => 0.006), tspan = (0.0, 80.0),
                             saveat = 1.0, TOL...)
        @test all(x -> all(isfinite, x), (compartment(sys, sol, k) for k in keys(sys.variables)))
        # each block is the untyped lift of its part, with the within-type seed ρ/n
        sa = edge_based(A, ConfigurationNetwork(PoissonDegree(4.0)))
        sb = edge_based(B, ConfigurationNetwork(PoissonDegree(3.0)))
        sola = solve_epidemic(sa; initial = SeedFraction(:I => 0.01), tspan = (0.0, 80.0), saveat = 1.0, TOL...)
        solb = solve_epidemic(sb; initial = SeedFraction(:E => 0.01), tspan = (0.0, 80.0), saveat = 1.0, TOL...)
        @test maximum(abs.(compartment(sys, sol, :S_a) ./ 0.4 .- compartment(sa, sola, :S))) < 1e-10
        @test maximum(abs.(compartment(sys, sol, :S_b) ./ 0.6 .- compartment(sb, solb, :S))) < 1e-10
        @test maximum(abs.(compartment(sys, sol, :θ_a_a) .- compartment(sa, sola, :θ))) < 1e-10
        @test maximum(abs.(compartment(sys, sol, :φ_I_b_b) .- compartment(sb, solb, :φ_I))) < 1e-10
        @test maximum(abs.(compartment(sys, sol, :pop_E_b) ./ 0.6 .- compartment(sb, solb, :pop_E))) < 1e-10
    end
end
