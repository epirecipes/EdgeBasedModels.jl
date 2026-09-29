"""Like-for-like EoN references for the EdgeBasedModels EoN cross-validation (verified issue E29).

The legacy file ``test/eon_reference.json`` was produced by ``eon_crossval.py`` from ONE
Erdos-Renyi graph ER(N=1000, p=5/999, seed=42), whose empirical degree distribution is not
Poisson(5) (excess degree 5.034).  The legacy tests compare it with the exact ``poisson_pgf(5)``
and pass only because of loose tolerances (atol 5e-3, rtol 1e-2).  This script produces the
references that the E29 tests in ``test/suites/00_legacy_eon.jl`` compare against, each on the
SAME network and the SAME seeding convention as the Julia model:

* ``sir_poisson5``: EoN.EBCM_uniform_introduction on the exact Poisson(5) PGF;
* ``sir_er1000_seed42``: EoN.EBCM_from_graph on the ER graph of eon_crossval.py, with its
  empirical degree distribution ``pk`` (Julia uses ``polynomial_pgf(pk)``);
* ``attack_rate``: EoN.Attack_rate_cts_time on the exact Poisson(5) distribution, rho -> 0
  (the relation ``final_size`` implements) and rho = 0.01, and on the ER graph;
* ``sis``: EoN.SIS_compact_pairwise on exact Poisson(5) and on the ER graph (a different
  closure from EBM's reinfection-counting model; the comparison is approximate).

Parameters are the canonical anchors: tau = 1/6 (per edge), gamma = 1/4, rho = 0.01, so
T = 0.4 and R0 = 2 on Poisson(5).

Usage (from the repository root, with the EoN source tree next to the packages):

    python3 EdgeBasedModels.jl/test/golden/eon/generate_eon.py   (needs numpy, scipy, networkx, matplotlib)

It rewrites ``eon_like_for_like.toml`` and the two ``*_curves.csv`` files next to this script.
Everything is deterministic (the only random object is the seeded ER graph).
"""

import math
import os
import platform
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
EON_SRC = os.path.abspath(os.path.join(HERE, "..", "..", "..", "..", "EoN"))
sys.path.insert(0, EON_SRC)

import networkx as nx  # noqa: E402
import numpy as np  # noqa: E402
import scipy  # noqa: E402

import EoN  # noqa: E402

GAMMA = 0.25
KAPPA = 5
TAU = (2.0 / KAPPA) * GAMMA / (1 - 2.0 / KAPPA)  # 1/6: T = 0.4, R0 = T * kappa = 2
RHO = 0.01
TMAX = 40.0
TCOUNT = 201  # 0.2 time units, as in eon_crossval.py
N_ER = 1000
SIS_TMAX = 400.0


def poisson_pk(kmax=80):
    pk = np.array([math.exp(-KAPPA) * KAPPA**k / math.factorial(k) for k in range(kmax + 1)])
    return pk / pk.sum()


def write_curves(path, t, S, I, R):
    with open(path, "w", encoding="utf-8") as io:
        io.write("t,S,I,R\n")
        for row in zip(t, S, I, R):
            io.write(",".join(repr(float(x)) for x in row) + "\n")


def toml_value(x):
    if isinstance(x, str):
        return '"' + x.replace("\\", "\\\\").replace('"', '\\"') + '"'
    if isinstance(x, bool):
        return "true" if x else "false"
    if isinstance(x, (int, np.integer)):
        return str(int(x))
    if isinstance(x, (float, np.floating)):
        return repr(float(x))
    if isinstance(x, (list, tuple, np.ndarray)):
        return "[" + ", ".join(toml_value(v) for v in x) + "]"
    raise TypeError(type(x))


def main():
    # --- SIR EBCM on the exact Poisson(5) PGF --------------------------------------------------
    psi = lambda x: np.exp(KAPPA * (x - 1))  # noqa: E731
    dpsi = lambda x: KAPPA * np.exp(KAPPA * (x - 1))  # noqa: E731
    t, S, I, R = EoN.EBCM_uniform_introduction(1, psi, dpsi, TAU, GAMMA, RHO,
                                              tmin=0, tmax=TMAX, tcount=TCOUNT)
    write_curves(os.path.join(HERE, "sir_poisson5_curves.csv"), t, S, I, R)
    pois = dict(peak_I=float(I.max()), peak_t=float(t[I.argmax()]), R40=float(R[-1]),
                S0=float(S[0]), I0=float(I[0]))

    # --- SIR EBCM on the ER(1000, seed 42) graph used by eon_crossval.py -------------------------
    G = nx.erdos_renyi_graph(N_ER, KAPPA / (N_ER - 1), seed=42)
    Pk = EoN.get_Pk(G)
    kmax = max(Pk)
    pk = [float(Pk.get(k, 0.0)) for k in range(kmax + 1)]
    tg, Sg, Ig, Rg = EoN.EBCM_from_graph(G, TAU, GAMMA, rho=RHO, tmin=0, tmax=TMAX, tcount=TCOUNT)
    Sg, Ig, Rg = Sg / N_ER, Ig / N_ER, Rg / N_ER
    write_curves(os.path.join(HERE, "sir_er1000_seed42_curves.csv"), tg, Sg, Ig, Rg)
    mean_k = sum(k * p for k, p in enumerate(pk))
    excess = sum(k * (k - 1) * p for k, p in enumerate(pk)) / mean_k
    er = dict(peak_I=float(Ig.max()), peak_t=float(tg[Ig.argmax()]), R40=float(Rg[-1]),
              mean_degree=float(mean_k), excess_degree=float(excess))

    # --- Attack rates ------------------------------------------------------------------------------
    pois_pk = {k: float(p) for k, p in enumerate(poisson_pk())}
    ar = dict(
        poisson5_rho_to_0=float(EoN.Attack_rate_cts_time(pois_pk, TAU, GAMMA, rho=None, number_its=2000)),
        poisson5_rho_001=float(EoN.Attack_rate_cts_time(pois_pk, TAU, GAMMA, rho=RHO, number_its=2000)),
        er1000_seed42_rho_001=float(EoN.Attack_rate_cts_time(Pk, TAU, GAMMA, rho=RHO)),
    )

    # --- SIS compact pairwise -------------------------------------------------------------------------
    ppk = poisson_pk(60)
    ks = np.arange(len(ppk))
    kbar = float((ks * ppk).sum())
    ts, Ss, Is = EoN.SIS_compact_pairwise((1 - RHO) * ppk, RHO * ppk, kbar * (1 - RHO) * RHO,
                                          kbar * (1 - RHO) ** 2, kbar * RHO**2, TAU, GAMMA,
                                          tmax=SIS_TMAX, tcount=1001)
    tse, Sse, Ise = EoN.SIS_compact_pairwise_from_graph(G, TAU, GAMMA, rho=RHO, tmax=SIS_TMAX, tcount=1001)
    sis = dict(poisson5_compact_pairwise_I_end=float(Is[-1]),
               er1000_seed42_compact_pairwise_I_end=float(Ise[-1] / N_ER), tmax=SIS_TMAX)

    lines = [
        "# Generated by test/golden/eon/generate_eon.py -- do not edit by hand.",
        "# Like-for-like EoN references for verified issue E29 (see the script docstring).",
        "schema = 1",
        'kind = "external_reference"',
        'issues = ["E29"]',
        "",
        "[provenance]",
        f"eon = {toml_value(getattr(EoN, '__version__', 'unknown'))}",
        f"eon_source = {toml_value('EoN source tree next to the packages (sys.path insert)')}",
        f"networkx = {toml_value(nx.__version__)}",
        f"numpy = {toml_value(np.__version__)}",
        f"scipy = {toml_value(scipy.__version__)}",
        f"python = {toml_value(platform.python_version())}",
        "",
        "[setup]",
        f"tau = {toml_value(TAU)}",
        f"gamma = {toml_value(GAMMA)}",
        f"rho = {toml_value(RHO)}",
        f"tmax = {toml_value(TMAX)}",
        f"tcount = {toml_value(TCOUNT)}",
        "",
        "[sir_poisson5]",
        f"call = {toml_value('EoN.EBCM_uniform_introduction(1, psi, psi_prime, tau, gamma, rho, tmin=0, tmax=40, tcount=201) with psi(x) = exp(5(x-1))')}",
        'curves = "sir_poisson5_curves.csv"',
    ] + [f"{k} = {toml_value(v)}" for k, v in pois.items()] + [
        "",
        "[sir_er1000_seed42]",
        f"call = {toml_value('EoN.EBCM_from_graph(G, tau, gamma, rho=rho, tmin=0, tmax=40, tcount=201) with G = networkx.erdos_renyi_graph(1000, 5/999, seed=42)')}",
        'curves = "sir_er1000_seed42_curves.csv"',
        f"pk = {toml_value(pk)}",
    ] + [f"{k} = {toml_value(v)}" for k, v in er.items()] + [
        "",
        "[attack_rate]",
        f"call = {toml_value('EoN.Attack_rate_cts_time(Pk, tau, gamma, rho=...)')}",
    ] + [f"{k} = {toml_value(v)}" for k, v in ar.items()] + [
        "",
        "[sis]",
        f"call = {toml_value('EoN.SIS_compact_pairwise on the exact Poisson(5) degree counts (k <= 60), and EoN.SIS_compact_pairwise_from_graph on G; rho = 0.01, tmax = 400')}",
    ] + [f"{k} = {toml_value(v)}" for k, v in sis.items()] + [""]
    with open(os.path.join(HERE, "eon_like_for_like.toml"), "w", encoding="utf-8") as io:
        io.write("\n".join(lines))
    print("sir_poisson5", pois)
    print("sir_er1000_seed42", er)
    print("attack_rate", ar)
    print("sis", sis)


if __name__ == "__main__":
    main()
