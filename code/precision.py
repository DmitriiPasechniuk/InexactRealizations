"""Attainable accuracy of the realizations in working precision.

Every vector operation result is rounded to the working format (binary32
by an exact float32 cast of each float64 result, fp16/bf16 by
lowprec.round_binary, binary64 natively); coefficients are float64 from
the 80-digit preparation. The test problem is a diagonal quadratic with
eigenvalues mu, L and 398 uniform draws, x0 = 0 and a random unit solution;
the oracle returns fl(lam * y - b) with b = fl(lam * x*). Errors are RMS
relative final errors ||x_N - x*|| / ||x*|| over seeds 100, 101, ...

Forms: pref (classical recurrence), flat_alg1 (Algorithm 1 as printed:
query formed in V and restored), flat (the experiments' Flat, query in a
temporary), flat5 (five-slot buffer), balanced (eq:W with compensated
readout, as in the experiments), balanced2 (Algorithm 2'), balanced2c
(Algorithm 2'C). pref, flat and balanced follow common.run operation by
operation; without rounding they reproduce it bit for bit.

python precision.py table [--seeds 8] [--output results/precision_2pc]
"""

import argparse
import json
import math
import time
from pathlib import Path

import numpy as np

from averaged import _same, rounding, run_averaged, run_flat_buffered
from common import prepare

HERE = Path(__file__).resolve().parent
FORMS = ("pref", "flat_alg1", "flat", "flat5", "balanced", "balanced2", "balanced2c")
LABEL = {
    "pref": "Prefix",
    "flat_alg1": "Flat Alg. 1 (printed, 4 slots)",
    "flat": "Flat (experiments)",
    "flat5": "Flat 5-slot",
    "balanced": "Balanced (eq:W)",
    "balanced2": "Balanced 2′ (7 slots)",
    "balanced2c": "Balanced 2′C (9 slots)",
}
# Research report BEZOUT-RESEARCH-CD.md, D.4 and d_final.txt (8 seeds).
# Columns: Prefix, Flat Alg. 1, Flat 5-slot, eq:W, 2', 2'C.
RESEARCH = {
    ("fp32", 100, 1024): (1.4e-7, 2.4e-6, 3.4e-7, 1.9e-5, 3.8e-7, 2.4e-7),
    ("fp32", 100, 2048): (1.4e-7, 4.6e-6, 3.3e-7, 3.9e-5, 3.6e-7, 2.4e-7),
    ("fp32", 10000, 1024): (4.6e-6, 1.6e-5, 2.1e-5, 7.5e-4, 1.8e-5, 4.7e-6),
    ("fp32", 10000, 2048): (4.6e-6, 1.5e-5, 2.0e-5, 7.7e-4, 1.8e-5, 5.0e-6),
    ("fp64", 100, 1024): (4.8e-16, 4.7e-15, 6.3e-16, 2.5e-14, 9.0e-16, 6.0e-16),
    ("fp64", 100, 2048): (4.8e-16, 9.1e-15, 6.3e-16, 4.0e-14, 9.1e-16, 6.1e-16),
    ("fp64", 10000, 1024): (1.8e-9,) * 6,
    ("fp64", 10000, 2048): (1.5e-14, 2.7e-14, 3.8e-14, 1.6e-12, 2.2e-14, 1.7e-14),
}
RESEARCH_FORMS = ("pref", "flat_alg1", "flat5", "balanced", "balanced2", "balanced2c")


def _prefix(c, x0, oracle, R):
    x = previous = x0
    for s, (alpha, beta) in enumerate(zip(c["alpha"], c["beta"])):
        g = oracle(x, s)
        previous, x = x, R(R(R((1 + beta) * x) - R(beta * previous)) - R(alpha * g))
    return x


def _flat(c, x0, oracle, R, printed):
    N = c["N"]
    V = P = x0
    G = np.zeros_like(x0, dtype=float)
    for s, t in enumerate(c["tau"]):
        if printed:  # A <- V - P; V <- V + tau A; A <- O(V); restore V
            Y = R(V + R(t * R(V - P)))
            A = oracle(Y, s)
            V = R(R(Y + R(t * P)) / (1 + t))
        else:
            A = oracle(R(R((1 + t) * V) - R(t * P)), s)
        G = R(R(A + R(t * G)) / (1 + t))
        if s == N - 1:
            a, b = c["last_a"], c["last_b"]
            return R(R(R((1 + a) * V) - R(a * P)) - R(b * G))
        V, P = R(R(R((1 + c["beta"][s]) * V) - R(c["beta"][s] * P)) - R(c["alpha"][s] * G)), V


def _balanced_w(c, x0, oracle, R):
    N = c["N"]
    X, correction = x0, np.zeros_like(x0, dtype=float)

    def accumulate(g, s):
        nonlocal X, correction
        term = R(R(-c["b"][s] * g) - correction)
        new = R(X + term)
        correction = R(R(new - X) - term)
        X = new

    g0 = oracle(x0, 0)
    accumulate(g0, 0)
    previous = R(x0 - R(c["first"] * g0))
    g1 = oracle(previous, 1)
    accumulate(g1, 1)
    if N == 2:
        return X
    a, b, d = c["start"]
    v = R(R(a * x0) + R(b * R(g0 + g1)))
    old_v = np.zeros_like(x0, dtype=float)
    query = R(R(d * x0) + R(c["w"][2] * v))
    old_g, g_previous = g0, g1
    for s in range(2, N):
        g = oracle(query, s)
        accumulate(g, s)
        if s + 1 < N:
            a, b, d, e, f = c["W"][s]
            next_v = R(R(R(R(a * v) + R(b * old_v)) + R(d * g)) + R(e * old_g))
            previous, query = query, R(R(f * previous) + R(c["w"][s + 1] * next_v))
            old_v, v = v, next_v
            old_g, g_previous = g_previous, g
    return X


def execute(form, N, mu, L, x0, oracle, rounding_function=None):
    """Run one form with every vector operation rounded; exactly N calls."""
    R = rounding_function or _same
    key = "flat" if form == "flat_alg1" else form
    c = prepare(key, N, mu, L)
    if form == "pref":
        return _prefix(c, x0, oracle, R)
    if form in ("flat", "flat_alg1"):
        return _flat(c, x0, oracle, R, form == "flat_alg1")
    if form == "flat5":
        return run_flat_buffered(c, x0, oracle, rounding_function)
    if form == "balanced":
        return _balanced_w(c, x0, oracle, R)
    if form in ("balanced2", "balanced2c"):
        return run_averaged(c, x0, oracle, rounding_function)
    raise ValueError(form)


def problem(kappa, seed, dimension=400):
    """Diagonal test problem of the research report (same generator and seeds)."""
    rng = np.random.default_rng(seed)
    mu, L = 1 / kappa, 1.0
    lam = np.concatenate([[mu, L], mu + (L - mu) * rng.random(dimension - 2)])
    star = rng.standard_normal(dimension)
    return mu, L, lam, star / np.linalg.norm(star)


def relative_error(form, kappa, N, fmt="fp32", seed=100):
    mu, L, lam, star = problem(kappa, seed)
    R = rounding(fmt)
    Q = R or _same
    rhs = Q(lam * star)
    calls = []

    def oracle(y, s):
        calls.append(s)
        return Q(lam * y - rhs)

    x = execute(form, N, mu, L, np.zeros_like(star), oracle, R)
    if calls != list(range(N)):
        raise AssertionError(f"{form}: oracle calls {len(calls)} != {N}")
    return float(np.linalg.norm(x - star) / np.linalg.norm(star))


def rms(form, kappa, N, fmt="fp32", seeds=8):
    errors = [relative_error(form, kappa, N, fmt, 100 + j) for j in range(seeds)]
    return math.sqrt(float(np.mean(np.square(errors))))


def table(cases=None, forms=FORMS, seeds=8):
    cases = cases or [(fmt, kappa, N) for fmt in ("fp32", "fp64")
                      for kappa in (100, 10000) for N in (1024, 2048)]
    rows = []
    for fmt, kappa, N in cases:
        started = time.monotonic()
        values = {form: rms(form, kappa, N, fmt, seeds) for form in forms}
        theta = math.acosh((1 + 1 / kappa) / (1 - 1 / kappa))
        rows.append({"fmt": fmt, "kappa": kappa, "N": N, "seeds": seeds,
                     "epsilon": 1 / math.cosh(N * theta) if N * theta < 700 else 0.0,
                     "errors": values, "research": dict(zip(RESEARCH_FORMS, RESEARCH.get((fmt, kappa, N), ()))),
                     "seconds": time.monotonic() - started})
    return rows


def markdown(rows, forms=FORMS):
    head = "| format | κ | N | ε_N^⋆ | " + " | ".join(LABEL[f] for f in forms) + " |"
    lines = [head, "|" + "---|" * (4 + len(forms))]
    for r in rows:
        cells = []
        for f in forms:
            value = f"{r['errors'][f]:.1e}"
            if f in r["research"]:
                value += f" ({r['research'][f]:.1e})"
            cells.append(value)
        lines.append(f"| {r['fmt']} | {r['kappa']:g} | {r['N']} | {r['epsilon']:.1e} | " + " | ".join(cells) + " |")
    return "\n".join(lines) + "\n\nParentheses: research report D.4 / d_final.txt.\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("action", choices=("table", "lowformats"))
    parser.add_argument("--seeds", type=int, default=8)
    parser.add_argument("--output", type=Path, default=HERE / "results/precision_2pc")
    args = parser.parse_args()
    if args.action == "table":
        cases = None
    else:  # informative half-precision rows (not in the research table)
        cases = [(fmt, 100, N) for fmt in ("bf16", "fp16") for N in (256, 1024)]
    rows = table(cases, seeds=args.seeds)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / f"{args.action}.json").write_text(json.dumps(rows, indent=2) + "\n")
    text = markdown(rows)
    (args.output / f"{args.action}.md").write_text(text)
    print(text)
