"""Balanced in averaged-Prefix form (Algorithms 2' and 2'C) and buffered Flat.

Algorithm 2' realizes the Balanced history through virtual Prefix iterates
x_s (x_s - x^star = T_s(Z) e_0 / C_s) and one parity running average per class:
the query is y_s = Ybar + theta_s (x_s - Ybar), the gradient at x_s is
recovered affinely, G = Gbar + (g - Gbar) / theta_s, and the averages are
updated with weight phi_s. The output is the last Prefix iterate x_N.
All scalar coefficients are ratios: r_s = C_s / C_{s+1}, zeta_s = Z_s / C_s,
theta_s = varpi_s / zeta_s, phi_s = (varpi_s - varpi_{s+2}) / (zeta_s - varpi_{s+2}).
The Python function omega(), result key 'omega' and coefficient array w
retain their implementation names for averaging weights varpi_s (ϖ_s);
the printed omega_s denotes an oracle error.
No Chebyshev value C_s is formed, so the preparation cannot overflow.

Algorithm 2'C keeps a compensation vector for each point average
(Fast2Sum-style update of Ybar + c). It uses nine vector slots; 2' uses seven.
Buffered Flat forms the query in a fifth slot instead of overwriting and
restoring V; its coefficients are those of Algorithm 1.

Every routine takes an optional rounding function. With none, the vector
arithmetic is ordinary float64. Otherwise every operation result is rounded
by it (working-precision emulation with float64 coefficients), for example
rounding("fp32") or rounding("bf16") from lowprec.round_binary.
"""

from decimal import Decimal, localcontext

import numpy as np


def _same(value):
    return value


def rounding(fmt="fp64", mode="RN", rng=None):
    """Rounding of each operation result to fmt; None means float64 arithmetic."""
    if fmt == "fp64":
        return None
    if fmt == "fp32" and mode == "RN":
        return lambda v: np.asarray(v, dtype=float).astype(np.float32).astype(float)
    from lowprec import round_binary

    return lambda v: round_binary(v, fmt, mode, rng)


def omega(N, s, one=1):
    """Balanced class weights varpi_s (exact rational, cast through `one`)."""
    if s < 2:
        return one
    if N % 2 == 0:
        return one * (N + 2 - s - s % 2) / N
    if s % 2 == 0:
        return one * ((N + 1) * (N + 1 - s)) / (N * N + 1)
    return one * (N + 2 - s) / (N + 1)


def ratios(N, mu, L, one=1.0):
    """Ratio-only scalar preparation of Algorithm 2'.

    `one` fixes the number type (Decimal for the 80-digit preparation, float
    for a plain float64 preparation). Every intermediate lies in a bounded
    range: 0 < r_s < 1, varpi_s <= zeta_s <= 1, 0 < theta_s, phi_s <= 1.
    Returns lists alpha, beta, theta, phi, omega, zeta, r (length N each).
    """
    D = L - mu
    eta = (L + mu) / D
    r = [one / eta]
    for _ in range(1, N):
        r.append(one / (2 * eta - r[-1]))
    alpha = [2 * one / (L + mu)] + [4 * r[s] / D for s in range(1, N)]
    beta = [0 * one] + [r[s - 1] * r[s] for s in range(1, N)]
    w = [omega(N, s, one) for s in range(N + 2)]
    zeta = [one, one]
    for s in range(2, N):
        zeta.append(w[s] + (zeta[s - 2] - w[s]) * (r[s - 2] * r[s - 1]))
    zeta = zeta[:N]
    theta = [one if s < 2 else w[s] / zeta[s] for s in range(N)]
    # phi_s is used only for 2 <= s <= N-3; the first element of each class
    # starts its average (phi = 1), later entries are unused (stored as 0).
    phi = [
        one if s < 2 else (w[s] - w[s + 2]) / (zeta[s] - w[s + 2]) if s + 2 < N else 0 * one
        for s in range(N)
    ]
    return {"alpha": alpha, "beta": beta, "theta": theta, "phi": phi,
            "omega": w[:N], "zeta": zeta, "r": r}


def prepare_averaged(method, N, mu, L):
    """80-digit ratio-only preparation for 'balanced2' and 'balanced2c'.

    Besides the iteration coefficients it stores the Balanced response data
    (w, invZ, scale) in ratio form: 1/Z_s = prod_{j<s} r_j / zeta_s and
    Z_s / C_N = zeta_s prod_{j>=s} r_j. These products underflow gracefully.
    """
    if method not in ("balanced2", "balanced2c"):
        raise ValueError(method)
    with localcontext() as ctx:
        ctx.prec = 80
        lo, hi = Decimal(str(mu)), Decimal(str(L))
        q = ratios(N, lo, hi, Decimal(1))
        r, zeta = q["r"], q["zeta"]
        head = [Decimal(1)]
        for s in range(1, N):
            head.append(head[-1] * r[s - 1])  # 1/C_s
        tail = [Decimal(1)] * (N + 1)
        for s in reversed(range(N)):
            tail[s] = tail[s + 1] * r[s]  # C_s/C_N
        D = hi - lo
        values = {k: np.array([float(v) for v in q[k]]) for k in ("alpha", "beta", "theta", "phi")}
        return {
            "method": method,
            "N": N,
            "mu": mu,
            "L": L,
            "compensated": method == "balanced2c",
            **values,
            "w": np.array([float(v) for v in q["omega"]]),
            "invZ": np.array([float(head[s] / zeta[s]) for s in range(N)]),
            "scale": np.array([float(-4 * zeta[s] * tail[s] / D) for s in range(N)]),
        }


def run_averaged(c, x0, oracle, rounding=None, compensated=None):
    """Algorithm 2' (7 slots) or 2'C (9 slots); exactly N oracle calls.

    oracle(y, s) receives the actual query at call s. Vectors are never
    modified in place, so x0 may be a read-only broadcast view.
    """
    R = rounding or _same
    N = c["N"]
    if compensated is None:
        compensated = c["compensated"]
    alpha, beta, theta, phi = c["alpha"], c["beta"], c["theta"], c["phi"]
    x = previous = x0
    points, gradients, corrections = [None, None], [None, None], [None, None]
    for s in range(N):
        k = s % 2
        if s < 2:
            query = x
        else:
            base = R(points[k] + corrections[k]) if compensated else points[k]
            query = R(base + R(theta[s] * R(x - base)))
        g = oracle(query, s)
        if s >= 2:  # gradient at x_s from the affine oracle model
            g = R(gradients[k] + R(R(g - gradients[k]) / theta[s]))
        if s + 2 < N:
            if s < 2:
                points[k], gradients[k] = x, g
                corrections[k] = np.zeros_like(x) if compensated else None
            else:
                f = phi[s]
                if compensated:
                    old = points[k]
                    increment = R(corrections[k] + R(f * R(R(x - old) - corrections[k])))
                    points[k] = R(old + increment)
                    corrections[k] = -R(R(points[k] - old) - increment)
                else:
                    points[k] = R(points[k] + R(f * R(x - points[k])))
                gradients[k] = R(gradients[k] + R(f * R(g - gradients[k])))
        previous, x = x, R(R(R((1 + beta[s]) * x) - R(beta[s] * previous)) - R(alpha[s] * g))
    return x


def run_flat_buffered(c, x0, oracle, rounding=None):
    """Algorithm 1 with a fifth slot for the query; V is never overwritten."""
    R = rounding or _same
    N, tau = c["N"], c["tau"]
    V = P = x0
    G = np.zeros_like(x0, dtype=float)
    for s in range(N):
        t = tau[s]
        g = oracle(R(V + R(t * R(V - P))), s)
        G = R(R(g + R(t * G)) / (1 + t))
        if s == N - 1:
            a, b = c["last_a"], c["last_b"]
            return R(R(R((1 + a) * V) - R(a * P)) - R(b * G))
        V, P = R(R(R((1 + c["beta"][s]) * V) - R(c["beta"][s] * P)) - R(c["alpha"][s] * G)), V
