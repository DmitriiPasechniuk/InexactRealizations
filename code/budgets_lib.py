"""Library for Table 1 (tab:budgets): positive-peak histories, Flat, Balanced and LF/fractal data.
Everything is built from the formulas printed in bezout.tex:
  z(lam) = eta - 2 lam/Delta, Phi_s = -4 eps f_s(z)/Delta, pi_s = q_s(z),
  B_N(x,y) = (T_N(x)-T_N(y))/(2(x-y)) = sum_s f_s(x) q_s(y), q_s(eta) = 1.
Requires mpmath and NumPy."""
import mpmath as mp
import numpy as np

mp.mp.dps = 60


def params(N, kappa, L=1):
    L = mp.mpf(L)
    mu = L / kappa
    D = L - mu
    eta = (L + mu) / D
    C = [mp.mpf(1), eta]
    for s in range(2, N + 2):
        C.append(2 * eta * C[-1] - C[-2])
    eps = 1 / C[N]
    S = (1 - eps) / mu
    DN = 2 * eps * N ** 2 / D
    sig2 = 1 + ((N - 1) / mp.mpf((N + 1) * N ** 2) if N % 2 else 0)
    GN = DN / mp.sqrt(N) * mp.sqrt(sig2)
    return dict(N=N, kappa=kappa, L=L, mu=mu, D=D, eta=eta, C=C, eps=eps, S=S, DN=DN, GN=GN)


# ---------- Chebyshev-series helpers (coefficient lists, index = degree) ----------
def chebT(k):
    c = [mp.mpf(0)] * (k + 1); c[k] = mp.mpf(1); return c


def chebU(k):
    # U_k = 2(T_k + T_{k-2} + ...) with the T_0 term counted once
    c = [mp.mpf(0)] * (k + 1)
    for j in range(k, -1, -2):
        c[j] = mp.mpf(2) if j > 0 else mp.mpf(1)
    return c


def cheb_eval(c, x):
    # Clenshaw
    b1 = b2 = 0 * x
    for a in reversed(c[1:]):
        b1, b2 = 2 * x * b1 - b2 + a, b1
    return x * b1 - b2 + c[0]


def bezout_matrix(N):
    """C[k][j] = coefficient of T_k(x) T_j(y) in B_N (claimed: e_k e_j / 2 if k+j<=n, k+j = n mod 2)."""
    n = N - 1
    e = lambda j: 1 if j == 0 else 2
    return [[mp.mpf(e(k) * e(j)) / 2 if (k + j <= n and (n - k - j) % 2 == 0) else mp.mpf(0)
             for j in range(N)] for k in range(N)]


def responses_from_queries(N, Q):
    """Q[s] = Chebyshev coefficients of q_s (len s+1).  Returns F[s] = coefficients of f_s with
    B_N = sum_s f_s(x) q_s(y), i.e. C = F^⊤ Qmat  ->  F^⊤ = C Qmat^{-1}."""
    C = mp.matrix(bezout_matrix(N))
    Qm = mp.matrix(N, N)
    for s in range(N):
        for j, a in enumerate(Q[s]):
            Qm[s, j] = a
    FT = C * mp.inverse(Qm)
    return [[FT[k, s] for k in range(N)] for s in range(N)]


def normalize(qc, eta):
    v = cheb_eval(qc, eta)
    return [a / v for a in qc]


# ---------- query bases ----------
def q_prefix(P):
    N, C = P['N'], P['C']
    return [[a / C[s] for a in chebT(s)] for s in range(N)]


def flat_data(P):
    N, eta = P['N'], P['eta']
    n = N - 1
    u = [mp.mpf(1), 2 * eta]
    for j in range(2, N + 1):
        u.append(2 * eta * u[-1] - u[-2])
    a = [u[n] / 2] + [u[n - m] for m in range(1, n + 1)]
    M = sum(a)
    d = M / N
    R = [sum(a[:m + 1]) - m * d for m in range(N)]
    tau = [R[n - s] / d - 1 for s in range(N)]
    return u, a, M, d, R, tau


def q_flat(P):
    N = P['N']
    u, a, M, d, R, tau = flat_data(P)
    Q = []
    for s in range(N):
        c = [(1 + tau[s]) * x / u[s] for x in chebU(s)]
        if s > 0:
            cu = chebU(s - 1)
            for j in range(s):
                c[j] -= tau[s] * cu[j] / u[s - 1]
        Q.append(c)
    return Q


def balanced_omega(N):
    om = [mp.mpf(1), mp.mpf(1)]
    for s in range(2, N):
        if N % 2 == 0:
            om.append(mp.mpf(N + 2 - s - (s % 2)) / N)
        elif s % 2 == 0:
            om.append(mp.mpf((N + 1) * (N + 1 - s)) / (N * N + 1))
        else:
            om.append(mp.mpf(N + 2 - s) / (N + 1))
    return om


def q_balanced(P):
    N, eta = P['N'], P['eta']
    om = balanced_omega(N)
    Psi = [chebT(0), chebT(1)]
    for s in range(2, N):
        c = Psi[s - 2] + [mp.mpf(0)] * 2
        c[s] += om[s]
        c[s - 2] -= om[s]
        Psi.append(c)
    return [normalize(c, eta) for c in Psi[:N]]


def sj_a2(N):
    return [None] + [mp.sin(mp.pi * s / N) ** 2 / (4 * mp.sin(mp.pi * (s - mp.mpf(1) / 2) / N)
                                                   * mp.sin(mp.pi * (s + mp.mpf(1) / 2) / N)) for s in range(1, N)]


def sj_leading(N):
    """monic leading polynomials P_0..P_N of the sine-Jacobi matrix (zero diagonal), Chebyshev coefficients."""
    a2 = sj_a2(N)
    P = [chebT(0), chebT(1)]  # P_1 = x
    for s in range(1, N):
        # P_{s+1} = x P_s - a2[s] P_{s-1};  x T_k = (T_{k+1} + T_{|k-1|})/2
        xp = [mp.mpf(0)] * (s + 2)
        for k, c in enumerate(P[s]):
            if k == 0:
                xp[1] += c
            else:
                xp[k + 1] += c / 2
                xp[k - 1] += c / 2
        for k, c in enumerate(P[s - 1]):
            xp[k] -= a2[s] * c
        P.append(xp)
    return P


def q_sinejacobi(P):
    N, eta = P['N'], P['eta']
    Ps = sj_leading(N)
    return [normalize(Ps[s], eta) for s in range(N)]


def lf_perm(N):
    p = [1]
    while len(p) < N:
        m = len(p)
        q = []
        for x in p:
            q += [x, 2 * m + 1 - x]
        p = q
    return p


def lf_steps(P):
    N, L, mu, D = P['N'], P['L'], P['mu'], P['D']
    perm = lf_perm(N)
    return [1 / ((L + mu) / 2 - D / 2 * mp.cos((perm[s] - mp.mpf(1) / 2) * mp.pi / N)) for s in range(N)]


def q_lf(P):
    """q_s(z) = prod_{j<s} (1 - alpha_j lam(z)), lam(z) = (eta - z) Delta/2, as Chebyshev series."""
    N, eta, D = P['N'], P['eta'], P['D']
    al = lf_steps(P)
    Q = [chebT(0)]
    for s in range(1, N):
        prev = Q[-1]
        # multiply prev by (1 - al*(eta - z)*D/2) = (1 - al*eta*D/2) + (al*D/2) z
        c0, c1 = 1 - al[s - 1] * eta * D / 2, al[s - 1] * D / 2
        new = [mp.mpf(0)] * (s + 1)
        for k, c in enumerate(prev):
            new[k] += c0 * c
            if k == 0:
                new[1] += c1 * c
            else:
                new[k + 1] += c1 * c / 2
                new[k - 1] += c1 * c / 2
        Q.append(new)
    return Q


METHODS = dict(Prefix=q_prefix, SineJacobi=q_sinejacobi, LF=q_lf, Flat=q_flat, Balanced=q_balanced)


def grid(M):
    return [mp.cos(mp.pi * k / (M - 1)) for k in range(M)]  # from 1 down to -1
