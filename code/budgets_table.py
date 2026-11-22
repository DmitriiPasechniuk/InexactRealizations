"""Decision table (Theorem budgets): ratios to the optimum for gamma in {inf, 2}, additive (noise coefficient,
r = 0) and relative / operator-norm variation.  Closed forms for the positive-peak histories (Prefix,
sine-Jacobi, Balanced) and for Flat (responses peak at mu, queries at L with the closed form of |q_s(-1)|);
LF/fractal on a grid (float64 log-products) with a Frank-Wolfe certificate for the gamma = inf relative value
(jointly concave objective)."""
import sys
import mpmath as mp
import numpy as np
from budgets_lib import params, flat_data, balanced_omega, sj_leading, cheb_eval, lf_steps

mp.mp.dps = 80


def closed(P):
    N, eps, D, S, DN, GN, eta, C = P['N'], P['eps'], P['D'], P['S'], P['DN'], P['GN'], P['eta'], P['C']
    k = 4 * eps / D
    res = {}
    # Prefix
    f1 = [mp.mpf(N) / 2] + [C[s] * (N - s) for s in range(1, N)]
    q1 = [1 / C[s] for s in range(N)]
    res['Prefix'] = ([k * x for x in f1], q1)
    # sine-Jacobi via PartI Thm 5.1, 5.2 and persymmetry Q^{(s+1)}_{N-s-1} = P_{N-s-1}
    a2 = [None] + [mp.sin(mp.pi * s / N) ** 2 / (4 * mp.sin(mp.pi * (s - mp.mpf(1) / 2) / N)
                                                 * mp.sin(mp.pi * (s + mp.mpf(1) / 2) / N)) for s in range(1, N)]
    Pe, P1 = [mp.mpf(1), eta], [mp.mpf(1), mp.mpf(1)]
    for s in range(1, N):
        Pe.append(eta * Pe[-1] - a2[s] * Pe[-2])
        P1.append(P1[-1] - a2[s] * P1[-2])
    res['SineJacobi'] = ([(2 / D) * Pe[s] * P1[N - s - 1] / Pe[N] for s in range(N)], [P1[s] / Pe[s] for s in range(N)])
    # Balanced
    om = balanced_omega(N)
    Z = [mp.mpf(1), eta]
    for s in range(2, N):
        Z.append(Z[s - 2] + om[s] * (C[s] - C[s - 2]))
    if N % 2 == 0:
        mbar = [mp.mpf(N) / 2] * 2
    else:
        mbar = [mp.mpf(N * N + 1) / (2 * (N + 1)), mp.mpf(N + 1) / 2]
    res['Balanced'] = ([k * Z[s] * mbar[s % 2] for s in range(N)], [1 / Z[s] for s in range(N)])
    # Flat
    u, a, M, d, R, tau = flat_data(P)
    qm1 = [(1 + tau[s]) * (s + 1) / u[s] + (tau[s] * s / u[s - 1] if s else 0) for s in range(N)]
    res['Flat'] = ([S / N] * N, qm1)
    return res


def ratios_closed(P, Pb, Qb, flat=False):
    N, S, DN, GN = P['N'], P['S'], P['DN'], P['GN']
    add_inf = sum(Pb) / S
    add_2 = mp.sqrt(sum(x * x for x in Pb)) / (S / mp.sqrt(N))
    prod = [x * y for x, y in zip(Pb, Qb)]
    rel_inf = sum(prod) / DN
    rel_2 = mp.sqrt(sum(x * x for x in prod)) / GN
    return add_inf, add_2, rel_inf, rel_2


def lf_grid(P, M):
    N, eta, D = P['N'], P['eta'], P['D']
    al = np.array([float(a) for a in lf_steps(P)])
    z = np.cos(np.pi * np.arange(M) / (M - 1))
    lam = (float(eta) - z) * float(D) / 2
    fac = 1 - al[None, :] * lam[:, None]          # M x N
    la, sg = np.log(np.abs(fac)), np.sign(fac)
    # pi_s = prod_{j<s}, Phi_s = -al_s prod_{j>s}
    cla = np.concatenate([np.zeros((M, 1)), np.cumsum(la, 1)[:, :-1]], 1)
    csg = np.concatenate([np.ones((M, 1)), np.cumprod(sg, 1)[:, :-1]], 1)
    rla = np.concatenate([np.cumsum(la[:, ::-1], 1)[:, ::-1][:, 1:], np.zeros((M, 1))], 1)
    rsg = np.concatenate([np.cumprod(sg[:, ::-1], 1)[:, ::-1][:, 1:], np.ones((M, 1))], 1)
    pi = csg * np.exp(cla)
    Phi = -al[None, :] * rsg * np.exp(rla)
    return lam, Phi, pi


def fw_rel_inf(A, B, iters=4000):
    """max over probability vectors al, be of sum_s sqrt((A al)_s (B be)_s); A, B: N x M nonneg.
    Jointly concave.  Returns best value, certified upper bound (value + FW gap), start value."""
    E = np.sqrt(A).T @ np.sqrt(B)                       # point pairs: sum_s |Phi_s(l)||pi_s(n)|
    i, j = np.unravel_index(np.argmax(E), E.shape)
    al = np.zeros(A.shape[1]); al[i] = 1
    be = np.zeros(B.shape[1]); be[j] = 1
    start = E[i, j]

    def val(al, be):
        return np.sum(np.sqrt(np.maximum(A @ al, 0) * np.maximum(B @ be, 0)))
    best, ub = start, np.inf
    for k in range(iters):
        a, c = A @ al, B @ be
        ga = A.T @ (0.5 * np.sqrt(c / a))
        gb = B.T @ (0.5 * np.sqrt(a / c))
        ia, ib = np.argmax(ga), np.argmax(gb)
        gap = (ga[ia] - ga @ al) + (gb[ib] - gb @ be)
        v = val(al, be)
        ub = min(ub, v + gap)
        best = max(best, v)
        if gap <= 1e-12 * v:
            break
        da = -al.copy(); da[ia] += 1
        db = -be.copy(); db[ib] += 1
        lo, hi = 0.0, 1.0
        for _ in range(60):  # golden-section line search on concave function
            m1, m2 = lo + (hi - lo) * 0.382, lo + (hi - lo) * 0.618
            if val(al + m1 * da, be + m1 * db) < val(al + m2 * da, be + m2 * db):
                lo = m1
            else:
                hi = m2
        t = (lo + hi) / 2
        al, be = al + t * da, be + t * db
    return best, ub, start


def lf_ratios(P, M):
    N, S, DN, GN = P['N'], float(P['S']), float(P['DN']), float(P['GN'])
    lam, Phi, pi = lf_grid(P, M)
    Pb = np.abs(Phi).max(0)
    add_inf_hi = Pb.sum() / S
    add_inf_lo = abs(Phi[0, :].sum()) / S   # z = 1 is lam = mu (first grid point)
    peak_dev = np.max(Pb / np.abs(Phi[0, :]) - 1)
    add_2 = np.sqrt((Phi ** 2).sum(1)).max() / (S / np.sqrt(N))
    A, B = (Phi ** 2).T, (pi ** 2).T                   # N x M
    E = A.T @ B
    rel_2 = np.sqrt(E.max()) / GN
    best, ub, start = fw_rel_inf(A, B)
    return dict(add_inf=(add_inf_lo, add_inf_hi, peak_dev), add_2=add_2, rel_2=rel_2,
                rel_inf=(start / DN, best / DN, ub / DN))


if __name__ == '__main__':
    configs = [(100, 64), (10000, 1024), (100, 1024), (10000, 64)]
    for kappa, N in configs:
        P = params(N, kappa)
        print(f'=== kappa={kappa} N={N}   eps={mp.nstr(P["eps"],6)}  S_N/(N D_N)={mp.nstr(P["S"]/(N*P["DN"]),6)}')
        res = closed(P)
        for name in ['Prefix', 'SineJacobi', 'Balanced', 'Flat']:
            r = ratios_closed(P, *res[name])
            print(f'  {name:10s} add_inf={mp.nstr(r[0],8)} add_2={mp.nstr(r[1],6)} rel_inf={mp.nstr(r[2],6)} rel_2={mp.nstr(r[3],6)}')
        for M in ([801, 1601] if N == 64 else [1201, 2401]):
            r = lf_ratios(P, M)
            print(f'  LF (grid M={M}) add_inf in [{r["add_inf"][0]:.8f},{r["add_inf"][1]:.8f}] (resp. peak dev {r["add_inf"][2]:.2e})'
                  f' add_2={r["add_2"]:.6g} rel_2={r["rel_2"]:.6g} rel_inf: point-pair {r["rel_inf"][0]:.6g},'
                  f' FW best {r["rel_inf"][1]:.6g}, certified (grid) upper {r["rel_inf"][2]:.6g}')
        sys.stdout.flush()
