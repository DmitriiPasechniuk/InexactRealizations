"""LF/fractal relative gains (gamma = 2 and gamma = inf) with local refinement, in z-variables.
Root steps alpha_j = 2/(Delta (eta - zeta_j)), zeta_j = cos((perm_j - 1/2) pi/N): the normalized kernel is
 Delta K_s/(4 eps) = -F_s(x) Q_s(y),  F_s = 2^(N-1-s) prod_{j>s}(x - zeta_j),  Q_s = 2^(s-1) prod_{j<s}(y - zeta_j),
so relative ratios are kappa-independent; D_N <-> N^2/2, G_N <-> N^{3/2} sigma_N/2.
gamma = 2: max_{x,y} sum_s F_s(x)^2 Q_s(y)^2 (exact point-pair value), grid + golden refinement.
gamma = inf: sup over probability measures of sum_s ||F_s||_al ||Q_s||_be (jointly concave): Frank-Wolfe on a
grid augmented with refined local maximizers; FW gap gives a certificate on that grid.
Also additive check: positive peak of LF responses (max_x |F_s(x)| = |F_s(1)|) with refinement."""
import sys
import numpy as np
from budgets_lib import lf_perm

def setup(N):
    perm = np.array(lf_perm(N)[:N])
    zeta = np.cos((perm - 0.5) * np.pi / N)
    return zeta

def logs(N, zeta, x):
    # returns log|F_s(x)|, sign F_s(x), log|Q_s(x)|, sign Q_s(x) for array x  (shape len(x) x N)
    d = x[:, None] - zeta[None, :]
    la, sg = np.log(np.abs(d)), np.sign(d)
    s = np.arange(N)
    cla = np.concatenate([np.zeros((len(x), 1)), np.cumsum(la, 1)[:, :-1]], 1)       # sum_{j<s}
    csg = np.concatenate([np.ones((len(x), 1)), np.cumprod(sg, 1)[:, :-1]], 1)
    rla = np.concatenate([np.cumsum(la[:, ::-1], 1)[:, ::-1][:, 1:], np.zeros((len(x), 1))], 1)  # sum_{j>s}
    rsg = np.concatenate([np.cumprod(sg[:, ::-1], 1)[:, ::-1][:, 1:], np.ones((len(x), 1))], 1)
    lF = (N - 1 - s)[None, :] * np.log(2) + rla
    lQ = (s - 1)[None, :] * np.log(2) + cla
    return lF, rsg, lQ, csg

def golden(f, a, b, it=80):
    g = (np.sqrt(5) - 1) / 2
    c, d = b - g * (b - a), a + g * (b - a)
    fc, fd = f(c), f(d)
    for _ in range(it):
        if fc > fd:
            b, d, fd = d, c, fc
            c = b - g * (b - a); fc = f(c)
        else:
            a, c, fc = c, d, fd
            d = a + g * (b - a); fd = f(d)
    return (a + b) / 2

def run(N, M):
    zeta = setup(N)
    t = np.linspace(0, np.pi, M)
    x = np.cos(t)
    lF, sF, lQ, sQ = logs(N, zeta, x)
    F2, Q2 = np.exp(2 * lF), np.exp(2 * lQ)            # M x N
    sig = np.sqrt(1 + ((N - 1) / ((N + 1) * N * N) if N % 2 else 0))
    DNn, GNn = N * N / 2, N ** 1.5 * sig / 2
    # additive: positive peak of responses
    Fbar = np.sqrt(F2.max(0))
    print(f'  N={N} M={M}: max log|F| {np.nanmax(lF):.1f}, max log|Q| {np.nanmax(lQ):.1f}, finite F2 {np.isfinite(F2).all()}, finite Q2 {np.isfinite(Q2).all()}')
    F1 = np.exp(lF[0])
    # refine each s: local max near grid argmax
    dev = 0.0
    for s in range(N):
        i = np.argmax(F2[:, s])
        if i == 0:
            continue
        a, b = t[max(i - 1, 0)], t[min(i + 1, M - 1)]
        f = lambda tt: np.exp(2 * logs(N, zeta, np.array([np.cos(tt)]))[0][0, s])
        tt = golden(f, a, b)
        dev = max(dev, np.sqrt(f(tt)) / F1[s] - 1)
    # gamma = 2
    E = F2 @ Q2.T                                     # E[i,j] = sum_s F_s(x_i)^2 Q_s(x_j)^2
    i, j = np.unravel_index(np.argmax(E), E.shape)
    ti, tj = t[i], t[j]
    def Exy(a, b):
        lf, _, _, _ = logs(N, zeta, np.array([np.cos(a)]))
        _, _, lq, _ = logs(N, zeta, np.array([np.cos(b)]))
        return np.sum(np.exp(2 * lf[0] + 2 * lq[0]))
    h = np.pi / (M - 1)
    for _ in range(6):
        ti = golden(lambda a: Exy(a, tj), max(ti - 2 * h, 0), min(ti + 2 * h, np.pi))
        tj = golden(lambda b: Exy(ti, b), max(tj - 2 * h, 0), min(tj + 2 * h, np.pi))
    rel2 = np.sqrt(Exy(ti, tj)) / GNn
    # gamma = inf: FW on grid (point-pair start), then report
    A, B = F2.T, Q2.T                                 # N x M
    S = np.sqrt(F2) @ np.sqrt(Q2).T                   # M x M point-pair values sum_s |F_s(x)||Q_s(y)|
    i, j = np.unravel_index(np.argmax(S), S.shape)
    pp = S[i, j]
    # refine the point pair continuously
    def Pxy(a, b):
        lf, _, _, _ = logs(N, zeta, np.array([np.cos(a)]))
        _, _, lq, _ = logs(N, zeta, np.array([np.cos(b)]))
        return np.sum(np.exp(lf[0] + lq[0]))
    ti2, tj2 = t[i], t[j]
    for _ in range(6):
        ti2 = golden(lambda a: Pxy(a, tj2), max(ti2 - 2 * h, 0), min(ti2 + 2 * h, np.pi))
        tj2 = golden(lambda b: Pxy(ti2, b), max(tj2 - 2 * h, 0), min(tj2 + 2 * h, np.pi))
    pp_ref = Pxy(ti2, tj2)
    al = np.zeros(M); al[i] = 1
    be = np.zeros(M); be[j] = 1
    val = lambda al, be: np.sum(np.sqrt((A @ al) * (B @ be)))
    best, ub = pp, np.inf
    for k in range(3000):
        a, c = A @ al, B @ be
        ga = A.T @ (0.5 * np.sqrt(c / a)); gb = B.T @ (0.5 * np.sqrt(a / c))
        ia, ib = np.argmax(ga), np.argmax(gb)
        v = val(al, be)
        gap = (ga[ia] - ga @ al) + (gb[ib] - gb @ be)
        ub = min(ub, v + gap); best = max(best, v)
        if gap <= 1e-10 * v:
            break
        da = -al.copy(); da[ia] += 1
        db = -be.copy(); db[ib] += 1
        tt = golden(lambda s_: val(al + s_ * da, be + s_ * db), 0.0, 1.0, it=50)
        al, be = al + tt * da, be + tt * db
    print(f'N={N} M={M}: resp. positive-peak dev (refined) {dev:.2e}; rel2 point-pair refined {rel2:.6f} '
          f'(grid {np.sqrt(E.max())/GNn:.6f}); relinf point-pair grid {pp/DNn:.6f}, refined {pp_ref/DNn:.6f}, '
          f'FW best {best/DNn:.6f}, FW certified grid upper {ub/DNn:.6f} ({k+1} it)')
    sys.stdout.flush()

if __name__ == '__main__':
    for N, Ms in [(64, [1601, 4001]), (1024, [4001, 8001])]:
        for M in Ms:
            run(N, M)
