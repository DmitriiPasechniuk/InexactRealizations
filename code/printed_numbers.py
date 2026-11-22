"""Theory numbers printed in the article that no other stage produces.

python printed_numbers.py > results/printed_numbers.txt

Sections 1 and 4: the gain constants on the scale eps_N N^{3/2}/Delta (Prefix 4/sqrt3, sine-Jacobi
extrapolated in 1/N, Balanced 2) and Balanced's reductions of the Prefix and sine-Jacobi gains.
Section 6: sqrt(kappa) of the three Poisson grids; the dither variances h^2/12 and Gamma; and, for the
uniform spectral distribution with the kappa of each Poisson grid, the lower bound of Theorem 5.3(b) for
additively optimal histories over the Prefix value of Theorem 5.3(a), at the Poisson horizons.
"""

import math

import numpy as np

from common import epsilon, prepare, responses

POISSON_GRIDS = (64, 128, 256)
POISSON_HORIZONS = (64, 128, 255, 256, 257, 512, 1024)


def constant(method, N, mu=1e-8, L=1.0):
    """sqrt(sum_s K_s(mu,mu)^2) on the scale eps_N N^{3/2}/Delta."""
    _, q, phi = responses(prepare(method, N, mu, L), np.array([mu]))
    gain = math.sqrt(float(np.sum((phi[:, 0] * q[:, 0]) ** 2)))
    return gain / (epsilon(N, mu, L) * N**1.5 / (L - mu))


def extrapolated(values):
    """Aitken extrapolation of three values at N, 2N, 4N."""
    a, b, c = values
    return c - (c - b) ** 2 / ((c - b) - (b - a))


def uniform_ratio(kappa, N):
    """Theorem 5.3(b) lower bound (S_N/N)^2 sum_{k<N} (k+1)^{-2} over the Prefix value of Theorem 5.3(a)."""
    mu, L = 1 / kappa, 1.0
    delta = L - mu
    theta = math.acosh((L + mu) / delta)
    eps = 1 / math.cosh(N * theta)
    h = np.cumsum(1 / (2 * np.arange(1, N + 1) - 1))  # h[k-1] = h_k
    k = np.arange(1, N)
    prefix = 16 * eps**2 / delta**2 * (h[N - 1] / 4 + np.sum(np.cosh((N - k) * theta) ** 2 * h[k - 1]))
    S = (1 - eps) / mu
    bound = (S / N) ** 2 * np.sum(1 / np.arange(1, N + 1) ** 2)
    return bound / prefix


def main():
    prefix = 4 / math.sqrt(3)
    sine = extrapolated([constant("sine", N) for N in (1024, 2048, 4096)])
    print("Gain constants on the scale eps_N N^{3/2}/Delta (Sections 1 and 4)")
    print(f"  Prefix 4/sqrt3 = {prefix:.9f}; at N=1024: {constant('pref', 1024):.9f}")
    print(f"  sine-Jacobi, extrapolated from N=1024,2048,4096: {sine:.9f}")
    print(f"  Balanced at N=1024: {constant('balanced', 1024):.12f}")
    print(f"  Balanced reduces the Prefix gain by {100 * (1 - 2 / prefix):.4f} %"
          f" and the sine-Jacobi gain by {100 * (1 - 2 / sine):.4f} %")
    print("\nPoisson grids (Section 6): sqrt(kappa) = cot(pi/(2(n+1)))")
    for n in POISSON_GRIDS:
        print(f"  {n}x{n}: sqrt(kappa) = {1 / math.tan(math.pi / (2 * (n + 1))):.4f}")
    print("\nSubtractive dither (Section 6, Appendix F), h = sqrt(3)/2 sigma:")
    print(f"  h^2/12 = {(math.sqrt(3) / 2) ** 2 / 12:.6f} sigma^2 (1/16 = {1 / 16:.6f});"
          f" Gamma over four workers = {(math.sqrt(3) / 2) ** 2 / 48:.6f} sigma^2 I (1/64 = {1 / 64:.6f})")
    print("\nUniform spectrum with the kappa of each Poisson grid: Theorem 5.3(b) bound / Prefix (Theorem 5.3(a))")
    for n in POISSON_GRIDS:
        kappa = 1 / math.tan(math.pi / (2 * (n + 1))) ** 2
        ratios = {N: uniform_ratio(kappa, N) for N in POISSON_HORIZONS}
        above = [N for N, r in ratios.items() if r > 1]
        print(f"  {n}x{n} (kappa = {kappa:.1f}): "
              + ", ".join(f"N={N}: {r:.3f}" for N, r in ratios.items())
              + f"; bound above Prefix exactly at N in {above}")


if __name__ == "__main__":
    main()
