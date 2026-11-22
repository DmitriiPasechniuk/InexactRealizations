"""Dirichlet Poisson model with FFT-based orthonormal sine transforms."""

import hashlib

import numpy as np
from lowprec import stencil


def dst_axis(x, axis=-1):
    x = np.moveaxis(np.asarray(x), axis, -1)
    n = x.shape[-1]
    extended = np.zeros(x.shape[:-1] + (2 * (n + 1),))
    extended[..., 1 : n + 1] = x
    extended[..., n + 2 :] = -x[..., ::-1]
    result = -np.fft.rfft(extended, axis=-1).imag[..., 1 : n + 1] / np.sqrt(2 * (n + 1))
    return np.moveaxis(result, -1, axis)


def dst2(x):
    """Orthonormal DST-I, equal to its inverse."""
    return dst_axis(dst_axis(x, -1), -2)


def squared_sine_axis(x, axis=-1):
    """Multiply by S_ij^2=(1-cos(2*pi*i*j/(n+1)))/(n+1)."""
    x = np.moveaxis(x, axis, -1)
    n = x.shape[-1]
    padded = np.zeros(x.shape[:-1] + (n + 1,))
    padded[..., 1:] = x
    result = (
        x.sum(axis=-1, keepdims=True) - np.fft.fft(padded, axis=-1).real[..., 1:]
    ) / (n + 1)
    return np.moveaxis(result, -1, axis)


def response_diagonal(spectral_squared):
    """diag(Phi(H)^2) from the squared spectral response, O(n^2 log n)."""
    return squared_sine_axis(squared_sine_axis(spectral_squared, -1), -2)


def terminal_polynomial(c, lam):
    """The identical T_N recurrence, retaining only its two live arrays.

    Simulations need the nominal terminal, while predictions need the full
    responses. Avoid constructing all N query/response arrays for each trial
    configuration. Operation order matches common.responses bit for bit.
    """
    from common import epsilon

    z = (c["L"] + c["mu"] - 2 * np.asarray(lam, dtype=float)) / (c["L"] - c["mu"])
    previous, current = np.ones_like(z), z.copy()
    for _ in range(2, c["N"] + 1):
        previous, current = current, 2 * z * current - previous
    return epsilon(c["N"], c["mu"], c["L"]) * current


def tape_seed(*parts):
    return int.from_bytes(
        hashlib.sha256("|".join(map(str, parts)).encode()).digest()[:8], "little"
    )


class Poisson:
    """H=(4I-neighbours)/8 on n by n interior vertices, zero boundary."""

    def __init__(self, n):
        self.n = n
        t = np.sin(np.arange(1, n + 1) * np.pi / (2 * (n + 1))) ** 2
        self.lam = (t[:, None] + t[None, :]) / 2
        self.mu, self.L = float(self.lam.min()), float(self.lam.max())

    def field(self, seed):
        """Unit smooth field, Gaussian sine coefficients decaying as (j^2+k^2)^-1."""
        rng = np.random.default_rng(seed)
        j = np.arange(1, self.n + 1)
        a = rng.normal(size=(self.n, self.n)) / (j[:, None] ** 2 + j[None, :] ** 2)
        a /= np.linalg.norm(a)
        return dst2(a)

    def apply(self, x):
        return stencil(x)

    def oracle(self, fmt, mode, seed, trial, rhs, hook=None):
        """Tape keyed by trial and call, independent of method and execution order."""

        def evaluate(x, s):
            from lowprec_accel import product

            rng = (
                np.random.default_rng(tape_seed(seed, trial, s))
                if mode == "SR"
                else None
            )
            value = product(x, fmt, mode, rng)
            if hook is not None:
                hook(x, value, s)
            return value - rhs

        return evaluate
