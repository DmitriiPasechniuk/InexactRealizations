"""IEEE-like binary rounding and a fixed-order low-precision Poisson product.

Every input is rounded once. The arithmetic order is 4*y, subtract north,
south, west, east, multiply by 1/8. Each operation is rounded. Multiplication
by powers of two is exact away from underflow/overflow. Coefficients, RHS,
and vector recurrences remain float64. Subnormals use gradual underflow.
"""

import numpy as np

FORMATS = {
    "fp16": (11, -14, 15),
    "bf16": (8, -126, 127),
    "fp32": (24, -126, 127),
    "fp64": (53, -1022, 1023),
}


def spacing(x, fmt):
    p, emin, _ = FORMATS[fmt]
    _, exponent = np.frexp(np.abs(x))
    return np.exp2(np.maximum(exponent - p, emin - p + 1).astype(float))


def round_binary(x, fmt="fp16", mode="RN", rng=None):
    """Round float64 values, with ties to even or independent stochastic draws.

    SR selects adjacent finite representable values with barycentric
    probabilities. Overflow is IEEE RN overflow (infinite outside the
    nearest-even finite range); all production configurations record it.
    """
    x = np.asarray(x, dtype=float)
    if fmt == "fp64":
        return x.copy()
    if mode not in ("RN", "SR"):
        raise ValueError(mode)
    if mode == "RN" and fmt in ("fp16", "fp32"):
        with np.errstate(over="ignore", invalid="ignore"):
            return x.astype(np.float16 if fmt == "fp16" else np.float32).astype(float)
    step = spacing(x, fmt)
    with np.errstate(invalid="ignore", over="ignore"):
        scaled = x / step
        if mode == "RN":
            answer = np.rint(scaled) * step
        else:
            if rng is None:
                raise ValueError("SR requires a random generator.")
            lower = np.floor(scaled)
            answer = (lower + (rng.random(x.shape) < scaled - lower)) * step
        p, _, emax = FORMATS[fmt]
        maximum = (2 - 2.0 ** (1 - p)) * 2.0**emax
        answer = np.where(np.abs(answer) > maximum, np.copysign(np.inf, answer), answer)
    return np.where(np.isfinite(x), answer, x)


def sr_variance(x, fmt):
    """Frozen nominal variance: (x-lower)*(upper-x), in absolute units."""
    if fmt == "fp64":
        return np.zeros_like(x)
    step = spacing(x, fmt)
    fractional = x / step - np.floor(x / step)
    return step * step * fractional * (1 - fractional)


def neighbours(x):
    padded = np.pad(x, [(0, 0)] * (x.ndim - 2) + [(1, 1), (1, 1)])
    return (
        padded[..., :-2, 1:-1],
        padded[..., 2:, 1:-1],
        padded[..., 1:-1, :-2],
        padded[..., 1:-1, 2:],
    )


def stencil(x, fmt="fp64", mode="RN", rng=None):
    q = round_binary(x, fmt, mode, rng)
    value = round_binary(4 * q, fmt, mode, rng)
    for neighbour in neighbours(q):
        value = round_binary(value - neighbour, fmt, mode, rng)
    return round_binary(value * 0.125, fmt, mode, rng)


def frozen_covariance(x, fmt):
    """Return v,d for C=H diag(v) H + diag(d), at the nominal query x.

    Independent input errors are propagated by H. Each scalar arithmetic
    error is propagated by the remaining factor 1/8. The last scaling
    contributes its own variance. This freezes rounding variances at exact
    intermediates; measured nonlinear SR products test this approximation.
    """
    v = sr_variance(x, fmt)
    value = 4 * x
    d = sr_variance(value, fmt)
    for neighbour in neighbours(x):
        value = value - neighbour
        d = d + sr_variance(value, fmt)
    return v, d / 64 + sr_variance(value / 8, fmt)


def product_covariance(x, fmt, samples=32, seed=381):
    """Conditional product covariance at x, using Monte Carlo quadrature.

    C(x)=H diag(v(x)) H+diag(d(x)) exactly: each local arithmetic
    error is conditionally centered, so cross terms vanish even when
    neighboring rows share rounded inputs. v(x) is exact. For d(x) we
    average the conditional rounding variances along sampled arithmetic
    paths. This is a prediction quadrature, before any solver simulation;
    its seed and sample count are part of the saved configuration.
    """
    if x.ndim > 2:
        # Keep one field's arithmetic paths in cache, rather than broadcasting
        # all fields into several large temporary tensors at every operation.
        pairs = [product_covariance(y, fmt, samples, seed + i) for i, y in enumerate(x)]
        return np.array([v for v, _ in pairs]), np.array([d for _, d in pairs])
    rng = np.random.default_rng(seed)
    z = np.broadcast_to(x, (samples,) + x.shape)
    q = round_binary(z, fmt, "SR", rng)
    value = 4 * q
    variance = sr_variance(value, fmt)
    value = round_binary(value, fmt, "SR", rng)
    for neighbour in neighbours(q):
        value = value - neighbour
        variance += sr_variance(value, fmt)
        value = round_binary(value, fmt, "SR", rng)
    variance = variance / 64 + sr_variance(value / 8, fmt)
    return sr_variance(x, fmt), variance.mean(axis=0)
