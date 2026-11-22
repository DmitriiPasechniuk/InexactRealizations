"""Optional compiler acceleration; NumPy remains the portable reference.

The C kernel consumes NumPy PCG64's own next_double function in exactly the
same operation-major order. The power-of-two operation's unused random slot
is skipped by advance, and subsequent seeds remain independent per call.
Compiler flags preserve binary64 operation order. A missing compiler selects
the reference; no package is installed. Only 2-D products use this backend.
"""

import ctypes
import hashlib
import os
import shutil
import subprocess
import sys
import tempfile
from functools import lru_cache
from pathlib import Path

import numpy as np
from lowprec import FORMATS, stencil


@lru_cache(maxsize=1)
def library():
    compiler = shutil.which("cc")
    if not compiler:
        return None
    source = Path(__file__).with_name("lowprec_native.c")
    flags = ["-O3", "-std=c11", "-fno-fast-math", "-ffp-contract=off"]
    identity = hashlib.sha256(
        source.read_bytes() + " ".join(flags).encode()
    ).hexdigest()
    folder = Path(tempfile.gettempdir()) / "bezout-lowprec-native" / identity
    target = folder / ("kernel.dylib" if sys.platform == "darwin" else "kernel.so")
    if not target.exists():
        folder.mkdir(parents=True, exist_ok=True)
        temporary = folder / f"build-{os.getpid()}{target.suffix}"
        command = [
            compiler,
            *flags,
            "-dynamiclib" if sys.platform == "darwin" else "-shared",
            "-fPIC",
            str(source),
            "-o",
            str(temporary),
            "-lm",
        ]
        subprocess.run(command, check=True, capture_output=True)
        temporary.replace(target)
    lib = ctypes.CDLL(str(target))
    ptr = ctypes.c_void_p
    lib.lp_inputs.argtypes = [
        ptr,
        ptr,
        ptr,
        ctypes.c_size_t,
        ctypes.c_int,
        ctypes.c_int,
        ctypes.c_int,
        ctypes.c_int,
        ptr,
        ptr,
    ]
    lib.lp_finish.argtypes = [
        ptr,
        ptr,
        ptr,
        ctypes.c_size_t,
        ctypes.c_int,
        ctypes.c_int,
        ctypes.c_int,
        ctypes.c_int,
        ptr,
        ptr,
    ]
    lib.lp_inputs.restype = None
    lib.lp_finish.restype = ctypes.c_int
    return lib


def product(x, fmt="fp64", mode="RN", rng=None):
    x = np.asarray(x, dtype=float)
    if (
        x.ndim != 2
        or x.shape[0] != x.shape[1]
        or fmt == "fp64"
        or mode not in ("RN", "SR")
        or (
            mode == "SR"
            and (
                rng is None
                or not isinstance(getattr(rng, "bit_generator", None), np.random.PCG64)
            )
        )
    ):
        return stencil(x, fmt, mode, rng)
    lib = library()
    if lib is None:
        return stencil(x, fmt, mode, rng)
    x = np.ascontiguousarray(x)
    q, v, out = np.empty_like(x), np.empty_like(x), np.empty_like(x)
    state = callback = None
    if mode == "SR":
        info = rng.bit_generator.ctypes
        state = info.state
        callback = ctypes.cast(info.next_double, ctypes.c_void_p)
    p, emin, emax = FORMATS[fmt]
    lib.lp_inputs(
        x.ctypes.data,
        q.ctypes.data,
        v.ctypes.data,
        x.size,
        p,
        emin,
        emax,
        mode == "SR",
        state,
        callback,
    )
    if mode == "SR":
        rng.bit_generator.advance(x.size)
    final_draws = lib.lp_finish(
        q.ctypes.data,
        v.ctypes.data,
        out.ctypes.data,
        x.shape[0],
        p,
        emin,
        emax,
        mode == "SR",
        state,
        callback,
    )
    if mode == "SR" and not final_draws:
        rng.bit_generator.advance(x.size)
    return out
