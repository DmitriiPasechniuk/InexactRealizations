"""Resumable Poisson study; frozen-covariance predictions precede simulations.

Let r be input rounding error and e_j the local scalar arithmetic errors.
To first order, xi=H r + (e_0+...+e_4)/8 + e_5. Thus
C_s=H diag(v_s) H + diag(d_s), with v_s,d_s from product_covariance.
For F_s=Phi_s(H), the terminal noise MSE is
sum_s dot(v_s,diag((H F_s)^2)) + dot(d_s,diag(F_s^2)).
In regime R the nominal query is pi_s(H)x0; in A it is
xstar-pi_s(H)xstar. The stationary additive-floor prediction evaluates
C_s at xstar. Exact bias is added separately. RN energy/gain predictions
are worst-case response quantities; SR predictions describe this stencil.
"""

import hashlib
import json
import os
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path

import numpy as np
from common import SAME_HISTORY, prepare, realized, responses, run
from lowprec import FORMATS, product_covariance
from poisson import Poisson, dst2, response_diagonal, tape_seed, terminal_polynomial

HERE = Path(__file__).resolve().parent
METHODS = ("flat", "balanced", "pref", "lf", "sine")
CONFIG = {
    "version": 2,
    "grids": [64, 128, 256],
    "horizons": [64, 128, 255, 256, 257, 512, 1024],
    "formats": ["fp16", "bf16", "fp32"],
    "modes": ["SR", "RN"],
    "regimes": ["R", "A"],
    "methods": METHODS,
    "sr_fields": [1701, 1702, 1703, 1704],
    "sr_per_field": 64,
    "rn_fields": list(range(2701, 2733)),
    "seed": 20261114,
    "covariance_samples": 8,
    "bootstrap": 500,
}


def timestamp():
    return datetime.now(timezone.utc).isoformat()


def digest(config):
    return hashlib.sha256(json.dumps(config, sort_keys=True).encode()).hexdigest()


def write_json(path, obj):
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(obj, indent=2, allow_nan=False) + "\n")
    tmp.replace(path)


def prediction(problem, c, fmt, regime, field_seeds, covariance_samples=32):
    """Instance prediction, averaged over prespecified smooth fields.

    Spectral responses are computed once; the squared sine transform forms
    the diagonals of F_s^2 and (HF_s)^2 without dense eigenvectors.
    """
    n, N = problem.n, c["N"]
    terminal, query, phi = responses(c, problem.lam.ravel())
    terminal = terminal.reshape(n, n)
    query = query.reshape(N, n, n)
    phi = phi.reshape(N, n, n)
    fields = np.array([problem.field(seed) for seed in field_seeds])
    spectral = dst2(fields)
    stationary = (
        [product_covariance(x, fmt, covariance_samples) for x in fields]
        if regime == "A"
        else None
    )
    bias = float(np.mean(np.sum((spectral * terminal) ** 2, axis=(-2, -1))))
    noise = floor = 0.0
    variance = np.sum(phi**2, axis=0)
    for s in range(N):
        w = response_diagonal(phi[s] ** 2)
        wh = response_diagonal((problem.lam * phi[s]) ** 2)
        nominal = dst2(query[s] * spectral)
        nominal = fields - nominal if regime == "A" else nominal
        v, d = product_covariance(nominal, fmt, covariance_samples, seed=381 + s)
        noise += float(np.mean(np.sum(v * wh + d * w, axis=(-2, -1))))
        if stationary is not None:
            floor += float(np.mean([np.sum(vv * wh + dd * w) for vv, dd in stationary]))
    # Cauchy-Schwarz upper bound for arbitrary operator perturbations. It
    # separates the maxima in the two eigenvalues; labels retain 'bound'.
    operator_bound = float(
        np.sqrt(np.sum(np.max(phi**2, axis=(1, 2)) * np.max(query**2, axis=(1, 2))))
    )
    return {
        "bias": bias,
        "noise": noise,
        "mse": bias + noise,
        "floor": floor if regime == "A" else None,
        "additive_energy": float(np.sqrt(variance.max())),
        "operator_bound": operator_bound,
        "epsilon": float(np.max(np.abs(terminal))),
    }


def configurations(config):
    # Small tasks finish first and yield a usable checkpoint for every grid.
    for N in config["horizons"]:
        for n in config["grids"]:
            for regime in config["regimes"]:
                for fmt in config["formats"]:
                    for mode in config["modes"]:
                        for method in config["methods"]:
                            if method == "lf" and N & (N - 1):
                                continue
                            yield {
                                "n": n,
                                "N": N,
                                "regime": regime,
                                "fmt": fmt,
                                "mode": mode,
                                "method": method,
                            }


def key(row):
    return "_".join(str(row[k]) for k in ("n", "N", "regime", "fmt", "mode", "method"))


def predictions(output=None, config=None):
    output = Path(output or HERE / "results")
    output.mkdir(parents=True, exist_ok=True)
    config = config or CONFIG
    declaration = output / "config_lowprec.json"
    if declaration.exists():
        if json.loads(declaration.read_text())["config_hash"] != digest(config):
            raise ValueError("Declared low-precision configuration differs")
    else:
        write_json(
            declaration,
            {
                "config": config,
                "config_hash": digest(config),
                "declared_utc": timestamp(),
            },
        )
    path = output / "pred_lowprec.json"
    if path.exists():
        stored = json.loads(path.read_text())
        if stored["config_hash"] != digest(config):
            raise ValueError(
                "Prediction configuration differs; use a new output directory."
            )
        return stored
    if config.get("frozen_predictions"):
        rows, source = frozen_rows(config)
        saved = {
            "config": config,
            "config_hash": digest(config),
            "written_utc": timestamp(),
            "formulas": __doc__,
            "prediction_source": source,
            "rows": rows,
        }
        write_json(path, saved)
        print(timestamp(), "FROZEN PREDICTIONS REUSED", source["path"], flush=True)
        return saved
    folder = output / "lowprec_predictions"
    folder.mkdir(exist_ok=True)
    rows = []
    for row in configurations(config):
        if row["mode"] != "SR":
            continue  # RN uses the same deterministic energy response bounds.
        partial = folder / (key(row) + ".json")
        if partial.exists():
            saved = json.loads(partial.read_text())
            if saved["config_hash"] != digest(config):
                raise ValueError("Stale prediction checkpoint.")
            rows.append(saved["row"])
            continue
        p = Poisson(row["n"])
        c = prepare(realized(row["method"], config.get("realization")), row["N"], p.mu, p.L)
        result = dict(
            **row,
            **prediction(
                p,
                c,
                row["fmt"],
                row["regime"],
                config["sr_fields"],
                config["covariance_samples"],
            ),
        )
        rows.append(result)
        write_json(partial, {"config_hash": digest(config), "row": result})
        print(timestamp(), "predicted", key(row), flush=True)
    saved = {
        "config": config,
        "config_hash": digest(config),
        "written_utc": timestamp(),
        "formulas": __doc__,
        "rows": rows,
    }
    write_json(path, saved)
    print(timestamp(), "FINAL PREDICTIONS WRITTEN", path, flush=True)
    return saved


def same_history_check(config, points=513):
    """Largest relative difference of p, queries and responses, realization vs label.

    Responses are polynomials of degree at most N; they are compared at the
    extreme Poisson eigenvalues and Chebyshev points of [mu, L].
    """
    worst = 0.0
    for method in config["methods"]:
        code = realized(method, config.get("realization"))
        if code == method:
            continue
        if SAME_HISTORY.get(code) != method:
            raise ValueError(f"{code} does not realize the {method} history")
        for n in config["grids"]:
            p = Poisson(n)
            lam = (p.L + p.mu) / 2 - (p.L - p.mu) / 2 * np.cos(np.linspace(0, np.pi, points))
            for N in config["horizons"]:
                ours = responses(prepare(code, N, p.mu, p.L), lam)
                base = responses(prepare(method, N, p.mu, p.L), lam)
                for a, b in zip(ours, base):
                    worst = max(worst, float(np.max(np.abs(a - b)) / np.max(np.abs(b))))
    return worst


def frozen_rows(config):
    """Reuse frozen predictions of the same histories (no prediction recomputation).

    The realization changes only the executed code: the source predictions are
    functions of the history's responses, which are checked to agree.
    """
    path = HERE / config["frozen_predictions"]
    stored = json.loads(path.read_text())
    if stored["config_hash"] != config["frozen_predictions_hash"]:
        raise ValueError("Frozen prediction source differs from the declared hash.")
    for k in ("sr_fields", "covariance_samples", "version"):
        if stored["config"][k] != config[k]:
            raise ValueError(f"Frozen predictions use a different {k}.")
    worst = same_history_check(config)
    if worst > 1e-12:
        raise ValueError(f"Realization responses differ from the frozen history: {worst:.3g}")
    index = {key(r): r for r in stored["rows"]}
    rows = []
    for row in configurations(config):
        if row["mode"] == "SR":
            if key(row) not in index:
                raise ValueError(f"No frozen prediction for {key(row)}.")
            rows.append(index[key(row)])
    source = {"path": config["frozen_predictions"], "config_hash": stored["config_hash"],
              "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
              "max_relative_response_difference": worst}
    return rows, source


def simulate_one(row, config):
    p = Poisson(row["n"])
    c = prepare(realized(row["method"], config.get("realization")), row["N"], p.mu, p.L)
    fields = config["sr_fields"] if row["mode"] == "SR" else config["rn_fields"]
    repeats = config["sr_per_field"] if row["mode"] == "SR" else 1
    terminal = terminal_polynomial(c, p.lam)
    errors, excesses, means, ids, nonfinite = [], [], [], [], []
    diagnostic = {
        "calls": 0,
        "subnormal_inputs": 0,
        "input_components": 0,
        "zero_products": 0,
        "product_components": 0,
        "max_product_relative_error": 0.0,
    }

    def observe(x, value, s):
        exact = p.apply(x)
        norm = np.linalg.norm(exact)
        diagnostic["calls"] += 1
        diagnostic["input_components"] += x.size
        diagnostic["product_components"] += value.size
        tiny = 2.0 ** FORMATS[row["fmt"]][1]
        diagnostic["subnormal_inputs"] += int(np.sum((abs(x) < tiny) & (x != 0)))
        diagnostic["zero_products"] += int(np.sum(value == 0))
        if norm and np.isfinite(value).all():
            diagnostic["max_product_relative_error"] = max(
                diagnostic["max_product_relative_error"],
                float(np.linalg.norm(value - exact) / norm),
            )

    started = time.monotonic()
    for field in fields:
        smooth = p.field(field)
        star = smooth if row["regime"] == "A" else np.zeros_like(smooth)
        x0 = np.zeros_like(smooth) if row["regime"] == "A" else smooth
        nominal = star + dst2(terminal * dst2(x0 - star))
        rhs = p.apply(star)
        for repeat in range(repeats):
            trial = tape_seed(field, repeat)
            oracle = p.oracle(
                row["fmt"],
                row["mode"],
                config["seed"],
                trial,
                rhs,
                hook=observe if repeat == 0 else None,
            )
            with np.errstate(over="ignore", invalid="ignore"):
                result = run(c, x0, oracle)
            finite = bool(np.isfinite(result).all())
            # Retain all trials. JSON carries a failure count; NPZ retains inf.
            errors.append(float(np.sum((result - star) ** 2)) if finite else np.inf)
            excesses.append(
                float(np.sum((result - nominal) ** 2)) if finite else np.inf
            )
            means.append(float(np.linalg.norm(nominal - star)))
            ids.append(trial)
            nonfinite.append(not finite)
    return {
        "error": np.array(errors),
        "excess": np.array(excesses),
        "bias_norm": np.array(means),
        "trial": np.array(ids, dtype=np.uint64),
        "nonfinite": np.array(nonfinite),
        "seconds": np.array(time.monotonic() - started),
        **{f"diagnostic_{k}": np.array(v) for k, v in diagnostic.items()},
    }


def experiment(output=None, config=None, workers=None):
    output = Path(output or HERE / "results")
    config = config or CONFIG
    workers = (
        int(os.environ.get("LOWPREC_WORKERS", "1")) if workers is None else workers
    )
    if workers < 1:
        raise ValueError("At least one worker is required")
    is_final = output == HERE / "results"
    if is_final:
        write_json(
            output / "lowprec_run_state.json",
            {"phase": "predictions running", "utc": timestamp()},
        )
    pred = predictions(output, config)
    if is_final:
        write_json(
            output / "lowprec_run_state.json",
            {"phase": "simulations running", "utc": timestamp()},
        )
    folder = output / "lowprec_checkpoints"
    folder.mkdir(exist_ok=True)
    print(timestamp(), "START/RESUME", digest(config), flush=True)
    pending = []
    for row in configurations(config):
        path = folder / (key(row) + ".npz")
        if path.exists():
            with np.load(path, allow_pickle=False) as data:
                if str(data["config_hash"]) != pred["config_hash"]:
                    raise ValueError("Stale simulation checkpoint.")
        else:
            pending.append(row)

    def save(row, data):
        path = folder / (key(row) + ".npz")
        tmp = path.with_suffix(".tmp.npz")
        np.savez_compressed(tmp, **data, config_hash=pred["config_hash"])
        tmp.replace(path)
        print(
            timestamp(),
            "measured",
            key(row),
            f"{float(data['seconds']):.3f}s",
            flush=True,
        )

    print(timestamp(), "SIMULATION WORKERS", workers, flush=True)
    if workers == 1:
        for row in pending:
            save(row, simulate_one(row, config))
    elif pending:
        with ProcessPoolExecutor(max_workers=workers) as executor:
            futures = {
                executor.submit(simulate_one, row, config): row for row in pending
            }
            for future in as_completed(futures):
                save(futures[future], future.result())

    # Canonical order makes outputs independent of scheduling and worker count.
    records = []
    for row in configurations(config):
        path = folder / (key(row) + ".npz")
        with np.load(path, allow_pickle=False) as data:
            records.append((row, {k: data[k].copy() for k in data.files}))
    # Ragged RN/SR sample counts are padded with NaN, with lengths saved.
    arrays = {k: np.array([r[k] for r, _ in records]) for k in records[0][0]}
    lengths = [len(d["error"]) for _, d in records]
    arrays["trials"] = np.array(lengths)
    for field in ("error", "excess", "bias_norm"):
        a = np.full((len(records), max(lengths)), np.nan)
        for i, (_, data) in enumerate(records):
            a[i, : lengths[i]] = data[field]
        arrays[field] = a
    arrays["config_hash"] = np.array(pred["config_hash"])
    for field in records[0][1]:
        if field.startswith("diagnostic_"):
            arrays[field] = np.array([d[field] for _, d in records])
    np.savez_compressed(output / "raw_lowprec.npz", **arrays)
    from analyze import analyze_lowprec
    from plots import build_lowprec

    analyze_lowprec(output)
    build_lowprec(
        output, HERE / "figures" if output == HERE / "results" else output / "figures"
    )
    if is_final:
        write_json(output / "lowprec_run_state.json", {"phase": "float64 controls", "utc": timestamp()})
        from lowprec_diagnostics import diagnose

        diagnose(output)
        from lowprec_regimes import render as render_regimes

        render_regimes(output, HERE / "figures")
        write_json(
            output / "lowprec_done.json",
            {"config_hash": pred["config_hash"], "utc": timestamp()},
        )
        write_json(
            output / "lowprec_run_state.json", {"phase": "complete", "utc": timestamp()}
        )
        from lowprec_report import update

        update()
    print(timestamp(), "COMPLETE", flush=True)


def pilot(output=None):
    config = dict(
        CONFIG,
        grids=[8],
        horizons=[8, 16, 32, 64],
        formats=["fp16", "bf16"],
        sr_fields=[1701],
        sr_per_field=16,
        rn_fields=list(range(2701, 2705)),
        covariance_samples=32,
    )
    experiment(output or HERE / f"results/lowprec_pilot_v{CONFIG['version']}", config)


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("kind", choices=("pred", "run", "resume", "pilot", "status"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--workers", type=int)
    args = parser.parse_args()
    if args.kind == "pilot":
        pilot(args.output)
    elif args.kind == "pred":
        predictions(args.output)
    elif args.kind == "status":
        output = args.output or HERE / "results"
        print(
            "Prediction checkpoints:",
            len(list((output / "lowprec_predictions").glob("*.json"))),
        )
        print(
            "Simulation checkpoints:",
            len(list((output / "lowprec_checkpoints").glob("*.npz"))),
        )
        print("Expected final configurations:", len(list(configurations(CONFIG))))
    else:
        experiment(args.output, workers=args.workers)
