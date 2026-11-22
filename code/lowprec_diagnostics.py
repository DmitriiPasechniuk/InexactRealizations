"""Float64 controls for deep-horizon low-precision realization errors.

These post-sweep diagnostics retain the frozen low-precision predictions and
samples. They replay the same four SR fields with float64 stencil products,
coefficients and vector updates, and measure departure from the nominal
Chebyshev terminal. This control includes coefficient and realization
arithmetic; its ratio to measured noise is a diagnostic, not a subtraction
or an additive decomposition of the low-precision result.
"""

import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

import numpy as np
from common import NAME, prepare, realized, run
from poisson import Poisson, dst2, terminal_polynomial

HERE = Path(__file__).resolve().parent


def write(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n")
    temporary.replace(path)


def key(row):
    return "_".join(str(row[k]) for k in ("n", "N", "regime", "method"))


def configuration(summary):
    base = summary["config"]
    horizons = [N for N in (256, 512, 1024) if N in base["horizons"]]
    config = {"base_hash": summary["config_hash"], "grids": base["grids"],
              "horizons": horizons or [max(base["horizons"])],
              "regimes": base["regimes"], "methods": base["methods"],
              "fields": base["sr_fields"], "arithmetic": "float64 stencil and realization",
              "reason": __doc__}
    if base.get("realization"):  # absent for the original study: its hash is unchanged
        config["realization"] = base["realization"]
    return config


def jobs(config):
    for n in config["grids"]:
        for N in config["horizons"]:
            for regime in config["regimes"]:
                for method in config["methods"]:
                    if method != "lf" or N & (N - 1) == 0:
                        yield {"n": n, "N": N, "regime": regime, "method": method}


def compute(row, fields, realization=None):
    p = Poisson(row["n"])
    c = prepare(realized(row["method"], realization), row["N"], p.mu, p.L)
    terminal = terminal_polynomial(c, p.lam)
    errors, excesses = [], []
    for field in fields:
        smooth = p.field(field)
        star = smooth if row["regime"] == "A" else np.zeros_like(smooth)
        x0 = np.zeros_like(smooth) if row["regime"] == "A" else smooth
        nominal = star + dst2(terminal * dst2(x0 - star))
        rhs = p.apply(star)
        result = run(c, x0, lambda x, s, rhs=rhs: p.apply(x) - rhs)
        errors.append(float(np.sum((result - star) ** 2)))
        excesses.append(float(np.sum((result - nominal) ** 2)))
    return {**row, "fields": fields, "field_errors": errors, "field_excesses": excesses,
            "mse": float(np.mean(errors)), "noise": float(np.mean(excesses)),
            "products_per_field": row["N"]}


def render(output):
    main = json.loads((output / "summary_lowprec.json").read_text())
    folder = output / "lowprec_float64_checkpoints"
    config = configuration(main)
    rows = [json.loads((folder / (key(job) + ".json")).read_text()) for job in jobs(config)]
    index = {(r["n"], r["N"], r["regime"], r["method"]): r for r in rows}
    comparisons = []
    for r in main["rows"]:
        control = index.get((r["n"], r["N"], r["regime"], r["method"]))
        if r["mode"] != "SR" or control is None:
            continue
        measured = r["measured_noise"]
        comparisons.append({k: r[k] for k in ("n", "N", "regime", "fmt", "method")} | {
            "float64_noise": control["noise"], "measured_noise": measured,
            "predicted_noise": r["predicted_noise"],
            "float64_over_measured_noise": control["noise"] / measured if measured else None,
            "measured_over_predicted_noise": measured / r["predicted_noise"] if measured is not None else None})
    summary = {"config": config, "base_hash": main["config_hash"], "controls": rows,
               "comparisons": comparisons, "solver_runs": len(rows) * len(config["fields"])}
    write(output / "summary_lowprec_float64.json", summary)
    text = ["# Float64 realization controls", "", __doc__.strip(), "",
            f"Controls: {len(rows)} configurations, {summary['solver_runs']} solver runs, one process.", "",
            "| n | N | Regime | Method | Float64 excess MSE | fp32 excess MSE | fp32 prediction | Control / fp32 excess |",
            "|---:|---:|---|---|---:|---:|---:|---:|"]
    for r in comparisons:
        if r["fmt"] != "fp32":
            continue
        ratio = r["float64_over_measured_noise"]
        measured = f"{r['measured_noise']:.6g}" if r['measured_noise'] is not None else "nonfinite"
        text.append(f"| {r['n']} | {r['N']} | {r['regime']} | {NAME[r['method']]} | "
                    f"{r['float64_noise']:.6g} | {measured} | {r['predicted_noise']:.6g} | "
                    + (f"{ratio:.6g}" if ratio is not None else "—") + " |")
    (output / "report_lowprec_float64.md").write_text("\n".join(text) + "\n")
    write(output / "lowprec_float64_done.json", {"base_hash": main["config_hash"],
          "solver_runs": summary["solver_runs"], "utc": datetime.now(timezone.utc).isoformat()})
    return summary


def diagnose(output=None):
    output = Path(output or HERE / "results")
    main = json.loads((output / "summary_lowprec.json").read_text())
    config = configuration(main)
    digest = hashlib.sha256(json.dumps(config, sort_keys=True).encode()).hexdigest()
    folder = output / "lowprec_float64_checkpoints"
    folder.mkdir(exist_ok=True)
    path = output / "config_lowprec_float64.json"
    if path.exists() and json.loads(path.read_text()) != config:
        raise ValueError("Float64-control configuration changed")
    write(path, config)
    for row in jobs(config):
        path = folder / (key(row) + ".json")
        if path.exists():
            if json.loads(path.read_text())["config_hash"] != digest:
                raise ValueError("Float64-control checkpoint configuration differs")
            continue
        value = compute(row, config["fields"], config.get("realization"))
        write(path, {**value, "config_hash": digest})
        print(datetime.now(timezone.utc).isoformat(), "float64 control", key(row), flush=True)
    return render(output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("run", "resume", "status", "render"))
    parser.add_argument("--output", type=Path, default=HERE / "results")
    args = parser.parse_args()
    if args.action == "status":
        print(len(list((args.output / "lowprec_float64_checkpoints").glob("*.json"))), "controls saved")
    elif args.action == "render":
        render(args.output)
    else:
        diagnose(args.output)
