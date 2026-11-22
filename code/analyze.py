"""Compute paired-bootstrap ratio intervals from the saved trial arrays."""

import json
from pathlib import Path

import numpy as np
from common import NAME

HERE = Path(__file__).resolve().parent
RESULTS = HERE / "results"


def paired(a, b, seed, bootstrap=500):
    ratio = float(a.mean() / b.mean())
    rng = np.random.default_rng(seed)
    values = []
    for _ in range(bootstrap):
        ids = rng.integers(0, len(a), len(a))
        values.append(a[ids].mean() / b[ids].mean())
    lo, hi = map(float, np.quantile(values, [0.025, 0.975]))
    return {"value": ratio, "lo": lo, "hi": hi}


def analyze(output=None):
    output = Path(output or RESULTS)
    predictions = json.loads((output / "pred.json").read_text())
    summary = {"parameters": predictions["parameters"], "additive": [], "variation": []}
    text = [
        "# Experiment results",
        "",
        "Rows compare the same task, instance and N. Intervals are paired bootstrap intervals.",
        "Variation noise is deviation from the common Chebyshev terminal, not total error.",
        "Its prediction is first order; additive predictions are exact finite-noise MSE.",
        "",
    ]
    for task in ("additive", "variation"):
        path = output / f"raw_{task}.npz"
        if not path.exists():
            continue
        with np.load(path, allow_pickle=False) as data:
            index = {
                (int(k), int(n), str(m)): j
                for j, (k, n, m) in enumerate(
                    zip(data["kappa"], data["N"], data["method"])
                )
            }
            for j in range(len(data["N"])):
                k, N, m = (
                    int(data["kappa"][j]),
                    int(data["N"][j]),
                    str(data["method"][j]),
                )
                curve = predictions[task].get(str(k), {}).get(m, [])
                point = next((p for p in curve if p["N"] == N), None)
                if point is None or not np.isclose(
                    point["energy"], data["theory_energy"][j], rtol=1e-8, atol=0
                ):
                    raise ValueError(
                        f"{path.name} does not match pred.json; rerun {task}."
                    )
                ref = index[k, N, "pref"]
                key = "error" if task == "additive" else "excess"
                samples, base = data[key][j], data[key][ref]
                ci = (
                    {"value": 1.0, "lo": 1.0, "hi": 1.0}
                    if j == ref
                    else paired(samples, base, SEED + k + N)
                )
                ours = index[k, N, "flat" if task == "additive" else "balanced"]
                direct = (
                    {"value": 1.0, "lo": 1.0, "hi": 1.0}
                    if j == ours
                    else paired(data[key][ours], samples, SEED + k + N)
                )
                row = {
                    "kappa": k,
                    "N": N,
                    "method": m,
                    "trials": len(samples),
                    "ratio": ci,
                    "ours_over_method": direct,
                    "measured_mse": float(data["error"][j].mean()),
                    "measured_noise": float(data["excess"][j].mean()),
                    "energy_ratio": float(data["energy"][j] / data["energy"][ref]),
                    "energy_measured": float(data["energy"][j]),
                    "energy_predicted": float(data["theory_energy"][j]),
                    "noise_measured_over_predicted": float(
                        data["excess"][j].mean() / data["theory_noise"][j]
                    ),
                    "full_mse_ratio": float(
                        data["error"][j].mean() / data["error"][ref].mean()
                    ),
                    "predicted_ratio": float(
                        data["theory_total"][j] / data["theory_total"][ref]
                    )
                    if task == "additive"
                    else float(data["theory_noise"][j] / data["theory_noise"][ref]),
                }
                summary[task].append(row)
        text += [
            f"## {task}: largest horizon",
            "",
            "| κ | Method | Measured ratio to Prefix [95% interval] | Theory ratio | Our method / competitor [95% interval] |",
            "|---:|---|---:|---:|---:|",
        ]
        largest = max(r["N"] for r in summary[task])
        for r in summary[task]:
            if r["N"] != largest:
                continue
            q = r["ratio"]
            d = r["ours_over_method"]
            text.append(
                f"| {r['kappa']} | {NAME[r['method']]} | {q['value']:.4g} [{q['lo']:.4g}, {q['hi']:.4g}] | {r['predicted_ratio']:.4g} | {d['value']:.4g} [{d['lo']:.4g}, {d['hi']:.4g}] |"
            )
        text.append("")
        if task == "variation":
            text += [
                "For full-MSE ratios, including the common nominal bias, see summary.json.",
                "",
            ]
    (output / "summary.json").write_text(
        json.dumps(summary, indent=2, allow_nan=False) + "\n"
    )
    (output / "report.md").write_text("\n".join(text) + "\n")
    return predictions, summary


SEED = 17013


def analyze_lowprec(output=None):
    """Analyze the separate low-precision stage, preserving the earlier outputs."""
    from lowprec_study import write_json
    output = Path(output or RESULTS)
    pred = json.loads((output / "pred_lowprec.json").read_text())
    prediction_index = {(r["n"], r["N"], r["regime"], r["fmt"], r["method"]): r
                        for r in pred["rows"]}
    rows = []
    with np.load(output / "raw_lowprec.npz", allow_pickle=False) as data:
        if str(data["config_hash"]) != pred["config_hash"]:
            raise ValueError("Raw low-precision arrays differ from predictions.")
        fields = ("n", "N", "regime", "fmt", "mode", "method")
        index = {tuple(str(data[k][j]) for k in fields): j for j in range(len(data["n"]))}
        for j in range(len(data["n"])):
            row = {k: int(data[k][j]) if k in ("n", "N") else str(data[k][j]) for k in fields}
            basekey = tuple(str(row[k]) if k != "method" else "pref" for k in fields)
            ref = index[basekey]
            count = int(data["trials"][j])
            a, b = data["error"][j, :count], data["error"][ref, :count]
            ea, eb = data["excess"][j, :count], data["excess"][ref, :count]
            theory = prediction_index[row["n"], row["N"], row["regime"], row["fmt"], row["method"]]
            reference = prediction_index[row["n"], row["N"], row["regime"], row["fmt"], "pref"]
            finite = bool(np.isfinite(a).all() and np.isfinite(b).all())
            ci = paired(a, b, SEED + row["n"] + row["N"]) if finite else None
            excess_ci = paired(ea, eb, SEED + row["n"] + row["N"]) if finite else None
            row.update(trials=count, failures=int((~np.isfinite(a)).sum()),
                       ratio=ci, noise_ratio=excess_ci,
                       measured_mse=float(a.mean()) if np.isfinite(a).all() else None,
                       measured_noise=float(ea.mean()) if np.isfinite(ea).all() else None,
                       predicted_ratio=theory["mse"] / reference["mse"],
                       predicted_noise_ratio=theory["noise"] / reference["noise"],
                       predicted_mse=theory["mse"], predicted_noise=theory["noise"],
                       stationary_floor=theory["floor"],
                       bias=theory["bias"],
                       additive_energy_ratio=theory["additive_energy"] / reference["additive_energy"],
                       operator_bound_ratio=theory["operator_bound"] / reference["operator_bound"])
            row["diagnostics"] = {k.removeprefix("diagnostic_"): float(data[k][j])
                                  for k in data.files if k.startswith("diagnostic_")}
            rows.append(row)
    result = {"config": pred["config"], "config_hash": pred["config_hash"], "rows": rows}
    write_json(output / "summary_lowprec.json", result)
    text = ["# Low-precision Poisson results", "",
            "Squared terminal errors; ratios use the same fields and SR tapes as Prefix.",
            "Intervals: 500 paired bootstrap resamples. RN intervals describe variation over fields.",
            "SR lines freeze operation variances at exact nominal queries. RN energy quantities are worst-case bounds.",
            "All configurations, including nonfinite trials, are retained in the summary.", "",
            "| n | N | Regime | Format | Mode | Method | MSE / Prefix [95% CI] | SR prediction | noise / prediction | Failures |",
            "|---:|---:|---|---|---|---|---:|---:|---:|---:|"]
    for r in rows:
        if r["N"] != max(pred["config"]["horizons"]):
            continue
        q = r["ratio"]
        ratio = f"{q['value']:.5g} [{q['lo']:.5g}, {q['hi']:.5g}]" if q else "nonfinite"
        calibration = (f"{r['measured_noise']/r['predicted_noise']:.5g}"
                       if r["measured_noise"] is not None and r["mode"] == "SR" else "—")
        prediction_text = f"{r['predicted_ratio']:.5g}" if r["mode"] == "SR" else "—"
        text.append(f"| {r['n']} | {r['N']} | {r['regime']} | {r['fmt']} | {r['mode']} | {NAME[r['method']]} | {ratio} | {prediction_text} | {calibration} | {r['failures']} |")
    (output / "report_lowprec.md").write_text("\n".join(text) + "\n")
    return result


if __name__ == "__main__":
    analyze()
