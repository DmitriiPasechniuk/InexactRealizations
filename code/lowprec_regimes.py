"""Render an additive-regime analysis from the frozen Poisson sweep; no solver runs."""

import argparse
import csv
import json
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def inverse_interval(interval):
    if interval is None:
        return None
    return {"value": 1 / interval["value"], "lo": 1 / interval["hi"], "hi": 1 / interval["lo"]}


def interval_text(value):
    return f"{value['value']:.4g} [{value['lo']:.4g}, {value['hi']:.4g}]" if value else "nonfinite"


def render(output=None, figures=None):
    output = Path(output or HERE / "results")
    figures = Path(figures) if figures is not None else (
        HERE / "figures" if output.resolve() == (HERE / "results").resolve() else output / "figures")
    source = json.loads((output / "summary_lowprec.json").read_text())
    predictions = json.loads((output / "pred_lowprec.json").read_text())
    if source["config_hash"] != predictions["config_hash"]:
        raise ValueError("Regime analysis requires the matching frozen predictions")
    rows = []
    for original in source["rows"]:
        if original["regime"] != "A":
            continue
        row = original.copy()
        row["mse_gain"] = inverse_interval(row["ratio"])
        row["noise_gain"] = inverse_interval(row["noise_ratio"])
        row["predicted_twofold_gain"] = row["predicted_ratio"] <= .5 if row["mode"] == "SR" else None
        row["bias_dominated"] = row["bias"] >= row["predicted_noise"]
        row["noise_calibration"] = (row["measured_noise"] / row["predicted_noise"]
                                    if row["mode"] == "SR" and row["measured_noise"] is not None else None)
        rows.append(row)
    flat = [r for r in rows if r["method"] == "flat" and r["mode"] == "SR"]
    predicted = [r for r in flat if r["predicted_twofold_gain"]]
    confirmed = [r for r in predicted if r["ratio"] and r["ratio"]["hi"] < .5]
    sr = [r for r in rows if r["mode"] == "SR" and r["noise_calibration"] is not None]
    errors = np.array([abs(r["noise_calibration"] - 1) for r in sr])
    calibration = []
    for method in source["config"]["methods"]:
        group = [r for r in sr if r["method"] == method]
        values = np.array([abs(r["noise_calibration"] - 1) for r in group])
        worst = max(group, key=lambda r: abs(r["noise_calibration"] - 1))
        calibration.append({"method": method, "configurations": len(group),
                            "median_absolute_error": float(np.median(values)),
                            "maximum_absolute_error": float(values.max()),
                            "worst_case": {k: worst[k] for k in ("n", "N", "fmt")}})
    precision_spreads = []
    for method in ("flat", "pref"):
        for n in source["config"]["grids"]:
            for N in source["config"]["horizons"]:
                values = [r["measured_noise"] / 2.0**(-2 * {"fp16": 11, "bf16": 8, "fp32": 24}[r["fmt"]])
                          for r in sr if r["method"] == method and r["n"] == n and r["N"] == N]
                if values:
                    precision_spreads.append({"method": method, "n": n, "N": N,
                                              "max_over_min": max(values) / min(values)})
    largest = max(source["config"]["horizons"])
    endpoints = [r for r in rows if r["method"] == "flat" and r["N"] == largest]
    summary = {"config_hash": source["config_hash"], "analysis": "post-sweep, stored results only",
               "selection": "All additive rows retained; twofold flag uses frozen predicted MSE ratio <= 0.5",
               "additive_configurations": len(rows), "sr_configurations": len(sr),
               "predicted_twofold_flat": len(predicted), "confirmed_with_95_interval": len(confirmed),
               "median_absolute_noise_calibration_error": float(np.median(errors)),
               "max_absolute_noise_calibration_error": float(errors.max()),
               "calibration_by_method": calibration, "precision_spreads": precision_spreads,
               "endpoints": endpoints}
    (output / "summary_lowprec_regimes.json").write_text(json.dumps(summary, indent=2, allow_nan=False) + "\n")
    with (output / "lowprec_regimes.csv").open("w", newline="") as stream:
        fields = ["n", "N", "fmt", "mode", "method", "measured_mse", "measured_noise",
                  "predicted_mse", "predicted_noise", "predicted_ratio", "bias_dominated",
                  "predicted_twofold_gain", "noise_calibration"]
        writer = csv.DictWriter(stream, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)
    text = ["# Additive Poisson regime: stored-data analysis", "",
            ("This follow-up analysis uses every declared additive configuration. No solver is run. "
             "The original largest-grid figure and all relative-regime results remain available."), "",
            f"Additive configurations: {len(rows)}; stochastic configurations: {len(sr)}.",
            (f"In {len(predicted)} Flat configurations the frozen model predicts at least a twofold MSE "
             f"reduction. The paired 95% intervals confirm at least a twofold reduction in "
             f"{len(confirmed)}/{len(predicted)} configurations. These counts share fields and tapes."),
            (f"Across all {len(sr)} additive SR configurations and all methods, the median absolute "
             f"relative discrepancy of measured excess MSE from the frozen covariance prediction is "
             f"{np.median(errors):.3%}; the maximum is {errors.max():.3%}."), ""]
    text += ["## Prediction accuracy by realization", "",
             "| Method | Configurations | Median absolute relative discrepancy | Maximum | Largest-discrepancy case |",
             "|---|---:|---:|---:|---|"]
    for r in calibration:
        case = r["worst_case"]
        text.append(f"| {r['method']} | {r['configurations']} | {r['median_absolute_error']:.3%} | "
                    f"{r['maximum_absolute_error']:.3%} | n={case['n']}, N={case['N']}, {case['fmt']} |")
    flat_accuracy = next(r for r in calibration if r["method"] == "flat")
    flat_spread = max(r["max_over_min"] for r in precision_spreads if r["method"] == "flat")
    text += ["", (f"For Flat, all {flat_accuracy['configurations']} stochastic configurations agree "
                  f"with the frozen noise model within {flat_accuracy['maximum_absolute_error']:.3%}. "
                  f"At fixed grid and horizon, the largest format-to-format spread of excess "
                  f"MSE/u squared is {flat_spread:.6g} (maximum divided by minimum), over "
                  "the complete horizon sweep."), ""]
    for mode in ("SR", "RN"):
        text += [f"## Flat gains at N={largest}, {mode}", "",
                 "| Grid | Format | Prefix/Flat terminal MSE [95% interval] | Predicted SR gain | Prefix/Flat excess MSE [95% interval] |",
                 "|---:|---|---:|---:|---:|"]
        for r in endpoints:
            if r["mode"] != mode:
                continue
            prediction = f"{1 / r['predicted_ratio']:.4g}" if mode == "SR" else "—"
            text.append(f"| {r['n']} | {r['fmt']} | {interval_text(r['mse_gain'])} | "
                        f"{prediction} | {interval_text(r['noise_gain'])} |")
        text.append("")
    small = min(source["config"]["grids"])
    chosen = [r for r in endpoints if r["n"] == small and r["mode"] == "SR"]
    text += ["## Draft subsection (§6)", "",
             ("For a nonzero solution, the rounded products generate a persistent additive component. "
              "The five realizations use the same Chebyshev terminal polynomial and the same number "
              "of matrix–vector products. Their roundoff floors differ. Figure~\\ref{fig:lowprec-additive} "
              "shows the complete horizon sweep on all three grids for fp16 and bf16; the "
              "operation-covariance prediction was frozen before the simulations."), ""]
    gains = "; ".join(f"{r['fmt']}: {interval_text(r['mse_gain'])}" for r in chosen)
    text += [(f"On the {small} by {small} grid at N={largest}, the terminal MSE reduction "
              f"relative to Prefix is {gains}. The normalized excess MSE curves for fp16, bf16 "
              "and fp32 nearly coincide after division by the squared unit roundoff. This "
              "precision collapse identifies the sensitivity of the realization as the source "
              "of the gain. At shorter horizons the common polynomial bias and the transient "
              "noise response determine the total-error comparison."), "",
             "## Figure captions", "",
             ("**lowprec_additive.pdf.** Chebyshev iteration for the Poisson problem with a nonzero "
              "solution. Terminal MSE relative to Prefix over every declared horizon and all three "
              "grids. Rows: fp16 and bf16 stochastic rounding. Lines: the frozen conditional-covariance "
              "prediction; points and bars: 256 trials and paired 95% bootstrap intervals. Each "
              "horizon starts afresh. All five realizations use N rounded products."), "",
             ("**lowprec_floors.pdf.** Precision scaling of the additive roundoff floor. Excess MSE "
              "is squared deviation from the common nominal Chebyshev terminal; u is the unit "
              "roundoff. Each method has one curve on each grid: lines average the frozen "
              "operation-covariance predictions after division by u squared; dyadic markers "
              "average the corresponding measured means over fp16, bf16 and fp32. Each format's "
              "mean uses 256 stochastic-rounding trials. Bars give the minimum and maximum over "
              "formats, rather than confidence intervals. The near-coincidence of the formats "
              "confirms u-squared scaling and is summarised once. The full comparison and CSV "
              "retain every format and declared horizon."), "",
             "## Manuscript and full views", "",
             ("The manuscript uses additive_lowprec.pdf, generated by article_figures.py, to combine "
              "regression MSE with bf16 Poisson MSE on all three grids. The full lowprec_additive.pdf, "
              "lowprec_floors.pdf, and lowprec.pdf views retain the additional format and regime "
              "comparisons. Relative-regime limitations and float64 controls remain in the report."), ""]
    (output / "report_lowprec_regimes.md").write_text("\n".join(text))
    from plots import build_lowprec_additive

    build_lowprec_additive(output, figures)
    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("render",))
    parser.add_argument("--output", type=Path, default=HERE / "results")
    parser.add_argument("--figures", type=Path)
    args = parser.parse_args()
    render(args.output, args.figures)
