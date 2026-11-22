"""Generate the numerical section of the task report from stored artifacts."""

import json
import math
from pathlib import Path

from common import NAME
from lowprec_study import CONFIG, configurations
from poisson import Poisson

HERE = Path(__file__).resolve().parent
REPORT = HERE.parent / "litreview/tasks/BEZOUT-LOWPREC-REPORT.md"
MARKER = "<!-- BEGIN GENERATED LOWPREC RESULTS -->"


def update():
    output = HERE / "results"
    final = output / "summary_lowprec.json"
    source = final if final.exists() else output / "lowprec_cost/summary_lowprec.json"
    config = CONFIG
    count = len(list((output / "lowprec_checkpoints").glob("*.npz")))
    predictions = len(list((output / "lowprec_predictions").glob("*.json")))
    expected = len(list(configurations(config)))
    sweep_done = (output / "lowprec_done.json").exists()
    controls_done = (output / "lowprec_float64_done.json").exists()
    done = sweep_done and controls_done
    state_path = output / "lowprec_run_state.json"
    state = (
        json.loads(state_path.read_text())
        if state_path.exists()
        else {"phase": "prepared"}
    )
    lines = [
        MARKER,
        "",
        "## Generated status and numerical evidence",
        "",
        (
            f"Main-sweep stage: **{'complete' if done else ('float64 controls pending/running' if sweep_done else state['phase'])}**. "
            f"Prediction checkpoints: {predictions}/{expected // 2}; "
            f"simulation checkpoints: {count}/{expected}."
        ),
        "",
        "Session: `bezout-lowprec`; log: `bezout-code/results/logs/lowprec.log`.",
        "Resume: `cd bezout-code; screen -dmS bezout-lowprec sh run_lowprec.sh`.",
        "`./run.sh lowprec-pred` prepares/reuses predictions; `./run.sh lowprec` resumes simulations.",
        "",
        "The full prediction manifest is completed before any final simulation starts.",
        "",
    ]
    regime_path = output / "summary_lowprec_regimes.json"
    if regime_path.exists():
        regime = json.loads(regime_path.read_text())
        accuracy = next(r for r in regime["calibration_by_method"] if r["method"] == "flat")
        spread = max(r["max_over_min"] for r in regime["precision_spreads"] if r["method"] == "flat")
        lines += ["### Main additive finding", "",
                  (f"Across all {accuracy['configurations']} Flat SR configurations, the frozen "
                   f"noise prediction has median absolute relative discrepancy {accuracy['median_absolute_error']:.3%} "
                   f"and maximum {accuracy['maximum_absolute_error']:.3%}. The maximum format-to-format "
                   f"spread after normalization by u squared is {spread:.6g}. The frozen prediction "
                   f"selects {regime['predicted_twofold_flat']} configurations with at least a twofold "
                   f"MSE reduction; paired 95% intervals confirm this in {regime['confirmed_with_95_interval']} "
                   "configurations. This follow-up view reuses the declared sweep and runs no solver."), "",
                  ("Recommended views: `bezout-code/figures/lowprec_additive.pdf` and "
                  "`bezout-code/figures/lowprec_floors.pdf`. Complete regime table and draft: "
                  "`bezout-code/results/report_lowprec_regimes.md`."), ""]
    lines += [
        "### Fixed final design",
        "",
        (
            f"Grids: {config['grids']}; horizons: {config['horizons']}; "
            f"formats: {config['formats']}; modes: {config['modes']}."
        ),
        (
            f"SR: {len(config['sr_fields']) * config['sr_per_field']} trials per configuration "
            f"({len(config['sr_fields'])} fixed fields, {config['sr_per_field']} tapes each); "
            f"RN: {len(config['rn_fields'])} fixed fields. Bootstrap: {config['bootstrap']} paired resamples."
        ),
        f"Configured solver runs: {expected // 2 * (len(config['sr_fields']) * config['sr_per_field'] + len(config['rn_fields']))}.",
        "",
        "| Grid n | Dimension | μ | L | κ |",
        "|---:|---:|---:|---:|---:|",
    ]
    for n in config["grids"]:
        p = Poisson(n)
        lines.append(f"| {n} | {n * n} | {p.mu:.8g} | {p.L:.8g} | {p.L / p.mu:.8g} |")
    coherent = output / "coherent_reaction"
    if (coherent / "pred.json").exists():
        predicted = json.loads((coherent / "pred.json").read_text())
        ready = (coherent / "summary.json").exists()
        lines += ["", "### Coherent reaction-coefficient companion", "",
                  ("Predictions are frozen for a single Poisson grid, bf16 SR of the shared reaction "
                   "coefficient and a two-mode initial error. The invariant subspace reduces the "
                   "spatial problem exactly to two coordinates. This is a separate coefficient-rounding "
                   "model; the rounded-stencil sweep remains intact."), "",
                  "Status: **" + ("complete" if ready else "short validation queued at a quiet campaign boundary") + "**.", "",
                  "| N | Predicted Balanced/Prefix excess MSE |",
                  "|---:|---:|"]
        for N in predicted["config"]["horizons"]:
            b = next(r for r in predicted["rows"] if r["N"] == N and r["method"] == "balanced")
            p = next(r for r in predicted["rows"] if r["N"] == N and r["method"] == "pref")
            lines.append(f"| {N} | {b['noise']/p['noise']:.6g} |")
    sensitivity = output / "logs/lowprec-quadrature-sensitivity.json"
    if sensitivity.exists():
        check = json.loads(sensitivity.read_text())
        maximum = max(abs(r["noise_8_over_32"] - 1) for r in check["rows"])
        lines += ["", f"Quadrature pilot: maximum relative noise-prediction change over {len(check['rows'])} declared cases: {maximum:.6%} (8 versus 32 paths).", ""]
    prediction_path = output / "pred_lowprec.json"
    if prediction_path.exists():
        saved = json.loads(prediction_path.read_text())
        problems = {n: Poisson(n) for n in saved["config"]["grids"]}
        checks = []
        for row in saved["rows"]:
            if row["method"] != "flat":
                continue
            closed = (1 - row["epsilon"]) / (problems[row["n"]].mu * math.sqrt(row["N"]))
            checks.append({"n": row["n"], "N": row["N"], "regime": row["regime"], "format": row["fmt"],
                           "closed": closed, "saved_gain": row["additive_energy"],
                           "relative_error": abs(row["additive_energy"] / closed - 1)})
        maximum = max(r["relative_error"] for r in checks)
        receipt = {"config_hash": saved["config_hash"], "checks": len(checks),
                   "maximum_relative_error": maximum, "rows": checks}
        (output / "logs/lowprec-theory-identities.json").write_text(json.dumps(receipt, indent=2) + "\n")
        lines += ["", (f"The {len(checks)} saved Flat prediction rows reproduce the closed energy gain "
                  f"(1−epsilon_N^star)/(mu sqrt(N)) to maximum relative discrepancy {maximum:.6g}. "
                  "This check uses the frozen prediction file and preserves its values."), ""]
    lines += [
        "",
        "SR covariance quadrature uses "
        + str(config["covariance_samples"])
        + " arithmetic paths per nominal field/query. These draws precede solver simulation.",
        (
            "Predictions use the simulated horizons. The denser 16-call prediction grid was omitted "
            "because the pilot covariance quadrature dominates preparation cost. "
            "Adjacent odd horizons are included in the declared final design."
        ),
        "",
    ]
    if source.exists():
        summary = json.loads(source.read_text())
        pilot = source != final
        largest = max(summary["config"]["horizons"])
        n = max(summary["config"]["grids"])
        lines += [
            "### " + ("Cost pilot (provisional)" if pilot else "Final results"),
            "",
            f"Source: `{source.relative_to(HERE.parent)}`. Grid {n} × {n}, N={largest}.",
            "Pilot quantities retain their own prediction manifest and random seeds." if pilot
            else "Every declared configuration remains in the complete saved summary.",
            "",
            "| Regime | Format | Mode | Method | MSE / Prefix [95% interval] | SR prediction | Noise / prediction |",
            "|---|---|---|---|---:|---:|---:|",
        ]
        selected = [r for r in summary["rows"] if r["n"] == n and r["N"] == largest]
        for r in selected:
            q = r["ratio"]
            ratio = (
                f"{q['value']:.4g} [{q['lo']:.4g}, {q['hi']:.4g}]" if q else "nonfinite"
            )
            pr = f"{r['predicted_ratio']:.4g}" if r["mode"] == "SR" else "—"
            calibration = (
                f"{r['measured_noise'] / r['predicted_noise']:.4g}"
                if r["mode"] == "SR" and r["measured_noise"] is not None
                else "—"
            )
            lines.append(
                f"| {r['regime']} | {r['fmt']} | {r['mode']} | {NAME[r['method']]} | {ratio} | {pr} | {calibration} |"
            )
        lines += [
            "",
            "### Draft subsection "
            + ("(pilot wording; replace after final completion)" if pilot else ""),
            "",
            (
                "**Chebyshev iteration with low-precision products.** "
                "We solve the Dirichlet Poisson problem on a square interior grid. "
                "The five-point stencil is scaled by 1/8. Every product input and scalar "
                "stencil operation is rounded to the specified low format; vector updates "
                "use double precision. The five realizations retain the same Chebyshev "
                "terminal polynomial. Predictions propagate the conditional product covariance "
                "through the physical responses in the sine basis."
            ),
            "",
        ]

        def find(regime, fmt, mode, method):
            return next(
                r
                for r in selected
                if (r["regime"], r["fmt"], r["mode"], r["method"])
                == (regime, fmt, mode, method)
            )

        if all(
            any(
                r["regime"] == a
                and r["fmt"] == b
                and r["mode"] == "SR"
                and r["method"] == m
                for r in selected
            )
            for a, b, m in [
                ("A", "fp16", "flat"),
                ("A", "bf16", "flat"),
                ("R", "bf16", "balanced"),
            ]
        ):
            f, b, r = (
                find("A", "fp16", "SR", "flat"),
                find("A", "bf16", "SR", "flat"),
                find("R", "bf16", "SR", "balanced"),
            )
            if all(x["ratio"] for x in (f, b, r)):
                lines += [
                    (
                        f"At N={largest} on the {n} × {n} grid, Flat's stochastic MSE "
                        f"in the nonzero-solution regime is {f['ratio']['value']:.3g} "
                        f"(95% interval [{f['ratio']['lo']:.3g}, {f['ratio']['hi']:.3g}]) "
                        f"times Prefix's in fp16 and {b['ratio']['value']:.3g} "
                        f"([{b['ratio']['lo']:.3g}, {b['ratio']['hi']:.3g}]) in bf16. "
                        f"The corresponding covariance predictions are {f['predicted_ratio']:.3g} "
                        f"and {b['predicted_ratio']:.3g}. For the zero solution and smooth "
                        f"initial fields, Balanced's bf16 MSE ratio is {r['ratio']['value']:.3g}, "
                        f"with predicted ratio {r['predicted_ratio']:.3g}. "
                        "The stencil's spatial covariance determines this instance-specific "
                        "ordering; the theorem gives the optimum under a shared worst-case energy budget."
                    ),
                    "",
                ]
        lines += [
            (
                "**Figure caption.** Chebyshev iteration with rounded Poisson products. "
                "Terminal MSE ratios to Prefix for the zero-solution (R) and nonzero-solution (A) "
                "regimes. Lines use the conditional-covariance prediction along the nominal path. "
                "Filled circles: stochastic rounding; open squares: nearest-even rounding. "
                "Intervals use paired bootstrap resampling. Each horizon starts afresh."
            ),
            "",
            (
                "Proposed placement: first subsection of §6. Estimated length: 1–1.5 Springer pages "
                "including the figure. The repeated protocol paragraph in §6 and the verbal "
                "recapitulation of the additive variance derivation in Appendix D could be shortened."
            ),
            "",
            "### Findings requiring qualification",
            "",
            (
                "The R pilot reaches the fp16 subnormal range. The final run records sampled "
                "subnormal inputs, zero products, and product error relative to the exact product. "
                "These are saved per configuration. Balanced's worst-case optimum and the actual "
                "stencil covariance are distinct comparison criteria. All unfavorable configurations remain saved."
            ),
            "",
            "### Absolute terminal errors",
            "",
            "| Regime | Format | Mode | Method | RMS terminal error | RMS / unit roundoff | Stationary additive MSE prediction |",
            "|---|---|---|---|---:|---:|---:|",
        ]
        for r in selected:
            if r["method"] not in ("flat", "balanced", "pref"):
                continue
            mse = r["measured_mse"]
            rms = mse**0.5 if mse is not None else None
            u = 2.0 ** -{"fp16": 11, "bf16": 8, "fp32": 24}[r["fmt"]]
            floor = r["stationary_floor"]
            lines.append(
                f"| {r['regime']} | {r['fmt']} | {r['mode']} | {NAME[r['method']]} | "
                + (
                    f"{rms:.5g} | {rms / u:.5g}"
                    if rms is not None
                    else "nonfinite | nonfinite"
                )
                + " | "
                + (f"{floor:.5g}" if floor is not None else "—")
                + " |"
            )
        lines += [
            "", "### First-order and arithmetic diagnostics", "",
            ("The diagnostics below use all saved configurations. Product-error and subnormal "
             "statistics sample the first tape of each field; MSE estimates use every tape."), "",
            "| Regime | Format | Finite SR configurations | Noise/prediction range | Maximum sampled subnormal fraction | Maximum sampled relative product error |",
            "|---|---|---:|---:|---:|---:|",
        ]
        for regime in ("R", "A"):
            for fmt in summary["config"]["formats"]:
                group = [r for r in summary["rows"] if r["regime"] == regime
                         and r["fmt"] == fmt and r["mode"] == "SR"]
                finite = [r for r in group if r["measured_noise"] is not None]
                calibration = [r["measured_noise"] / r["predicted_noise"] for r in finite]
                diagnosed = [r for r in group if r.get("diagnostics")]
                subnormal = max((r["diagnostics"]["subnormal_inputs"] /
                                 max(1, r["diagnostics"]["input_components"]) for r in diagnosed), default=0)
                product = max((r["diagnostics"]["max_product_relative_error"] for r in diagnosed), default=0)
                span = f"{min(calibration):.4g}–{max(calibration):.4g}" if calibration else "—"
                arithmetic = f"{subnormal:.5g} | {product:.5g}" if diagnosed else "— | —"
                lines.append(f"| {regime} | {fmt} | {len(finite)}/{len(group)} | {span} | "
                             f"{arithmetic} |")
        lines += ["", "### Adjacent-horizon parity check", "",
                  f"SR MSE/Prefix on the predeclared largest grid n={n}. All three adjacent horizons start afresh.", "",
                  "| Regime | Format | Method | N=255 | N=256 | N=257 |",
                  "|---|---|---|---:|---:|---:|"]
        for regime in ("R", "A"):
            for fmt in ("fp16", "bf16"):
                for method in ("flat", "balanced", "pref"):
                    cells = []
                    for horizon in (255, 256, 257):
                        point = next((r for r in summary["rows"] if (r["n"], r["N"], r["regime"],
                                      r["fmt"], r["mode"], r["method"]) ==
                                      (n, horizon, regime, fmt, "SR", method)), None)
                        cells.append("—" if point is None else
                                     (f"{point['ratio']['value']:.5g}" if point['ratio'] else "nonfinite"))
                    lines.append(f"| {regime} | {fmt} | {NAME[method]} | " + " | ".join(cells) + " |")
        lines += ["", f"Nonfinite trial outcomes across the saved design: {sum(r['failures'] for r in summary['rows'])}.", ""]
        lines += ["### Deterministic rounding and robust quantities", "",
                  ("The gain columns use a common unit error-energy budget. The measured stencil "
                  "generates its own method-dependent error energy. The operator column gives "
                  "squared Cauchy–Schwarz upper bounds; the additive column gives exact squared "
                  "energy gains on the discrete spectrum. RN measurements are individual "
                  "deterministic, correlated rounding realizations."), "",
                  "| Regime | Format | Method | RN MSE/Prefix | Squared additive gain/Prefix | Squared operator bound/Prefix |",
                  "|---|---|---|---:|---:|---:|"]
        for r in selected:
            if r["mode"] == "RN":
                value = f"{r['ratio']['value']:.5g}" if r['ratio'] else "nonfinite"
                lines.append(f"| {r['regime']} | {r['fmt']} | {NAME[r['method']]} | {value} | "
                             f"{r['additive_energy_ratio']**2:.5g} | {r['operator_bound_ratio']**2:.5g} |")
        controls_path = output / "summary_lowprec_float64.json"
        if controls_path.exists():
            controls = json.loads(controls_path.read_text())
            lines += ["", "### Float64 realization controls", "",
                      (f"The post-sweep diagnostic has {len(controls['controls'])} configurations and "
                       f"{controls['solver_runs']} solver runs on the same four SR fields. "
                       "It retains every original prediction and low-precision sample. "
                       "Products, coefficients and vector updates use float64; excess MSE is "
                       "measured against the nominal Chebyshev terminal."), "",
                      "Balanced, R regime, fp32 reference:", "",
                      "| n | N | Float64 excess MSE | Measured fp32 excess MSE | fp32 first variation | Control / measured |",
                      "|---:|---:|---:|---:|---:|---:|"]
            for r in controls["comparisons"]:
                if (r["method"], r["regime"], r["fmt"]) == ("balanced", "R", "fp32"):
                    lines.append(f"| {r['n']} | {r['N']} | {r['float64_noise']:.6g} | "
                                 f"{r['measured_noise']:.6g} | {r['predicted_noise']:.6g} | "
                                 f"{r['float64_over_measured_noise']:.6g} |")
            target = next(r for r in controls["comparisons"] if
                          (r["n"], r["N"], r["method"], r["regime"], r["fmt"]) ==
                          (min(config["grids"]), max(config["horizons"]), "balanced", "R", "fp32"))
            lines += ["", (f"At n={target['n']}, N={target['N']}, the float64 control's excess MSE "
                           f"is {target['float64_noise']:.6g}, compared with "
                           f"{target['measured_noise']:.6g} in fp32 and a first-variation prediction "
                           f"of {target['predicted_noise']:.6g}. The control/reference ratio is "
                           f"{target['float64_over_measured_noise']:.6g}, consistent with a "
                           "float64 realization-arithmetic floor at this depth. The control includes "
                           "coefficient and update arithmetic; its ratio is a diagnostic comparison. "
                           "The complete per-method table is results/report_lowprec_float64.md."), ""]
        figure = (
            (HERE / "figures/lowprec.pdf")
            if not pilot
            else source.parent / "figures/lowprec.pdf"
        )
        lines += ["", f"Figure: `{figure.relative_to(HERE.parent)}`.", ""]
        regime_report = output / "report_lowprec_regimes.md"
        if regime_report.exists():
            lines += ["## Additive-regime experimental closing", "", regime_report.read_text(), ""]
        coherent_report = output / "coherent_reaction/REPORT.md"
        if coherent_report.exists():
            lines += ["## Coherent-operator companion: measured results", "", coherent_report.read_text(), "",
                      "Figure: `bezout-code/figures/lowprec_coherent.pdf`.", ""]
    base = REPORT.read_text().split(MARKER)[0].rstrip()
    REPORT.write_text(base + "\n\n" + "\n".join(lines) + "\n")


if __name__ == "__main__":
    update()
