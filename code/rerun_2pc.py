"""Reruns with Balanced executed by Algorithm 2'C (averaged-Prefix form).

The method label stays "balanced"; analysis, reports and figures are those of
the original stages. Every output goes below results/rerun_2pc (or --output);
the stored results and figures are never written.

  smoke       tiny consensus/regression and Poisson runs, then full-size timing
              probes and a run-time estimate (a few minutes)
  consensus   coupled cycles (variation), Balanced -> 2'C, 2048 trials
  regression  distributed ridge (additive), Flat -> 5-slot buffer (optional)
  lowprec     Poisson study, Balanced -> 2'C, all five methods; the frozen
              predictions of results/pred_lowprec.json are reused after a
              same-history check (--recompute-predictions recomputes them)
  all         consensus, then lowprec
  status      checkpoint counts

python rerun_2pc.py smoke
python rerun_2pc.py all
"""

import argparse
import json
import re
import time
from datetime import datetime, timezone
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
OUTPUT = HERE / "results/rerun_2pc"
BALANCED = {"balanced": "balanced2c"}
FLAT = {"flat": "flat5"}
SOURCE = "results/pred_lowprec.json"


def stamp(*text):
    print(datetime.now(timezone.utc).isoformat(), *text, flush=True)


def guard(output):
    output = Path(output).resolve()
    if output == (HERE / "results").resolve() or output == HERE.resolve():
        raise ValueError("Reruns write to a separate directory, not results/.")
    return output


def consensus(output, trials=2048, smoke=False):
    """Variation (coupled cycles) experiment with Balanced -> 2'C."""
    import run_all
    from analyze import analyze

    output = guard(output)
    horizons = (64, 128) if smoke else None
    curve = (64, 96, 128) if smoke else None
    run_all.predictions(output, BALANCED, horizons, curve)
    run_all.experiment("variation", trials, output, BALANCED, horizons)
    analyze(output)


def regression(output, trials=2048, smoke=False):
    """Additive (ridge) experiment with Flat -> 5-slot buffer."""
    import run_all
    from analyze import analyze
    from plots import build

    output = guard(output)
    horizons = (64, 128) if smoke else None
    curve = (64, 96, 128) if smoke else None
    run_all.predictions(output, FLAT, horizons, curve)
    run_all.experiment("additive", trials, output, FLAT, horizons)
    analyze(output)
    build(output, output / "figures")


def lowprec_config(frozen=True, methods=None, smoke=False):
    from lowprec_study import CONFIG

    config = dict(CONFIG, realization=dict(BALANCED))
    if methods:
        config["methods"] = list(methods)
    if smoke == "grid":  # smallest production grid, frozen predictions
        config.update(grids=[64], horizons=[64, 128], formats=["bf16"],
                      sr_per_field=4, rn_fields=[2701, 2702])
    elif smoke:  # tiny grid, predictions recomputed
        config.update(grids=[8], horizons=[16, 32], formats=["bf16", "fp32"],
                      sr_fields=[1701], sr_per_field=8, rn_fields=[2701, 2702])
        frozen = False
    if frozen:
        config["frozen_predictions"] = SOURCE
        config["frozen_predictions_hash"] = json.loads((HERE / SOURCE).read_text())["config_hash"]
    return config


def lowprec(output, config, workers=None):
    """Poisson study, float64 controls and additive-regime views in `output`."""
    from lowprec_diagnostics import diagnose
    from lowprec_regimes import render
    from lowprec_study import experiment

    output = guard(output)
    experiment(output, config, workers)
    diagnose(output)
    if {"flat", "pref"} <= set(config["methods"]):
        render(output, output / "figures")


def _seconds(function):
    started = time.perf_counter()
    function()
    return time.perf_counter() - started


def probes(trials=2048):
    """Full-size per-configuration timings (one configuration each)."""
    import predict
    import simulate
    from common import prepare
    from lowprec_study import CONFIG
    from models import CoupledCycles, SpikedRidge
    from poisson import Poisson, tape_seed

    result = {"consensus": {}, "regression": {}, "poisson": {}}
    problem = CoupledCycles(10000)
    for method in ("balanced", "balanced2c", "pref", "lf", "sine"):
        c = prepare(method, 1024, problem.mu, problem.L)
        p = predict.variation(c, problem)
        result["consensus"][method] = _seconds(
            lambda c=c, p=p: simulate.variation(c, problem, .01 * problem.mu, trials, 7, p))
    problem = SpikedRidge(100)
    for method in ("flat", "flat5", "pref", "lf", "dfb", "masg"):
        c = prepare(method, 1024, problem.mu, problem.L)
        p = predict.additive(c, problem, .3 * problem.mu)
        result["regression"][method] = _seconds(
            lambda c=c, p=p: simulate.additive(c, problem, .3 * problem.mu, trials, 7, p))
    from common import run

    for n in CONFIG["grids"]:
        p = Poisson(n)
        star = p.field(1701)
        rhs = p.apply(star)
        x0 = np.zeros_like(star)
        result["poisson"][str(n)] = {}
        for method in ("balanced", "balanced2c", "pref"):
            c = prepare(method, 1024, p.mu, p.L)
            times = []
            for trial in range(2):
                oracle = p.oracle("bf16", "SR", CONFIG["seed"], tape_seed(1701, trial), rhs)
                times.append(_seconds(lambda c=c, x0=x0, oracle=oracle: run(c, x0, oracle)))
            result["poisson"][str(n)][method] = min(times)
    return result


def estimate(timing, workers=8, efficiency=0.9):
    """Scale the probes to the full reruns; Poisson uses the original per-configuration log."""
    from run_all import HORIZONS, KAPPAS

    scale = sum(HORIZONS) / 1024
    dyadic = sum(N for N in HORIZONS if not N & (N - 1)) / 1024
    out = {}
    for task, label, methods in (("consensus", "variation", ("balanced2c", "pref", "sine")),
                                 ("regression", "additive", ("flat5", "pref", "dfb", "masg"))):
        t = timing[task]
        seconds = len(KAPPAS[label]) * (scale * sum(t[m] for m in methods) + dyadic * t["lf"])
        out[task] = {"seconds_one_process": seconds}
    log = HERE / "results/logs/lowprec.log"
    measured = {}
    for line in log.read_text().splitlines() if log.exists() else []:
        m = re.search(r"measured (\S+) ([\d.]+)s$", line)
        if m:
            n, _, _, _, _, method = m.group(1).split("_")
            measured[m.group(1)] = (n, method, float(m.group(2)))
    total = 0.0
    for n, method, seconds in measured.values():
        if method == "balanced":
            p = timing["poisson"].get(n)
            seconds *= p["balanced2c"] / p["balanced"] if p else 1.0
        total += seconds
    out["lowprec"] = {"cpu_seconds": total, "configurations": len(measured),
                      "workers": workers, "efficiency": efficiency,
                      "wall_seconds": total / (workers * efficiency),
                      "float64_controls_seconds": 60,
                      "recompute_predictions_seconds": 28791}
    return out


def smoke(output, workers=2):
    output = guard(output)
    started = time.perf_counter()
    report = {"utc": datetime.now(timezone.utc).isoformat(), "stages": {}}
    for name, function in (
        ("consensus", lambda: consensus(output / "consensus", 16, smoke=True)),
        ("regression", lambda: regression(output / "regression", 16, smoke=True)),
        ("lowprec_grid64_frozen", lambda: lowprec(output / "lowprec", lowprec_config(smoke="grid"), workers)),
        ("lowprec_grid8_recomputed", lambda: lowprec(output / "lowprec_tiny", lowprec_config(smoke=True), workers)),
    ):
        report["stages"][name] = _seconds(function)
        stamp("smoke stage", name, f"{report['stages'][name]:.1f}s")
    report["probes"] = probes()
    report["estimate"] = estimate(report["probes"])
    report["seconds"] = time.perf_counter() - started
    (output / "timing.json").write_text(json.dumps(report, indent=2) + "\n")
    e = report["estimate"]
    stamp("ESTIMATE consensus", f"{e['consensus']['seconds_one_process'] / 60:.1f} min;",
          "regression", f"{e['regression']['seconds_one_process'] / 60:.1f} min;",
          "lowprec", f"{e['lowprec']['wall_seconds'] / 3600:.2f} h with {e['lowprec']['workers']} workers")
    stamp("SMOKE COMPLETE", f"{report['seconds']:.1f}s", output)
    return report


def status(output):
    for sub in ("consensus", "regression", "lowprec"):
        folder = Path(output) / sub
        files = sorted(p.name for p in folder.glob("*.npz")) if folder.exists() else []
        checkpoints = len(list((folder / "lowprec_checkpoints").glob("*.npz"))) if folder.exists() else 0
        print(sub, files, "checkpoints:", checkpoints)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("stage", choices=("smoke", "consensus", "regression", "lowprec", "all", "status"))
    parser.add_argument("--output", type=Path)
    parser.add_argument("--trials", type=int, default=2048)
    parser.add_argument("--workers", type=int)
    parser.add_argument("--methods", help="comma-separated Poisson methods (default: all five)")
    parser.add_argument("--recompute-predictions", action="store_true")
    args = parser.parse_args()
    if args.stage == "smoke":
        smoke(args.output or HERE / "results/rerun_2pc_smoke", args.workers or 2)
        return
    output = guard(args.output or OUTPUT)
    if args.stage == "status":
        status(output)
        return
    stamp("START", args.stage, output)
    if args.stage in ("consensus", "all"):
        consensus(output / "consensus", args.trials)
        stamp("consensus complete")
    if args.stage == "regression":
        regression(output / "regression", args.trials)
        stamp("regression complete")
    if args.stage in ("lowprec", "all"):
        methods = args.methods.split(",") if args.methods else None
        config = lowprec_config(not args.recompute_predictions, methods)
        lowprec(output / "lowprec", config, args.workers)
        stamp("lowprec complete")
    stamp("COMPLETE", args.stage)


if __name__ == "__main__":
    main()
