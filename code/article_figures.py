"""Rebuild the manuscript's additive figure from saved regression and Poisson data.

One row of panels at the text width of the article: the two left panels retain
the regression MSE comparison; the three right panels show bf16 SR Poisson
solves on all three grids at their common dyadic horizons.
No solver or bootstrap simulation is performed.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path

import matplotlib

matplotlib.use("pdf")
import matplotlib.pyplot as plt
import numpy as np
from common import ADDITIVE, NAME
from matplotlib.lines import Line2D
from matplotlib.ticker import FuncFormatter, NullFormatter, NullLocator
from plots import COLOR

HERE = Path(__file__).resolve().parent
REGRESSION = tuple(m for m in ADDITIVE if m != "masg")  # M-ASG is not plotted in the article
WIDTH_IN, HEIGHT_IN = 5.13, 1.76  # text width of the Springer Nature layout: the figure prints at 1:1
PT = 72 * HEIGHT_IN  # vertical positions below are fixed in points from the bottom edge


def build(output=None, figures=None, poisson_dir=None):
    """output: regression results (pred.json, summary.json); poisson_dir: Poisson results
    (summary_lowprec.json, pred_lowprec.json), by default the 2'C rerun used by the article."""
    output = Path(output or HERE / "results")
    poisson_dir = Path(poisson_dir or HERE / "results" / "rerun_2pc" / "lowprec")
    figures = Path(figures or HERE / "figures")
    figures.mkdir(parents=True, exist_ok=True)
    prediction = json.loads((output / "pred.json").read_text())
    regression = json.loads((output / "summary.json").read_text())
    poisson = json.loads((poisson_dir / "summary_lowprec.json").read_text())
    if prediction["parameters"] != regression["parameters"]:
        raise ValueError("Regression predictions differ from the saved summary")
    frozen = json.loads((poisson_dir / "pred_lowprec.json").read_text())
    if poisson["config_hash"] != frozen["config_hash"]:
        raise ValueError("Poisson predictions differ from the saved summary")

    plt.rcParams.update({"font.family": "serif", "font.serif": ["DejaVu Serif"],
                         "mathtext.fontset": "cm", "font.size": 8,
                         "axes.labelsize": 8, "legend.fontsize": 7,
                         "xtick.labelsize": 7, "ytick.labelsize": 7,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "axes.linewidth": .6, "axes.grid": True,
                         "grid.color": "#e6e5e0", "grid.linewidth": .5,
                         "lines.linewidth": 1.2, "pdf.fonttype": 42})
    fig = plt.figure(figsize=(WIDTH_IN, HEIGHT_IN))
    # One row: regression (two panels), a spacer for the Poisson tick labels, Poisson (three panels).
    grid = fig.add_gridspec(1, 6, width_ratios=(1, 1, .2, 1, 1, 1), left=.1, right=.975,
                            bottom=27.3 / PT, top=93.2 / PT, wspace=.3)
    top = [fig.add_subplot(grid[0, 0]), fig.add_subplot(grid[0, 1])]
    bottom = [fig.add_subplot(grid[0, j]) for j in (3, 4, 5)]
    top[1].sharey(top[0])
    for ax in bottom[1:]:
        ax.sharey(bottom[0])
    selected = []
    for ax in [*top, *bottom]:
        ax.set(xscale="log", yscale="log")


    def measurements(ax, x, rows, method):
        if method == "pref":
            return
        mean = np.array([r["ratio"]["value"] for r in rows])
        lo = np.array([r["ratio"]["lo"] for r in rows])
        hi = np.array([r["ratio"]["hi"] for r in rows])
        ax.errorbar(x, mean, yerr=[np.maximum(0, mean-lo), np.maximum(0, hi-mean)],
                    color=COLOR[method], fmt="o", ms=3.1, mec="white", mew=.4,
                    elinewidth=.7, capsize=1.2)


    for ax, kappa in zip(top, prediction["parameters"]["kappas"]["additive"]):
        curves = prediction["additive"][str(kappa)]
        base = {r["N"]: r for r in curves["pref"]}
        for method in REGRESSION:
            curve = curves[method]
            ax.plot([r["N"] / np.sqrt(kappa) for r in curve],
                    [r["mse"] / base[r["N"]]["mse"] for r in curve],
                    color=COLOR[method], ls=":" if method == "pref" else "-",
                    lw=1.6 if method == "flat" else 1.0)
            rows = sorted([r for r in regression["additive"] if r["kappa"] == kappa and r["method"] == method],
                          key=lambda r: r["N"])
            measurements(ax, [r["N"] / np.sqrt(kappa) for r in rows], rows, method)
            selected.extend({"panel": "regression", "kappa": kappa, "N": r["N"], "method": method} for r in rows)
        ax.set_title(rf"$\kappa={kappa:,}$", fontsize=8, pad=3)
        ax.set_xticks(np.array([64, 256, 1024]) / np.sqrt(kappa))
        ax.xaxis.set_major_formatter(FuncFormatter(lambda x, pos: f"{x:.3g}"))

    for ax, n in zip(bottom, (64, 128, 256)):
        for method in ("flat", "pref", "lf"):
            rows = sorted([r for r in poisson["rows"] if r["n"] == n and r["fmt"] == "bf16"
                           and r["regime"] == "A" and r["mode"] == "SR" and r["method"] == method
                           and r["N"] & (r["N"] - 1) == 0], key=lambda r: r["N"])
            assert [r["N"] for r in rows] == [64, 128, 256, 512, 1024]
            x = [r["N"] for r in rows]
            ax.plot(x, [r["predicted_ratio"] for r in rows], color=COLOR[method],
                    ls=":" if method == "pref" else "-", lw=1.6 if method == "flat" else 1.)
            measurements(ax, x, rows, method)
            selected.extend({"panel": "poisson", "n": n, "N": r["N"], "method": method,
                             "format": "bf16", "mode": "SR", "regime": "A"} for r in rows)
        ax.set_title(rf"${n}\times {n}$", fontsize=8, pad=3)
        ax.set_xticks([64, 256, 1024])
        ax.xaxis.set_major_formatter(FuncFormatter(lambda x, pos: f"{x:g}"))

    for ax in [*top, *bottom]:
        ax.margins(x=.1)
        ax.xaxis.set_minor_locator(NullLocator())
        ax.yaxis.set_minor_formatter(NullFormatter())
    for ax in (top[1], *bottom[1:]):
        ax.tick_params(labelleft=False)
    top[0].set_ylabel("Terminal MSE / Prefix", labelpad=2)
    for group, heading, xlabel in ((top, "Quantized gradients", r"Horizon $N/\sqrt{\kappa}$"),
                                   (bottom, "Poisson", "Products $N$")):
        left, right = group[0].get_position().x0, group[-1].get_position().x1
        fig.text((left + right) / 2, 107.2 / PT, heading, ha="center", va="bottom", fontsize=8)
        fig.text((left + right) / 2, 2.0 / PT, xlabel, ha="center", va="bottom", fontsize=8)
    handles = [Line2D([], [], color=COLOR[m], ls=":" if m == "pref" else "-",
                      marker="" if m == "pref" else "o", ms=3.2, mec="white", mew=.4, label=NAME[m])
               for m in REGRESSION]
    fig.legend(handles=handles, loc="upper center", bbox_to_anchor=(.5, 1.0),
               ncol=len(handles), frameon=False, handlelength=1.7, columnspacing=1.1,
               borderaxespad=0, borderpad=.1)
    destination = figures / "additive_lowprec.pdf"
    fig.savefig(destination, metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)
    receipt = {"selection": "Original regression MSE; three Poisson grids, bf16 SR, additive regime, Flat/Prefix/LF, all common dyadic horizons",
               "config_hash": poisson["config_hash"], "observations": selected,
               "solver_calls": 0, "bootstrap_resamples": 0,
               "inputs": {os.path.relpath(d / p, HERE): hashlib.sha256((d / p).read_bytes()).hexdigest()
                          for d, p in ((output, "pred.json"), (output, "summary.json"),
                                       (poisson_dir, "summary_lowprec.json"))},
               "figure_sha256": hashlib.sha256(destination.read_bytes()).hexdigest()}
    receipt["renderer_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (output / "article_figure_provenance.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("Saved", destination, "using", len(selected), "stored observations")
    return receipt


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "results")
    parser.add_argument("--figures", type=Path, default=HERE / "figures")
    parser.add_argument("--poisson", type=Path, default=HERE / "results" / "rerun_2pc" / "lowprec")
    args = parser.parse_args()
    build(args.output, args.figures, args.poisson)
