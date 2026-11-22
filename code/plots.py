"""Two single-page vector PDFs: theoretical curves and measured markers."""

import json
import logging
from pathlib import Path

import matplotlib

matplotlib.use("pdf")
import matplotlib.pyplot as plt
import numpy as np
from common import ADDITIVE, NAME, VARIATION
from matplotlib.lines import Line2D
from matplotlib.ticker import FuncFormatter, MaxNLocator, NullFormatter, NullLocator

HERE = Path(__file__).resolve().parent
COLOR = {
    "flat": "#2377b4",
    "balanced": "#2377b4",
    "pref": "#666666",
    "tail": "#b5651d",
    "lf": "#009e73",
    "dfb": "#8868b0",
    "masg": "#c48a00",
    "sine": "#d65b25",
}
ROW_SIZE_IN = (5.13, 1.68)  # one-row variation figure at the article's text width, printed at 1:1
ROW_PT = 72 * ROW_SIZE_IN[1]  # its vertical positions are fixed in points from the bottom edge


def build(results=None, figures=None, variation_kappas=None):
    """variation_kappas: optional subset of kappas for the left variation columns,
    plotted against N. With a single kappa (the article's figure) the four panels
    form one row: energy gain and variance at that kappa, then LF/fractal."""
    results = Path(results or HERE / "results")
    logging.getLogger("fontTools.ttLib.tables._h_e_a_d").setLevel(logging.ERROR)
    plt.rcParams.update(
        {
            "font.family": "serif",
            "font.serif": ["DejaVu Serif"],
            "mathtext.fontset": "cm",
            "font.size": 8,
            "axes.labelsize": 8,
            "legend.fontsize": 7,
            "xtick.labelsize": 7,
            "ytick.labelsize": 7,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "axes.linewidth": 0.6,
            "axes.grid": True,
            "grid.color": "#e6e5e0",
            "grid.linewidth": 0.5,
            "lines.linewidth": 1.3,
            "pdf.fonttype": 42,
        }
    )
    P = json.loads((results / "pred.json").read_text())
    S = json.loads((results / "summary.json").read_text())
    output = Path(figures or HERE / "figures")
    output.mkdir(parents=True, exist_ok=True)
    for task, methods in [("additive", ADDITIVE), ("variation", VARIATION)]:
        if not S[task]:
            continue
        columns = P["parameters"]["kappas"][task]
        single = task == "variation" and variation_kappas is not None
        if single:
            columns = list(variation_kappas)
        one_row = single and len(columns) == 1
        if one_row:
            fig, row_axes = plt.subplots(1, 4, figsize=ROW_SIZE_IN)
            fig.subplots_adjust(left=.1, right=.985, bottom=26.2 / ROW_PT, top=89.06 / ROW_PT, wspace=.52)
            # axes[row, col] as in the two-row layout: rows energy/variance, columns kappa/LF.
            axes = np.array([[row_axes[0], row_axes[2]], [row_axes[1], row_axes[3]]])
        elif task == "variation":
            fig, axes = plt.subplots(
                2,
                len(columns) + 1,
                figsize=(6.5, 4.0) if single and len(columns) == 1 else (6.5, 5.15),
                sharex="col",
                gridspec_kw={"width_ratios": (*[1] * len(columns), 0.68)},
            )
            for row in range(2):
                for col in range(1, len(columns)):
                    axes[row, col].sharey(axes[row, 0])
                    axes[row, col].tick_params(labelleft=False)
        else:
            fig, axes = plt.subplots(2, 2, figsize=(6.5, 5.15), sharex="col")
        handles = [
            Line2D(
                [],
                [],
                color=COLOR[m],
                ls=":" if m == "pref" else "-",
                marker="o",
                ms=3,
                markeredgecolor="white",
                markeredgewidth=0.4,
                label=NAME[m],
            )
            for m in methods
        ]
        fig.legend(
            handles=handles,
            loc="upper center",
            bbox_to_anchor=(0.5, 1.0 if one_row else 0.998),
            ncol=len(methods),
            frameon=False,
            handlelength=1.7,
            columnspacing=1.1,
            **({"borderaxespad": 0, "borderpad": 0.1} if one_row else {}),
        )
        for col, kappa in enumerate(columns):
            scale = 1.0 if single else np.sqrt(kappa)
            curves = P[task][str(kappa)]
            reference = {r["N"]: r for r in curves["pref"]}
            for method in methods:
                if task == "variation" and method == "lf":
                    continue
                curve = curves[method]
                x = np.array([r["N"] / scale for r in curve])
                for row in range(2):
                    field = (
                        "energy"
                        if (task == "additive" and row == 1)
                        or (task == "variation" and row == 0)
                        else "mse"
                        if task == "additive"
                        else "gamma"
                    )
                    y = [r[field] / reference[r["N"]][field] for r in curve]
                    axes[row, col].plot(
                        x,
                        y,
                        color=COLOR[method],
                        ls=":" if method == "pref" else "-",
                        lw=1.8 if method in ("flat", "balanced") else 1.2,
                    )
            for r in S[task]:
                if r["kappa"] != kappa:
                    continue
                if task == "variation" and r["method"] == "lf":
                    continue
                x = r["N"] / scale
                m = r["method"]
                energy_row = 1 if task == "additive" else 0
                stat_row = 1 - energy_row
                axes[energy_row, col].plot(
                    x,
                    r["energy_ratio"],
                    "o",
                    ms=3.3,
                    color=COLOR[m],
                    mec="white",
                    mew=0.45,
                )
                q = r["ratio"]
                axes[stat_row, col].errorbar(
                    x,
                    q["value"],
                    yerr=[
                        [max(0, q["value"] - q["lo"])],
                        [max(0, q["hi"] - q["value"])],
                    ],
                    fmt="o",
                    ms=3.3,
                    color=COLOR[m],
                    mec="white",
                    mew=0.45,
                    elinewidth=0.7,
                    capsize=1.3,
                )
            for row, ax in enumerate(axes[:, col]):
                ax.set_xscale("log")
                ax.set_yscale("linear" if task == "variation" else "log")
                ax.axhline(1, color=COLOR["pref"], lw=0.7, ls=":")
                ticks = np.array([64, 256, 1024] if single else [64, 128, 256, 512, 1024]) / scale
                ax.set_xticks(ticks)
                ax.xaxis.set_major_formatter(FuncFormatter((lambda x, p: f"{x:g}") if single else (lambda x, p: f"{x:.2g}")))
                ax.xaxis.set_minor_locator(NullLocator())
                ax.yaxis.set_minor_formatter(NullFormatter())
                if row == 0:
                    ax.set_title(rf"$\kappa={kappa:,}$")
                if row == 1:
                    ax.set_xlabel(r"Horizon $N$" if single else r"Horizon $N/\sqrt{\kappa}$")
                ylabel = (
                    ("Terminal MSE / Prefix", "Energy gain / Prefix")
                    if task == "additive"
                    else ("Local energy gain / Prefix", "Noise variance / Prefix")
                )
                if task == "additive" or col == 0:
                    ax.set_ylabel(ylabel[row])
                if task == "variation":
                    ax.yaxis.set_major_locator(MaxNLocator(4))
        if task == "variation":
            # LF is retained in a separate scale. Its normalized predictions
            # are kappa-independent in this commuting family; show both MC sets.
            kappas = P["parameters"]["kappas"][task]
            base = P[task][str(kappas[0])]
            ref = {r["N"]: r for r in base["pref"]}
            for row, field in enumerate(("energy", "gamma")):
                ax = axes[row, len(columns)]
                curve = base["lf"]
                x = [r["N"] for r in curve]
                y = [r[field] / ref[r["N"]][field] for r in curve]
                ax.plot(x, y, color=COLOR["lf"], lw=1.3)
                for ki, kappa in enumerate(kappas):
                    for r in S[task]:
                        if r["method"] != "lf" or r["kappa"] != kappa:
                            continue
                        marker = "o" if ki == 0 else "s"
                        face = COLOR["lf"] if ki == 0 else "white"
                        if row == 0:
                            ax.plot(
                                r["N"],
                                r["energy_ratio"],
                                marker=marker,
                                ms=3.3,
                                color=COLOR["lf"],
                                mfc=face,
                                mec=COLOR["lf"],
                                mew=0.6,
                            )
                        else:
                            q = r["ratio"]
                            ax.errorbar(
                                r["N"],
                                q["value"],
                                yerr=[
                                    [max(0, q["value"] - q["lo"])],
                                    [max(0, q["hi"] - q["value"])],
                                ],
                                fmt=marker,
                                ms=3.3,
                                color=COLOR["lf"],
                                mfc=face,
                                mec=COLOR["lf"],
                                mew=0.6,
                                elinewidth=0.7,
                                capsize=1.3,
                            )
                ax.set(xscale="log", yscale="log")
                ax.set_xticks([64, 256, 1024])
                ax.xaxis.set_major_formatter(FuncFormatter(lambda x, p: f"{x:g}"))
                ax.xaxis.set_minor_locator(NullLocator())
                ax.yaxis.set_minor_formatter(NullFormatter())
                ax.set_yticks([4, 8, 16] if row == 0 else [32, 128, 512])
                ax.yaxis.set_major_formatter(FuncFormatter(lambda x, p: f"{x:g}"))
                ax.yaxis.tick_right()
                if row == 0:
                    ax.set_title("LF/fractal")
                else:
                    ax.set_xlabel(r"Horizon $N$")
        if one_row:
            for row, title in enumerate(("Local energy gain", "Noise variance")):
                for ax in axes[row]:
                    ax.set_title(title, fontsize=8, pad=3)
                    ax.set_xlabel("")
                    ax.set_ylabel("")
                    ax.yaxis.tick_left()
                    ax.margins(x=0.1)
            axes[0, 0].set_ylabel("Ratio to Prefix", labelpad=2)
            for group, heading in ((row_axes[:2], rf"$\kappa={columns[0]:,}$"), (row_axes[2:], "LF/fractal")):
                left, right = group[0].get_position().x0, group[-1].get_position().x1
                fig.text((left + right) / 2, 100.6 / ROW_PT, heading, ha="center", va="bottom", fontsize=8)
                fig.text((left + right) / 2, 1.9 / ROW_PT, r"Horizon $N$", ha="center", va="bottom", fontsize=8)
            fig.savefig(output / f"{task}.pdf", metadata={"CreationDate": None, "ModDate": None})
        else:
            fig.tight_layout(rect=(0, 0, 1, 0.925))
            fig.savefig(output / f"{task}.pdf", bbox_inches="tight", pad_inches=0.03)
        plt.close(fig)
    print("Figures:", output)


def build_lowprec(output=None, figures=None):
    """Separate low-precision figure: SR lines and paired SR/RN markers."""
    output = Path(output or HERE / "results")
    figures = Path(figures or HERE / "figures")
    figures.mkdir(parents=True, exist_ok=True)
    summary = json.loads((output / "summary_lowprec.json").read_text())
    plt.rcParams.update({"font.family": "serif", "font.serif": ["DejaVu Serif"],
                         "mathtext.fontset": "cm", "font.size": 8,
                         "axes.labelsize": 8, "legend.fontsize": 7,
                         "xtick.labelsize": 7, "ytick.labelsize": 7,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "axes.linewidth": .6, "axes.grid": True,
                         "grid.color": "#e6e5e0", "grid.linewidth": .5,
                         "lines.linewidth": 1.3, "pdf.fonttype": 42})
    # Two regimes by two low formats. All grids stay in summary; use the
    # largest grid for this compact article figure, fixed by the design.
    n = max(summary["config"]["grids"])
    fig, axes = plt.subplots(2, 2, figsize=(6.5, 4.5), sharex=True)
    colors = dict(COLOR, balanced="#9b59b6")
    for i, regime in enumerate(("R", "A")):
        for j, fmt in enumerate(("fp16", "bf16")):
            ax = axes[i, j]
            for method in summary["config"]["methods"]:
                for mode in ("SR", "RN"):
                    rows = [r for r in summary["rows"] if r["n"] == n and r["regime"] == regime
                            and r["fmt"] == fmt and r["method"] == method and r["mode"] == mode]
                    rows.sort(key=lambda r: r["N"])
                    rows = [r for r in rows if r["ratio"] is not None]
                    if not rows:
                        continue
                    x = [r["N"] for r in rows]
                    if mode == "SR":
                        ax.plot(x, [r["predicted_ratio"] for r in rows], color=colors[method],
                                ls=":" if method == "pref" else "-", lw=1)
                    y = np.array([r["ratio"]["value"] for r in rows])
                    lo = np.array([r["ratio"]["lo"] for r in rows])
                    hi = np.array([r["ratio"]["hi"] for r in rows])
                    ax.errorbar(x, y, yerr=[np.maximum(0, y-lo), np.maximum(0, hi-y)],
                                fmt="o" if mode == "SR" else "s", ms=3,
                                color=colors[method], mfc=colors[method] if mode == "SR" else "white",
                                mew=.5, capsize=1, elinewidth=.6)
            ax.set(xscale="log", yscale="log")
            if i == 0:
                ax.set_title(f"{fmt}, {n} × {n} grid")
            if i == 1:
                ax.set_xlabel("Horizon N")
            if j == 0:
                ax.set_ylabel(("R: terminal MSE / Prefix", "A: terminal MSE / Prefix")[i])
    handles = [Line2D([], [], color=colors[m], label=NAME[m]) for m in summary["config"]["methods"]]
    handles += [Line2D([], [], color="black", marker="o", ls="", label="SR"),
                Line2D([], [], color="black", marker="s", mfc="white", ls="", label="RN")]
    fig.legend(handles=handles, loc="upper center", ncol=4, frameon=False)
    fig.tight_layout(rect=(0, 0, 1, .9))
    fig.savefig(figures / "lowprec.pdf", bbox_inches="tight", pad_inches=.03,
                metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)


def build_lowprec_additive(output=None, figures=None):
    """Render all additive grids and a precision-collapse view from saved rows."""
    output = Path(output or HERE / "results")
    figures = Path(figures or HERE / "figures")
    figures.mkdir(parents=True, exist_ok=True)
    summary = json.loads((output / "summary_lowprec.json").read_text())
    grids = summary["config"]["grids"]
    colors = dict(COLOR, balanced="#9b59b6")
    plt.rcParams.update({"font.family": "serif", "font.serif": ["DejaVu Serif"],
                         "mathtext.fontset": "cm", "font.size": 8,
                         "axes.labelsize": 8, "legend.fontsize": 7,
                         "xtick.labelsize": 7, "ytick.labelsize": 7,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "axes.linewidth": .6, "axes.grid": True,
                         "grid.color": "#e6e5e0", "grid.linewidth": .5,
                         "lines.linewidth": 1.1, "pdf.fonttype": 42})
    formats = [fmt for fmt in ("fp16", "bf16") if fmt in summary["config"]["formats"]]
    fig, axes = plt.subplots(len(formats), len(grids), figsize=(6.5, 4.25),
                             sharex=True, sharey=True, squeeze=False)
    for i, fmt in enumerate(formats):
        for j, n in enumerate(grids):
            ax = axes[i, j]
            for method in summary["config"]["methods"]:
                rows = sorted([r for r in summary["rows"] if r["regime"] == "A"
                               and r["mode"] == "SR" and r["fmt"] == fmt
                               and r["n"] == n and r["method"] == method], key=lambda r: r["N"])
                rows = [r for r in rows if r["ratio"] is not None]
                if not rows:
                    continue
                x = [r["N"] for r in rows]
                ax.plot(x, [r["predicted_ratio"] for r in rows], color=colors[method],
                        ls=":" if method == "pref" else "-", lw=1)
                if method != "pref":
                    y = np.array([r["ratio"]["value"] for r in rows])
                    lo = np.array([r["ratio"]["lo"] for r in rows])
                    hi = np.array([r["ratio"]["hi"] for r in rows])
                    ax.errorbar(x, y, yerr=[np.maximum(0, y-lo), np.maximum(0, hi-y)],
                                fmt="o", ms=3, color=colors[method], mfc=colors[method],
                                mec="white", mew=.4, capsize=1.2, elinewidth=.65)
            ax.set(xscale="log", yscale="log")
            ax.set_xticks([64, 256, 1024])
            ax.xaxis.set_major_formatter(FuncFormatter(lambda value, pos: f"{value:g}"))
            ax.xaxis.set_minor_locator(NullLocator())
            if i == 0:
                ax.set_title(rf"${n}\times{n}$ grid")
            if i == len(formats) - 1:
                ax.set_xlabel("Products N")
            if j == 0:
                ax.set_ylabel(f"{fmt}\nTerminal MSE / Prefix")
    handles = [Line2D([], [], color=colors[m], label=NAME[m]) for m in summary["config"]["methods"]]
    fig.legend(handles=handles, loc="upper center", ncol=5, frameon=False)
    fig.tight_layout(rect=(0, 0, 1, .925), w_pad=.8)
    fig.savefig(figures / "lowprec_additive.pdf", bbox_inches="tight", pad_inches=.03,
                metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)

    fig, axes = plt.subplots(1, len(grids), figsize=(6.5, 2.65), squeeze=False)
    for ax, n in zip(axes.ravel(), grids):
        for method in ("flat", "pref"):
            rows = [r for r in summary["rows"] if r["regime"] == "A" and r["mode"] == "SR"
                    and r["n"] == n and r["method"] == method and r["measured_noise"] is not None]
            if not rows:
                continue
            x = sorted({r["N"] for r in rows})
            groups = [[r for r in rows if r["N"] == N] for N in x]

            def normalized(group, key):
                return [r[key] / 2.0**(-2 * {"fp16": 11, "bf16": 8, "fp32": 24}[r["fmt"]])
                        for r in group]

            prediction = [np.mean(normalized(group, "predicted_noise")) for group in groups]
            measured = [normalized(group, "measured_noise") for group in groups]
            ax.plot(x, prediction, color=colors[method], lw=1)
            mask = np.array([N & (N - 1) == 0 for N in x])
            mean = np.array([np.mean(values) for values in measured])[mask]
            lo = np.array([np.min(values) for values in measured])[mask]
            hi = np.array([np.max(values) for values in measured])[mask]
            ax.errorbar(np.array(x)[mask], mean, yerr=[np.maximum(0, mean-lo), np.maximum(0, hi-mean)],
                        color=colors[method], fmt="o", ms=3.5, mfc="white", mew=.8,
                        elinewidth=.8, capsize=2)
        ax.set(xscale="log", yscale="log", title=rf"${n}\times{n}$ grid", xlabel="Products N")
        ax.set_xticks([64, 256, 1024])
        ax.xaxis.set_major_formatter(FuncFormatter(lambda value, pos: f"{value:g}"))
        ax.xaxis.set_minor_locator(NullLocator())
    axes[0, 0].set_ylabel(r"Excess MSE / $u^2$")
    handles = [Line2D([], [], color=colors[m], label=NAME[m]) for m in ("flat", "pref")]
    handles += [Line2D([], [], color="black", marker="o", mfc="white", ls="",
                      label="Mean and range over precisions")]
    fig.legend(handles=handles, loc="upper center", ncol=3, frameon=False)
    fig.tight_layout(rect=(0, 0, 1, .86), w_pad=1.2)
    fig.savefig(figures / "lowprec_floors.pdf", bbox_inches="tight", pad_inches=.03,
                metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)


def build_coherent_reaction(output):
    """Compact coefficient-rounding companion, using its saved trial summary."""
    output = Path(output)
    summary = json.loads((output / "summary.json").read_text())
    figures = HERE / "figures" if output.resolve() == (HERE / "results/coherent_reaction").resolve() else output / "figures"
    figures.mkdir(parents=True, exist_ok=True)
    colors = dict(COLOR, balanced="#9b59b6")
    plt.rcParams.update({"font.family": "serif", "font.serif": ["DejaVu Serif"],
                         "mathtext.fontset": "cm", "font.size": 8,
                         "axes.labelsize": 8, "legend.fontsize": 7,
                         "xtick.labelsize": 7, "ytick.labelsize": 7,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "axes.linewidth": .6, "axes.grid": True,
                         "grid.color": "#e6e5e0", "grid.linewidth": .5, "pdf.fonttype": 42})
    fig, axes = plt.subplots(1, 2, figsize=(6.5, 2.65))
    for ax, methods in zip(axes, (("balanced", "pref", "sine"), ("flat", "lf", "pref"))):
        for method in methods:
            rows = sorted([r for r in summary["rows"] if r["method"] == method], key=lambda r: r["N"])
            if not rows:
                continue
            x = [r["N"] for r in rows]
            ax.plot(x, [r["predicted_ratio"] for r in rows], color=colors[method],
                    ls=":" if method == "pref" else "-", lw=1.1, label=NAME[method])
            y = np.array([r["ratio"]["value"] for r in rows])
            lo = np.array([r["ratio"]["lo"] for r in rows])
            hi = np.array([r["ratio"]["hi"] for r in rows])
            ax.errorbar(x, y, yerr=[np.maximum(0, y-lo), np.maximum(0, hi-y)],
                        fmt="o", color=colors[method], ms=3.5, capsize=2, elinewidth=.7,
                        mec="white", mew=.4)
        ax.set(xscale="log", xlabel="Products N")
        ax.set_xticks(summary["config"]["horizons"])
        ax.xaxis.set_major_formatter(FuncFormatter(lambda value, pos: f"{value:g}"))
        ax.xaxis.set_minor_locator(NullLocator())
        ax.legend(frameon=False)
    axes[0].set(ylabel="Excess MSE / Prefix", title="Coherent reaction-coefficient rounding")
    axes[1].set(yscale="log", title="Flat and LF/fractal")
    fig.tight_layout(w_pad=2)
    fig.savefig(figures / "lowprec_coherent.pdf", bbox_inches="tight", pad_inches=.03,
                metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)


if __name__ == "__main__":
    build()
