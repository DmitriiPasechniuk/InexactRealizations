"""Call profiles at the lower spectral bound (computed from the paper's formulas).

For Prefix, sine-Jacobi, Flat and Balanced at one horizon, the figure shows the signed ratios
    s -> N Phi_s(mu) / (-S_N)                (responses, additive corner; left)
    s -> N Phi_s(mu) pi_s(mu) / (-D_N)       (response-query products, relative corner; right)
with S_N = (1-eps)/mu and D_N = 2 eps N^2/(L-mu), on linear scales. By the corner values
(eq:corners), the signed responses of every realization sum to -S_N and the signed products
to -D_N, so each profile averages to 1 and the equalized profile is the horizontal line 1:
Flat equalizes the responses, Balanced the products.

    python3 profiles.py            # writes figures/profiles.pdf
"""

import argparse
import logging
from pathlib import Path

import matplotlib

matplotlib.use("pdf")
import matplotlib.pyplot as plt
import numpy as np
from common import NAME, epsilon, prepare, responses
from matplotlib.lines import Line2D

HERE = Path(__file__).resolve().parent
METHODS = ("pref", "sine", "flat", "balanced")
# Colour-blind-safe set (Okabe-Ito hues; checked for CVD separation), each method also
# with its own line style and marker. Prefix keeps the dotted line of the other figures.
STYLE = {
    "pref": {"color": "#000000", "ls": ":", "marker": "^"},
    "sine": {"color": "#d65b25", "ls": "--", "marker": "v"},
    "flat": {"color": "#2377b4", "ls": "-", "marker": "o"},
    "balanced": {"color": "#009e73", "ls": "-.", "marker": "s"},
}
WIDTH_IN = 5.13   # text width of the Springer Nature single-column layout, so that fonts print at size
HEIGHT_IN = 1.6   # about 4 cm
PRODUCT_RANGE = (-1.3, 3.0)


def profiles(N=32, kappa=100.0, L=1.0):
    """Call profiles at mu = L/kappa for every method in METHODS.

    "response_ratio" = N Phi_s(mu)/(-S_N) and "product_ratio" = N Phi_s(mu) pi_s(mu)/(-D_N)
    are the plotted signed ratios; "responses" and "products" are their moduli.
    """
    mu = L / kappa
    eps = epsilon(N, mu, L)
    S = (1 - eps) / mu
    D = 2 * eps * N * N / (L - mu)
    out = {"N": N, "mu": mu, "L": L, "eps": eps, "S": S, "D": D}
    for method in METHODS:
        _, q, phi = responses(prepare(method, N, mu, L), np.array([mu]))
        response = -phi[:, 0] / (S / N)
        product = -phi[:, 0] * q[:, 0] / (D / N)
        out[method] = {
            "response_ratio": response,
            "product_ratio": product,
            "responses": np.abs(response),
            "products": np.abs(product),
            "signs": np.sign(phi[:, 0]),
            "product_signs": np.sign(phi[:, 0] * q[:, 0]),
        }
    return out


def build(figures=None, N=32, kappa=100.0):
    figures = Path(figures or HERE / "figures")
    figures.mkdir(parents=True, exist_ok=True)
    logging.getLogger("fontTools.ttLib.tables._h_e_a_d").setLevel(logging.ERROR)
    plt.rcParams.update({"font.family": "serif", "font.serif": ["DejaVu Serif"],
                         "mathtext.fontset": "cm", "font.size": 8,
                         "axes.labelsize": 8, "legend.fontsize": 7,
                         "xtick.labelsize": 7, "ytick.labelsize": 7,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "axes.linewidth": .6, "axes.grid": True,
                         "grid.color": "#e6e5e0", "grid.linewidth": .5,
                         "lines.linewidth": 1.1, "pdf.fonttype": 42})
    data = profiles(N, kappa)
    calls = np.arange(N)
    fig, axes = plt.subplots(1, 2, figsize=(WIDTH_IN, HEIGHT_IN))
    labels = {"response_ratio": r"$N\Phi_s(\mu)/(-S_N)$",
              "product_ratio": r"$N\Phi_s(\mu)\pi_s(\mu)/(-D_N)$"}
    for ax, key in zip(axes, ("response_ratio", "product_ratio")):
        for offset, method in enumerate(METHODS):
            style = STYLE[method]
            ax.plot(calls, data[method][key], color=style["color"], ls=style["ls"],
                    marker=style["marker"], markevery=(offset, len(METHODS)), ms=3.4,
                    mec="white", mew=.35, clip_on=True)
        ax.set_xlim(-.8, N - .2)
        ax.set_xticks([0, 8, 16, 24, N - 1])
        ax.set_xlabel(r"call $s$", labelpad=1)
        ax.set_ylabel(labels[key], labelpad=2)
    axes[0].set_ylim(0, 3.7)
    axes[0].set_yticks([0, 1, 2, 3])
    axes[1].set_ylim(*PRODUCT_RANGE)
    axes[1].set_yticks([-1, 0, 1, 2, 3])
    # Flat's products leave the plotted range: state the extreme values where the curve exits.
    flat = data["flat"]["product_ratio"]
    top, bottom = int(np.argmax(flat)), int(np.argmin(flat))
    color = STYLE["flat"]["color"]
    axes[1].text(9.0, 2.62, rf"$\uparrow$ ${flat[top]:.1f}$ at $s={top}$", color=color, fontsize=6.5,
                 ha="left", va="center")
    axes[1].text(11.0, -.95, rf"$\downarrow$ ${flat[bottom]:.1f}$ at $s={bottom}$", color=color,
                 fontsize=6.5, ha="left", va="center")
    handles = [Line2D([], [], color=STYLE[m]["color"], ls=STYLE[m]["ls"], marker=STYLE[m]["marker"],
                      ms=3.4, mec="white", mew=.35, label=NAME[m]) for m in METHODS]
    # One column in the upper left: above Flat's line at 1 and clear of the other curves.
    axes[0].legend(handles=handles, loc="upper left", ncol=1, frameon=False, handlelength=2.4,
                   borderaxespad=.2, labelspacing=.3)
    fig.tight_layout(w_pad=1.5, pad=.2)
    destination = figures / "profiles.pdf"
    fig.savefig(destination, pad_inches=.02, metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)
    print("Saved", destination)
    return destination


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--figures", type=Path, default=HERE / "figures")
    parser.add_argument("--N", type=int, default=32)
    parser.add_argument("--kappa", type=float, default=100.0)
    args = parser.parse_args()
    build(args.figures, args.N, args.kappa)
