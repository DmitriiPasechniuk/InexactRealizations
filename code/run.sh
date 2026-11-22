#!/bin/sh
# Recompute every figure, table and printed number of bezout.tex.
#   ./run.sh                 all stages, in this order
#   ./run.sh STAGE ...       selected stages
# Stages and outputs (results/ and figures/ are regenerated, never edited by hand):
#   regression  run_all.py additive: ridge experiment with Flat, Prefix, LF/fractal, DFB, M-ASG and Prefix with
#               tail averaging (mean of x_K..x_N, K = ceil(N/2)), 2048 trials (about 4 min)
#               -> results/pred.json, results/raw_additive.npz, results/summary.json, results/report.md
#   consensus   rerun_2pc.py consensus: coupled cycles, Balanced by Algorithm 2 (2'C), 2048 trials (about 1 min)
#               -> results/rerun_2pc/consensus/{pred.json,raw_variation.npz,summary.json,report.md}
#   poisson     rerun_2pc.py lowprec: bf16/fp16/fp32 Poisson study with float64 controls
#               (about 2 h with 8 workers; with no results/pred_lowprec.json the predictions are
#               computed first, about 8 h more) -> results/rerun_2pc/lowprec/
#   precision   precision.py table: working-precision accuracy check (not printed in the article)
#               -> results/precision_2pc/table.{json,md}
#   budgets     budgets_table.py, budgets_lf.py: Table 1 (tab:budgets) -> results/budgets_table.txt, results/budgets_lf.txt
#   numbers     printed_numbers.py: gain constants, Poisson sqrt(kappa), dither variances, uniform-spectrum
#               comparison of Theorem 5.3(a)-(b) (seconds) -> results/printed_numbers.txt
#   figures     profiles.py -> figures/profiles.pdf (Figure 1);
#               article_figures.py -> figures/additive_lowprec.pdf (Figure 2);
#               plots.build, single row at kappa = 10^4 -> figures/variation.pdf (Figure 3)
set -eu
package_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$package_dir"
export MPLCONFIGDIR="${MPLCONFIGDIR:-${TMPDIR:-/tmp}/bezout-matplotlib}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-${TMPDIR:-/tmp}/bezout-cache}"
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1

first_python() {  # first interpreter that imports the given modules
    for candidate in "${PYTHON:-}" .venv/bin/python python3 /usr/bin/python3; do
        [ -n "$candidate" ] || continue
        if "$candidate" -c "import $1" >/dev/null 2>&1; then
            echo "$candidate"
            return
        fi
    done
    echo "No Python with $1 found; see README.md." >&2
    exit 1
}

if [ "$#" -eq 0 ]; then set -- regression consensus poisson precision budgets numbers figures; fi
mkdir -p results figures
for stage in "$@"; do
    echo "== $stage"
    case "$stage" in
        regression) "$(first_python numpy)" run_all.py additive ;;
        consensus) "$(first_python numpy)" rerun_2pc.py consensus ;;
        poisson)
            if [ -f results/pred_lowprec.json ]; then
                "$(first_python numpy)" rerun_2pc.py lowprec
            else
                "$(first_python numpy)" rerun_2pc.py lowprec --recompute-predictions
            fi ;;
        precision) "$(first_python numpy)" precision.py table ;;
        budgets)
            py=$(first_python "numpy, mpmath")
            "$py" budgets_table.py > results/budgets_table.txt 2> /dev/null
            "$py" budgets_lf.py > results/budgets_lf.txt 2> /dev/null ;;
        numbers) "$(first_python numpy)" printed_numbers.py > results/printed_numbers.txt ;;
        figures)
            py=$(first_python "numpy, matplotlib")
            "$py" profiles.py
            "$py" article_figures.py
            "$py" -c "import plots; plots.build(results='results/rerun_2pc/consensus', figures='figures', variation_kappas=[10000])" ;;
        *) echo "Unknown stage: $stage" >&2; exit 1 ;;
    esac
done
