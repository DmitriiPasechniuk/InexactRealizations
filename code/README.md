# Numbers, table and figures of the bezout article

`./run.sh` recomputes every figure, the table and the printed numbers of *Optimal Realizations of the
Chebyshev Iteration with Inexact Residuals*: `results/` and `figures/` are written by it and nothing else.
Python 3.11 or newer with NumPy and Matplotlib (`requirements.txt`) runs the experiments and figures;
the `budgets` stage also needs mpmath (`run.sh` picks, per stage, the first of `$PYTHON`, `.venv/bin/python`,
`python3`, `/usr/bin/python3` that imports the required modules).

```sh
python3 -m venv .venv && .venv/bin/python -m pip install -r requirements.txt
./run.sh                                   # all stages (the Poisson stage takes hours)
./run.sh regression consensus precision budgets numbers figures   # everything except the Poisson study, about 11 min
```

| Article item | Stage: script | Output |
|---|---|---|
| Figure 1 (normalized responses and products) | `figures`: `profiles.py` | `figures/profiles.pdf` |
| Figure 2 (regression and Poisson terminal MSE) | `figures`: `article_figures.py` | `figures/additive_lowprec.pdf` |
| Figure 3 (consensus, one row at κ = 10⁴) | `figures`: `plots.build(..., variation_kappas=[10000])` | `figures/variation.pdf` |
| Table 1 (`tab:budgets`) | `budgets`: `budgets_table.py`, `budgets_lf.py` (LF/fractal refinement) | `results/budgets_table.txt`, `results/budgets_lf.txt` |
| Regression ratios and intervals, including Flat over Prefix with tail averaging (Sections 1 and 6) | `regression`: `run_all.py additive` | `results/pred.json`, `results/summary.json`, `results/report.md` |
| Gain constants 4/√3, 2.137936…, 2 and the reductions 13.4 %, 6.45 % (Sections 1 and 4); √κ ≈ 41, 82, 164 and the dither variances (Section 6); uniform-spectrum comparison of Theorem 5.3(a)–(b) at the Poisson horizons (Section 6) | `numbers`: `printed_numbers.py` | `results/printed_numbers.txt` |
| Consensus ratios and intervals (Section 6) | `consensus`: `rerun_2pc.py consensus` | `results/rerun_2pc/consensus/summary.json`, `report.md` |
| Poisson numbers, float64 controls (Section 6, Appendix F) | `poisson`: `rerun_2pc.py lowprec` | `results/rerun_2pc/lowprec/summary_lowprec.json`, `report_lowprec.md` |
| Working-precision accuracy of Algorithm 2, Flat and Prefix (check only; not printed in the article) | `precision`: `precision.py table` | `results/precision_2pc/table.json`, `table.md` |

All plotted quantities are divided by Prefix at the same instance and horizon; statistical markers have 95%
paired-bootstrap intervals. Balanced is executed by Algorithm 2 (`balanced2c`, averaged-Prefix form with
compensated point averages) in the consensus and Poisson stages; the regression experiment has no Balanced.
The Poisson stage reuses `results/pred_lowprec.json` when present (after a same-history check) and otherwise
computes the predictions first.

## Models and methods

**Distributed ridge regression.** The 64-dimensional Hessian is
`H = mu I + (1-mu) vv^⊤`, with `v = 1/sqrt(64)` and four workers.
The initial error has squared energy 0.9 in the weak eigenspace and 0.1
along v. Each worker rounds its gradient with subtractive uniform dither;
step `h = sigma sqrt(12 workers / dimension)` gives averaged covariance
`sigma^2 I / dimension`. The condition numbers are 100 and 10,000,
with `sigma / mu = 0.3`.

Methods: Flat, Prefix, LF/fractal, DFB, M-ASG and Prefix with tail averaging.
DFB averages all N+1 iterates, including the initial point, with step 1/L and
momentum one. The tail average returns the mean of the Prefix iterates
x_K, ..., x_N with K = ceil(N/2).
M-ASG uses p=1 and first-stage length floor(N/2). The MSE predictions
include each method's own terminal bias.

**Coupled cycles.** Two cycles of 16 vertices share a varying inter-network
channel. On the antisymmetric subspace, the reference spectrum spans
`[1/kappa, 1]`. The initial signal has squared amplitude 0.475 in each
endpoint mode and total energy 0.05 across the interior modes.
Independent channel signs have amplitude `delta = 0.01 mu`.
The condition numbers are 10,000 and 40,000.

Methods: Balanced, Prefix, LF/fractal and sine–Jacobi. All have the same
nominal terminal. The signal matrix has entries
`T[j,s] = a[j] Phi[s](lambda[j]) pi[s](lambda[j])`.
Its largest singular value predicts local temporal-energy gain;
`delta^2 ||T||_F^2` is the leading noise variance. Simulations execute the
full perturbed oracle, while deterministic gain measurements differentiate
the actual iteration.

**Poisson solutions.** Each Poisson solution has independent Gaussian sine coefficients
divided by `j^2+k^2`, then normalized (`poisson.py`).

Both experiments use horizons
`64,128,256,320,384,512,640,768,960,1024` and a denser prediction grid.
LF runs only at dyadic horizons. Every method starts afresh at each horizon.
The problem and random-tape seeds are fixed in `models.py` and `run_all.py`.
Methods share each trial's random tape; dither errors can differ because
their queried gradients differ.
