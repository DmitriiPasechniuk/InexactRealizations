import InexactRealizations.Operators.Prefix.Gain
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The asymptotic statement also uses mathlib's standard equivalence relation.
Use: `InexactRealizations.Operators.Prefix.gain_isEquivalent_rpow` feeds
`InexactRealizations.Operators.TwoTerm.optimal_asymptotic` (The asymptotic optimal value for any family of finite
prefix-exact recurrences).
-/
namespace InexactRealizations.Operators.Prefix
noncomputable section
open Filter
open scoped Topology Asymptotics
variable (I : SpectralInterval)

/-- The stated quantitative bound `0 ≤ shape N`. -/
theorem shape_nonneg (N : ℕ) (hN : 1 ≤ N) : 0 ≤ shape N := by
  dsimp [shape]
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (0 : ℝ) ≤ N - 1 := by linarith
  have h2 : (0 : ℝ) ≤ 2 * N - 1 := by linarith
  positivity

/-- Exact identity `(realization I).gain I N * I.delta / (I.epsilon N * (N : ℝ) * Real.sqrt N) = 2
* Real.sqrt ((4 / 3 : ℝ) - 1 / N + (2 / 3 : ℝ) * (1 / N) ^ 2)`.
-/
theorem normalized_gain_eq (N : ℕ) (hN : 1 ≤ N) :
    (realization I).gain I N * I.delta /
      (I.epsilon N * (N : ℝ) * Real.sqrt N) =
      2 * Real.sqrt ((4 / 3 : ℝ) - 1 / N + (2 / 3 : ℝ) * (1 / N) ^ 2) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs := Real.sqrt_pos.mpr hn
  have he : I.epsilon N ≠ 0 := by dsimp [SpectralInterval.epsilon]; exact one_div_ne_zero (I.den_ne N)
  have hd : I.delta ≠ 0 := ne_of_gt I.delta_pos
  have hpoly : shape N / ((N : ℝ) * Real.sqrt N) ^ 2 =
      (4 / 3 : ℝ) - 1 / N + (2 / 3 : ℝ) * (1 / N) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hn.le]
    dsimp [shape]
    field_simp
    ring
  rw [← hpoly, Real.sqrt_div (shape_nonneg N hN),
    Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hn hs), gain_exact I N hN]
  field_simp

/-- The asymptotic assertion; `N * sqrt N` is `N^(3/2)`.

Convergence along the specified source filter to the specified limit: `Tendsto (fun N : ℕ =>
(realization I).gain I N * I.delta / (I.epsilon N * (N : ℝ) * Real.sqrt N)) atTop (𝓝 (4 /
Real.sqrt 3))`.
-/
theorem gain_asymptotic :
    Tendsto (fun N : ℕ => (realization I).gain I N * I.delta /
      (I.epsilon N * (N : ℝ) * Real.sqrt N)) atTop (𝓝 (4 / Real.sqrt 3)) := by
  have h : Tendsto (fun N : ℕ => (4 / 3 : ℝ) - 1 / N +
      (2 / 3 : ℝ) * (1 / N) ^ 2) atTop (𝓝 (4 / 3 : ℝ)) := by
    have hi : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    convert! (tendsto_const_nhds.sub hi).add (hi.pow 2 |>.const_mul (2 / 3 : ℝ)) using 1
    norm_num
  have hc : 2 * Real.sqrt (4 / 3 : ℝ) = 4 / Real.sqrt 3 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
    ring
  rw [← hc]
  apply (h.sqrt.const_mul 2).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact (normalized_gain_eq I N hN).symm

end
end InexactRealizations.Operators.Prefix
