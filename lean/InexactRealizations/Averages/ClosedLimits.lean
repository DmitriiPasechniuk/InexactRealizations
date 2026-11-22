import InexactRealizations.Averages.Series

/-! Both fixed-interval limits, with exactly the
printed physical scaling. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Filter Topology Real
open InexactRealizations.Classical

theorem four_decay_ratio (I : InexactRealizations.Operators.SpectralInterval) :
    4 * decay I / (1 - decay I ^ 2) = (I.kappa - 1) / sqrt I.kappa := by
  have hs := condition_sqrt_gt_one I
  have hk : 0 < I.kappa := div_pos (I.mu_pos.trans I.mu_lt_L) I.mu_pos
  have hsq := sq_sqrt hk.le
  have hden : 1 - decay I ^ 2 ≠ 0 := by nlinarith [(decay_mem I).1, (decay_mem I).2]
  apply (div_eq_div_iff hden (by linarith : sqrt I.kappa ≠ 0)).mpr
  rw [InexactRealizations.Accuracy.decay_eq_condition]
  field_simp
  linear_combination (4 * sqrt I.kappa) * hsq

theorem condition_delta (I : InexactRealizations.Operators.SpectralInterval) : (I.kappa - 1) * I.L = I.kappa * I.delta := by
  unfold InexactRealizations.Operators.SpectralInterval.kappa InexactRealizations.Operators.SpectralInterval.delta
  field_simp [I.mu_pos.ne']

theorem uniform_denominator (I : InexactRealizations.Operators.SpectralInterval) :
    (1 - I.kappa⁻¹) * I.L ^ 2 = I.L * I.delta := by
  have hL := (I.mu_pos.trans I.mu_lt_L).ne'
  unfold InexactRealizations.Operators.SpectralInterval.kappa InexactRealizations.Operators.SpectralInterval.delta
  field_simp

theorem arcsine_limit_value (I : InexactRealizations.Operators.SpectralInterval) : spectralLimit (arcsine I) = I.kappa / I.L ^ 2 := by
  unfold spectralLimit
  rw [arcsine_series]
  have hq := decay_mem I
  have hd : 1 - decay I ^ 2 ≠ 0 := by nlinarith [hq.1, hq.2]
  have hk : 0 < I.kappa := div_pos (I.mu_pos.trans I.mu_lt_L) I.mu_pos
  calc
    _ = (4 * decay I / (1 - decay I ^ 2)) ^ 2 / I.delta ^ 2 := by field_simp; ring
    _ = ((I.kappa - 1) / sqrt I.kappa) ^ 2 / I.delta ^ 2 := by rw [four_decay_ratio]
    _ = I.kappa / I.L ^ 2 := by
      rw [div_pow, sq_sqrt hk.le]
      unfold InexactRealizations.Operators.SpectralInterval.kappa InexactRealizations.Operators.SpectralInterval.delta
      field_simp [I.mu_pos.ne', (I.mu_pos.trans I.mu_lt_L).ne', (sub_pos.mpr I.mu_lt_L).ne']

theorem uniform_limit_value (I : InexactRealizations.Operators.SpectralInterval) :
    spectralLimit (uniform I) = sqrt I.kappa * log I.kappa / ((1 - I.kappa⁻¹) * I.L ^ 2) := by
  unfold spectralLimit
  rw [uniform_series]
  have hq := decay_mem I
  have hd : 1 - decay I ^ 2 ≠ 0 := by nlinarith [hq.1, hq.2]
  have hk : 0 < I.kappa := div_pos (I.mu_pos.trans I.mu_lt_L) I.mu_pos
  have hs := condition_sqrt_gt_one I
  have hscale : (I.kappa - 1) / (sqrt I.kappa * I.delta ^ 2) = sqrt I.kappa / (I.L * I.delta) := by
    field_simp [I.delta_pos.ne', (I.mu_pos.trans I.mu_lt_L).ne', (by linarith : sqrt I.kappa ≠ 0)]
    rw [sq_sqrt hk.le]
    exact condition_delta I
  calc
    _ = (4 * decay I / (1 - decay I ^ 2)) * log I.kappa / I.delta ^ 2 := by field_simp; ring
    _ = (I.kappa - 1) / (sqrt I.kappa * I.delta ^ 2) * log I.kappa := by rw [four_decay_ratio]; ring
    _ = sqrt I.kappa * log I.kappa / (I.L * I.delta) := by rw [hscale]; ring
    _ = _ := by rw [uniform_denominator]

theorem journal_arcsine_limit (I : InexactRealizations.Operators.SpectralInterval) :
    Tendsto (fun N : ℕ ↦ (arcsine I).variance (history I N)) atTop (𝓝 (I.kappa / I.L ^ 2)) := by
  rw [← arcsine_limit_value]
  exact prefix_variance_tendsto (arcsine I)

theorem journal_uniform_limit (I : InexactRealizations.Operators.SpectralInterval) :
    Tendsto (fun N : ℕ ↦ (uniform I).variance (history I N)) atTop
      (𝓝 (sqrt I.kappa * log I.kappa / ((1 - I.kappa⁻¹) * I.L ^ 2))) := by
  rw [← uniform_limit_value]
  exact prefix_variance_tendsto (uniform I)

end
end InexactRealizations.Averages
