import InexactRealizations.Averages.FiniteUpper
import InexactRealizations.Averages.DecayBounds

/-! The finite Prefix variance approaches its exact infinite-horizon value
uniformly when N/sqrt(kappa) grows. The explicit remainder is derived from
the actual response formula, rather than supplied as a premise. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Real
open InexactRealizations.Classical

theorem uniform_limit_pos (I : InexactRealizations.Operators.SpectralInterval) : 0 < spectralLimit (uniform I) := by
  have hk : 1 < I.kappa := (lt_div_iff₀ I.mu_pos).mpr (by simpa [InexactRealizations.Operators.SpectralInterval.kappa] using I.mu_lt_L)
  rw [uniform_limit_value, uniform_denominator]
  exact div_pos (mul_pos (sqrt_pos.mpr (lt_trans zero_lt_one hk)) (log_pos hk))
    (mul_pos (I.mu_pos.trans I.mu_lt_L) I.delta_pos)

theorem linear_exp_remainder (x : ℝ) : (x + 1) * exp (-2 * x) ≤ exp (-x) := by
  have hh := mul_le_mul_of_nonneg_right (add_one_le_exp x) (exp_pos (-2 * x)).le
  exact hh.trans_eq (by rw [← exp_add]; congr 1; ring)

theorem uniform_prefix_ratio (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (hk : 9 ≤ I.kappa) (hlog : 1 ≤ log I.kappa) (hN : 0 < N) (hNk : (N : ℝ) ≤ I.kappa) :
    (uniform I).variance (history I N) ≤
      (1 + 128 * exp (-((N : ℝ) / sqrt I.kappa))) * spectralLimit (uniform I) := by
  let q := decay I
  let x := (N : ℝ) / sqrt I.kappa
  let B := spectralLimit (uniform I)
  have hq : 0 < q := (decay_mem I).1
  have hq1 : q < 1 := (decay_mem I).2
  have hqhalf : 1 / 2 ≤ q := decay_lower_half I hk
  have hs : 2 ≤ sqrt I.kappa := by
    nlinarith [sqrt_nonneg I.kappa, sq_sqrt (by linarith : 0 ≤ I.kappa)]
  have hspos : 0 < sqrt I.kappa := by linarith
  have hdiff : 0 < 1 - q ^ 2 := by nlinarith
  have hln : 0 < log I.kappa := by linarith
  have hmoment : oddHarmonic N ≤ 2 * log I.kappa := by
    have hn : 0 < (N : ℝ) := by exact_mod_cast hN
    have hl := log_le_log hn hNk
    linarith [oddHarmonic_log_bound N]
  have hcoef : 4 * oddHarmonic N / (q * log I.kappa) ≤ 16 := by
    apply (div_le_iff₀ (mul_pos hq hln)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hqhalf hln.le]
  have hbracket : 2 * ((N : ℝ) + 1) * (1 - q ^ 2) + 1 ≤ 8 * (x + 1) := by
    have hb := mul_le_mul_of_nonneg_left (one_sub_decay_square_bound I)
      (show 0 ≤ 2 * ((N : ℝ) + 1) by positivity)
    have hi : (sqrt I.kappa)⁻¹ ≤ (1 / 2 : ℝ) := by
      simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hs
    dsimp only [q, x]
    simp only [div_eq_mul_inv] at hb ⊢
    nlinarith
  have hfactor : (4 * oddHarmonic N / (q * log I.kappa)) * q ^ (2 * N) *
      (2 * ((N : ℝ) + 1) * (1 - q ^ 2) + 1) ≤ 128 * exp (-x) := by
    have hm0 := oddHarmonic_nonneg N
    have hc0 : 0 ≤ 4 * oddHarmonic N / (q * log I.kappa) := by positivity
    have hb0 : 0 ≤ 2 * ((N : ℝ) + 1) * (1 - q ^ 2) + 1 := by positivity
    have hp := mul_le_mul hcoef (decay_even_power_bound I N) (pow_nonneg hq.le _) (by norm_num : (0 : ℝ) ≤ 16)
    have hh := mul_le_mul hp hbracket hb0 (by positivity : 0 ≤ 16 * exp (-2 * x))
    exact hh.trans (by nlinarith [linear_exp_remainder x])
  have he : (16 / I.delta ^ 2) * oddHarmonic N * q ^ (2 * N) *
      (2 * ((N : ℝ) + 1) + (1 - q ^ 2)⁻¹) = B *
        ((4 * oddHarmonic N / (q * log I.kappa)) * q ^ (2 * N) *
          (2 * ((N : ℝ) + 1) * (1 - q ^ 2) + 1)) := by
    have hB : B = (16 / I.delta ^ 2) * (q * log I.kappa / (4 * (1 - q ^ 2))) := by
      dsimp only [B, spectralLimit]
      rw [uniform_series]
    rw [hB]
    field_simp [hq.ne', hln.ne', hdiff.ne']
  have hu := uniform_finite_upper I N hN
  rw [he] at hu
  have hf := mul_le_mul_of_nonneg_left hfactor (uniform_limit_pos I).le
  calc
    _ ≤ B + B * (128 * exp (-x)) := hu.trans (add_le_add le_rfl hf)
    _ = _ := by dsimp only [B, x]; ring

end
end InexactRealizations.Averages
