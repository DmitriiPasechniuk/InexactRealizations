import InexactRealizations.Averages.Moments
import InexactRealizations.Averages.Limits
import InexactRealizations.Accuracy.PrefixFactor
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Closed forms of the two actual geometric moment series. -/
namespace InexactRealizations.Averages
noncomputable section
open Filter Topology Real
open InexactRealizations.Classical
open scoped BigOperators

theorem uniform_series_difference (I : InexactRealizations.Operators.SpectralInterval) :
    (1 - decay I ^ 2) * (∑' k : ℕ, oddHarmonic k * decay I ^ (2 * k)) =
      decay I / 2 * (log (1 + decay I) - log (1 - decay I)) := by
  let f := fun k : ℕ ↦ oddHarmonic k * decay I ^ (2 * k)
  have hf : Summable f := by
    simpa only [uniform_moment] using spectral_series_summable (uniform I)
  have hshift : Summable (fun k : ℕ ↦ f (k + 1)) := hf.comp_injective Nat.succ_injective
  have hscale : Summable (fun k ↦ decay I ^ 2 * f k) := hf.mul_left _
  have hlog := hasSum_log_sub_log_of_abs_lt_one
    (show |decay I| < 1 by rw [abs_of_pos (decay_mem I).1]; exact (decay_mem I).2)
  have ht := hlog.mul_left (decay I / 2)
  have he : (fun k : ℕ ↦ decay I / 2 * (2 * (1 / (2 * (k : ℝ) + 1)) * decay I ^ (2 * k + 1))) =
      fun k ↦ f (k + 1) - decay I ^ 2 * f k := by
    funext k
    dsimp only [f]
    simp only [oddHarmonic, Finset.sum_range_succ]
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add, pow_add]
    simp only [pow_one, one_div]
    ring
  rw [he] at ht
  have hz : f 0 = 0 := by simp [f, oddHarmonic]
  have hshiftval : (∑' k : ℕ, f (k + 1)) = ∑' k : ℕ, f k := by
    have hh := hf.tsum_eq_zero_add
    simpa only [hz, zero_add] using hh.symm
  have hh := ht.tsum_eq
  rw [hshift.tsum_sub hscale, hshiftval, tsum_mul_left] at hh
  exact (by ring : (1 - decay I ^ 2) * (∑' k : ℕ, f k) =
    (∑' k : ℕ, f k) - decay I ^ 2 * (∑' k : ℕ, f k)).trans hh

theorem condition_sqrt_gt_one (I : InexactRealizations.Operators.SpectralInterval) : 1 < sqrt I.kappa := by
  have hk : 1 < I.kappa := (lt_div_iff₀ I.mu_pos).mpr (by simpa [InexactRealizations.Operators.SpectralInterval.kappa] using I.mu_lt_L)
  nlinarith [sq_sqrt (by linarith : 0 ≤ I.kappa), sqrt_nonneg I.kappa]

theorem decay_log_difference (I : InexactRealizations.Operators.SpectralInterval) :
    log (1 + decay I) - log (1 - decay I) = log I.kappa / 2 := by
  have hq := decay_mem I
  have hs := condition_sqrt_gt_one I
  rw [← log_div (by linarith : 1 + decay I ≠ 0) (by linarith : 1 - decay I ≠ 0)]
  have he : (1 + decay I) / (1 - decay I) = sqrt I.kappa := by
    rw [InexactRealizations.Accuracy.decay_eq_condition]
    field_simp
    ring
  rw [he]
  exact log_sqrt (show 0 ≤ I.kappa from (div_pos (I.mu_pos.trans I.mu_lt_L) I.mu_pos).le)

theorem arcsine_series (I : InexactRealizations.Operators.SpectralInterval) :
    (∑' k : ℕ, moment (arcsine I) k * decay I ^ (2 * k)) = decay I ^ 2 / (1 - decay I ^ 2) ^ 2 := by
  simp_rw [arcsine_moment, pow_mul]
  exact tsum_coe_mul_geometric_of_norm_lt_one (by
    rw [norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [(decay_mem I).1, (decay_mem I).2])

theorem uniform_series (I : InexactRealizations.Operators.SpectralInterval) :
    (∑' k : ℕ, moment (uniform I) k * decay I ^ (2 * k)) =
      decay I * log I.kappa / (4 * (1 - decay I ^ 2)) := by
  simp_rw [uniform_moment]
  have hh := uniform_series_difference I
  rw [decay_log_difference] at hh
  have hd : 1 - decay I ^ 2 ≠ 0 := by nlinarith [(decay_mem I).1, (decay_mem I).2]
  apply (eq_div_iff (mul_ne_zero (by norm_num) hd)).mpr
  nlinarith

end
end InexactRealizations.Averages
