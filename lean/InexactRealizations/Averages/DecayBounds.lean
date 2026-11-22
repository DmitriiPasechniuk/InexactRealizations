import InexactRealizations.Averages.ClosedLimits
import InexactRealizations.Operators.Chebyshev.DriftBudget

/-! Elementary uniform decay estimates used only for the joint range in
Their constants do not alter its sharp pi/sqrt(6) threshold. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Polynomial Polynomial.Chebyshev Real
open InexactRealizations.Classical

theorem decay_exp_bound (I : InexactRealizations.Operators.SpectralInterval) : decay I ≤ exp (-(sqrt I.kappa)⁻¹) := by
  have hs := condition_sqrt_gt_one I
  have hq : decay I = 1 - 2 / (sqrt I.kappa + 1) := by
    rw [InexactRealizations.Accuracy.decay_eq_condition]
    field_simp
    ring
  have hratio : (sqrt I.kappa)⁻¹ ≤ 2 / (sqrt I.kappa + 1) := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  calc
    _ ≤ exp (-(2 / (sqrt I.kappa + 1))) := by
      rw [hq]
      have hh := add_one_le_exp (-(2 / (sqrt I.kappa + 1)))
      linarith
    _ ≤ _ := exp_le_exp.mpr (neg_le_neg hratio)

theorem theta_condition_lower (I : InexactRealizations.Operators.SpectralInterval) : (sqrt I.kappa)⁻¹ ≤ theta I := by
  have hh := decay_exp_bound I
  change exp (-theta I) ≤ exp (-(sqrt I.kappa)⁻¹) at hh
  have ht := exp_le_exp.mp hh
  linarith

theorem decay_even_power_bound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    decay I ^ (2 * N) ≤ exp (-2 * ((N : ℝ) / sqrt I.kappa)) := by
  have hh := pow_le_pow_left₀ (decay_mem I).1.le (decay_exp_bound I) (2 * N)
  rw [← exp_nat_mul] at hh
  exact hh.trans_eq (congrArg exp (by push_cast; ring))

theorem epsilon_exp_bound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    I.epsilon N ≤ 2 * exp (-((N : ℝ) / sqrt I.kappa)) := by
  have hq := decay_mem I
  have hn : I.epsilon N ≤ 2 * decay I ^ N := by
    rw [InexactRealizations.Operators.SpectralInterval.epsilon, den_decay]
    have hp : 0 < decay I ^ N := pow_pos hq.1 N
    field_simp
    nlinarith [sq_nonneg (decay I ^ N)]
  have hh := pow_le_pow_left₀ hq.1.le (decay_exp_bound I) N
  rw [← exp_nat_mul] at hh
  have he : (N : ℝ) * (-(sqrt I.kappa)⁻¹) = -((N : ℝ) / sqrt I.kappa) := by ring
  rw [he] at hh
  linarith

theorem epsilon_cosh_bound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (c : ℝ)
    (hc : 0 ≤ c) (hN : c * sqrt I.kappa ≤ (N : ℝ)) : I.epsilon N ≤ (cosh c)⁻¹ := by
  have hs : 0 < sqrt I.kappa := lt_trans zero_lt_one (condition_sqrt_gt_one I)
  have hn : c ≤ (N : ℝ) / sqrt I.kappa := (le_div_iff₀ hs).mpr hN
  have ht : c ≤ (N : ℝ) * theta I := by
    have hh := mul_le_mul_of_nonneg_left (theta_condition_lower I) (Nat.cast_nonneg (α := ℝ) N)
    simpa only [div_eq_mul_inv] using hn.trans hh
  have hcos : cosh c ≤ cosh ((N : ℝ) * theta I) := cosh_le_cosh.mpr (by
    rw [abs_of_nonneg hc, abs_of_nonneg (hc.trans ht)]
    exact ht)
  rw [InexactRealizations.Operators.SpectralInterval.epsilon, I.den_cosh_arcosh]
  simpa only [one_div, theta] using inv_anti₀ (cosh_pos c) hcos

theorem one_sub_decay_square_bound (I : InexactRealizations.Operators.SpectralInterval) :
    1 - decay I ^ 2 ≤ 4 / sqrt I.kappa := by
  have hs := condition_sqrt_gt_one I
  rw [InexactRealizations.Accuracy.decay_eq_condition]
  field_simp
  nlinarith [sq_nonneg (sqrt I.kappa)]

theorem decay_lower_half (I : InexactRealizations.Operators.SpectralInterval) (hk : 9 ≤ I.kappa) : 1 / 2 ≤ decay I := by
  have hs : 3 ≤ sqrt I.kappa := by
    nlinarith [sqrt_nonneg I.kappa, sq_sqrt (by linarith : 0 ≤ I.kappa)]
  rw [InexactRealizations.Accuracy.decay_eq_condition]
  apply (le_div_iff₀ (by linarith : 0 < sqrt I.kappa + 1)).mpr
  linarith

end
end InexactRealizations.Averages
