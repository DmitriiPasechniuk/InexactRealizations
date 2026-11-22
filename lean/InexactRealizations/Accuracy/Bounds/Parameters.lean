import InexactRealizations.Accuracy.Estimates.Omega
import InexactRealizations.Accuracy.PrefixFactor

/-! Scalar bounds depending only on the horizon and condition number,
used by the uniform operation-perturbation estimates. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced

theorem kappa_gt_one (I : InexactRealizations.Operators.SpectralInterval) : 1 < I.kappa := by
  unfold InexactRealizations.Operators.SpectralInterval.kappa
  exact (lt_div_iff₀ I.mu_pos).mpr (by simpa only [one_mul] using I.mu_lt_L)

theorem condition_ratio (I : InexactRealizations.Operators.SpectralInterval) :
    I.L / I.delta = I.kappa / (I.kappa - 1) := by
  have hk := (sub_pos.mpr (kappa_gt_one I)).ne'
  unfold InexactRealizations.Operators.SpectralInterval.kappa InexactRealizations.Operators.SpectralInterval.delta at *
  field_simp [I.mu_pos.ne', (sub_pos.mpr I.mu_lt_L).ne', hk]

theorem omega_lower {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    1 / (N : ℝ) ≤ InexactRealizations.Balanced.omega N s := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases hsmall : s < 2
  · simp only [InexactRealizations.Balanced.omega, hsmall, ite_true]
    exact (div_le_one (by linarith : (0 : ℝ) < N)).mpr (by linarith)
  · have hidx : s - 2 + 2 = s := by omega
    have hh := (omega_next_bounds hN (show s - 2 + 2 < N by omega)).1
    rw [hidx] at hh
    have hsR : (s : ℝ) < N := by exact_mod_cast hs
    have hc : ((s - 2 : ℕ) : ℝ) = (s : ℝ) - 2 := Nat.cast_sub (by omega)
    apply le_trans _ hh
    rw [hc]
    apply (div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < N)).mpr
    linarith

theorem omega_le_theta (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    InexactRealizations.Balanced.omega N s ≤ theta I N s := by
  have hz := zeta_unit I hN hs
  have hw := (InexactRealizations.Balanced.omega_pos hN hs).le
  by_cases hsmall : s < 2
  · simp only [theta, InexactRealizations.Balanced.omega, hsmall, ite_true, le_refl]
  · rw [theta, ite_eq_right hsmall]
    apply (le_div_iff₀ hz.1).mpr
    nlinarith

theorem theta_inverse_bound (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    (theta I N s)⁻¹ ≤ N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ht := (theta_unit I hN hs).1
  have hb := (omega_lower hN hs).trans (omega_le_theta I hN hs)
  apply (inv_le_iff_one_le_mul₀ ht).mpr
  have hh := (div_le_iff₀ hn).mp hb
  simpa only [mul_comm] using hh

def parameterBound (kappa : ℝ) (N : ℕ) : ℝ := (N : ℝ) + 1 + 4 * (kappa / (kappa - 1))

theorem parameterBound_one (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    1 ≤ parameterBound I.kappa N := by
  have hk := kappa_gt_one I
  have hp : 0 ≤ I.kappa / (I.kappa - 1) := by positivity
  unfold parameterBound
  linarith [Nat.cast_nonneg (α := ℝ) N]

theorem alpha_scaled_bound (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    alpha I s * I.L ≤ parameterBound I.kappa N := by
  have ha := (alpha_bounds I s).2.le
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hh := mul_le_mul_of_nonneg_right ha hL
  have he : (4 / I.delta) * I.L = 4 * (I.kappa / (I.kappa - 1)) := by rw [← condition_ratio]; ring
  rw [he] at hh
  unfold parameterBound
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

theorem theta_parameter_bound (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    (theta I N s)⁻¹ ≤ parameterBound I.kappa N := by
  have hb := theta_inverse_bound I hN hs
  have hk := kappa_gt_one I
  have hp : 0 ≤ I.kappa / (I.kappa - 1) := by positivity
  unfold parameterBound
  linarith

end
end InexactRealizations.Accuracy
