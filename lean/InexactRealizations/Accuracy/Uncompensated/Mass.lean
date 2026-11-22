import InexactRealizations.Accuracy.Estimates.AverageWeights
import InexactRealizations.Comparisons.Classical.Exterior

/-! The geometric upper envelope of the stored parity mass, including
the distinct startup weight at s=0. 
-/
namespace InexactRealizations.Accuracy.Uncompensated
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced

theorem omega_drop_upper_all {N s : ℕ} (hN : 2 ≤ N) :
    InexactRealizations.Balanced.omega N s - InexactRealizations.Balanced.omega N (s + 2) ≤ 2 / ((N : ℝ) - 1) := by
  by_cases hs : s = 0
  · subst s
    have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have htwo : Even (2 : ℕ) := by decide
    rw [InexactRealizations.Balanced.omega_zero]
    simp only [Nat.zero_add, InexactRealizations.Balanced.omega,
      show ¬(2 : ℕ) < 2 by decide, ite_false, htwo, ite_true, Nat.cast_ofNat,
      Nat.mod_self, Nat.cast_zero, sub_zero]
    split_ifs
    · have he : 1 - ((N : ℝ) + 2 - 2) / N = 0 := by
        field_simp [(show (0 : ℝ) < N by linarith).ne']
        ring
      rw [he]
      exact div_nonneg (by norm_num) (by linarith)
    · have he : 1 - (((N : ℝ) + 1) * ((N : ℝ) + 1 - 2) / ((N : ℝ) ^ 2 + 1)) =
          2 / ((N : ℝ) ^ 2 + 1) := by
        field_simp [(show (0 : ℝ) < (N : ℝ) ^ 2 + 1 by positivity).ne']
        ring
      rw [he]
      apply (div_le_div_iff₀ (by positivity) (by linarith)).mpr
      nlinarith [sq_nonneg ((N : ℝ) - 1)]
  · exact (omega_drop_bounds hN (show 1 ≤ s by omega)).2

theorem scaled_den_forward (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hs : s ≤ N) :
    I.epsilon N * I.den s ≤ 2 * InexactRealizations.Classical.decay I ^ (N - s) := by
  have hh := InexactRealizations.Classical.scaled_den_le I N (N - s) (by omega)
  simpa only [Nat.sub_sub_self hs] using hh

set_option maxHeartbeats 1000000 in
theorem scaled_mass_upper (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (j : ℕ) (hj : j < N) :
    I.epsilon N * mass I N j ≤
      4 * InexactRealizations.Classical.decay I ^ (N + 2 - j) /
        (((N : ℝ) - 1) * (1 - InexactRealizations.Classical.decay I ^ 2)) := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : 0 < (N : ℝ) - 1 := by linarith
  have hq := InexactRealizations.Classical.decay_mem I
  have hq0 := hq.1.le
  have hgap : 0 < 1 - InexactRealizations.Classical.decay I ^ 2 := by nlinarith [hq.1, hq.2]
  have he : 0 ≤ I.epsilon N := (one_div_pos.mpr (I.den_pos N)).le
  induction j using Nat.twoStepInduction with
  | zero => simp only [mass_zero, mul_zero]; positivity
  | one => simp only [mass_one, mul_zero]; positivity
  | more j ih _ =>
    have hprev := ih (by omega : j < N)
    have hden := scaled_den_forward I (show j ≤ N by omega)
    have hd := omega_drop_upper_all (s := j) hN
    have hprod := mul_le_mul hd hden
      (mul_nonneg he (I.den_pos j).le) (by positivity : 0 ≤ 2 / ((N : ℝ) - 1))
    have hstep := add_le_add hprev hprod
    have hidx : N + 2 - j = (N - j) + 2 := by omega
    have hnext : N + 2 - (j + 2) = N - j := by omega
    have hid : 4 * InexactRealizations.Classical.decay I ^ (N + 2 - j) /
        (((N : ℝ) - 1) * (1 - InexactRealizations.Classical.decay I ^ 2)) +
        2 / ((N : ℝ) - 1) * (2 * InexactRealizations.Classical.decay I ^ (N - j)) =
        4 * InexactRealizations.Classical.decay I ^ (N + 2 - (j + 2)) /
          (((N : ℝ) - 1) * (1 - InexactRealizations.Classical.decay I ^ 2)) := by
      rw [hidx, hnext, pow_add]
      field_simp [(show (N : ℝ) - 1 ≠ 0 by linarith), hgap.ne']
      ring
    rw [mass_step, mul_add]
    rw [← hid]
    convert hstep using 1
    ring

end
end InexactRealizations.Accuracy.Uncompensated
