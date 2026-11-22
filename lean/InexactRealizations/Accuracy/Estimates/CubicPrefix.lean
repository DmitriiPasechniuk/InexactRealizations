import InexactRealizations.Accuracy.Estimates.Decay

/-! A cubic-horizon bound for the initial-error part of Prefix rounding. -/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced

set_option maxHeartbeats 1000000 in
theorem prefix_scaled_coefficient (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) :
    (InexactRealizations.Classical.decay I) ^ 2 * I.den (s + 1) * prefixInitialCoefficient I s ≤
      11 + 8 * (I.kappa / (I.kappa - 1)) := by
  let Q := (InexactRealizations.Classical.decay I) ^ 2
  let a := Q * I.den (s + 1) / I.den s
  let b := Q * I.den (s + 1) / I.den (s - 1)
  have hq := InexactRealizations.Classical.decay_mem I
  have hQ : 0 ≤ Q := sq_nonneg _
  have hQ1 : Q ≤ 1 := by dsimp [Q]; nlinarith [hq.1, hq.2]
  have ha : a ≤ 1 := (div_le_one (I.den_pos s)).mpr (den_decay_one_squared I s)
  have hb : b ≤ 1 := (div_le_one (I.den_pos (s - 1))).mpr (den_decay_previous I s)
  have ha0 : 0 ≤ a := div_nonneg (mul_nonneg hQ (I.den_pos _).le) (I.den_pos _).le
  have hbeta := beta_bounds I s
  have hbeta0 := hbeta.1
  have halpha := (alpha_bounds I s).1.le
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hal : alpha I s * I.L ≤ 4 * (I.kappa / (I.kappa - 1)) := by
    have hh := mul_le_mul_of_nonneg_right (alpha_bounds I s).2.le hL
    rw [show (4 / I.delta) * I.L = 4 * (I.L / I.delta) by ring, condition_ratio] at hh
    exact hh
  have ht1 : (3 + 4 * beta I s) * a ≤ 7 := by
    nlinarith [mul_le_mul_of_nonneg_left ha (show 0 ≤ 3 + 4 * beta I s by positivity)]
  have ht2 : 3 * beta I s * b ≤ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 3 * beta I s by positivity)]
  have ht3 : 2 * alpha I s * I.L * a ≤ 8 * (I.kappa / (I.kappa - 1)) := by
    nlinarith [mul_le_mul_of_nonneg_left ha (show 0 ≤ 2 * alpha I s * I.L by positivity)]
  have hid : Q * I.den (s + 1) * prefixInitialCoefficient I s =
      (3 + 4 * beta I s) * a + 3 * beta I s * b + 2 * alpha I s * I.L * a + Q := by
    dsimp [a, b, prefixInitialCoefficient]
    field_simp [(I.den_pos (s + 1)).ne']
  change Q * I.den (s + 1) * prefixInitialCoefficient I s ≤ _
  rw [hid]
  linarith

set_option maxHeartbeats 1000000 in
theorem prefix_cubic_point (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) (s : Fin N) :
    stateWeight I N s.val * prefixInitialCoefficient I s.val ≤
      (11 + 8 * (I.kappa / (I.kappa - 1))) * I.epsilon N * (N : ℝ) ^ 2 /
        (InexactRealizations.Classical.decay I) ^ 2 := by
  let Q := (InexactRealizations.Classical.decay I) ^ 2
  let K := 11 + 8 * (I.kappa / (I.kappa - 1))
  have hQ : 0 < Q := sq_pos_of_pos (InexactRealizations.Classical.decay_mem I).1
  have hK : 0 ≤ K := by
    have hk := kappa_gt_one I
    dsimp [K]
    positivity
  have he : 0 ≤ I.epsilon N := (one_div_pos.mpr (I.den_pos N)).le
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs0 : (0 : ℝ) ≤ s.val := Nat.cast_nonneg _
  have hsN : (s.val : ℝ) < N := by exact_mod_cast s.isLt
  have hh := mul_le_mul_of_nonneg_left (prefix_scaled_coefficient I s.val)
    (show 0 ≤ ((N : ℝ) - s.val) * I.epsilon N by positivity)
  have hpoint : stateWeight I N s.val * prefixInitialCoefficient I s.val ≤
      ((N : ℝ) - s.val) * I.epsilon N * K / Q := by
    apply (le_div_iff₀ hQ).mpr
    convert hh using 1
    unfold stateWeight InexactRealizations.Operators.SpectralInterval.epsilon
    dsimp only [Q, K]
    ring
  have harith : (N : ℝ) - s.val ≤ (N : ℝ) ^ 2 := by nlinarith
  have hlast := mul_le_mul_of_nonneg_right harith (show 0 ≤ I.epsilon N * K / Q by positivity)
  have hlast' : ((N : ℝ) - s.val) * I.epsilon N * K / Q ≤
      (N : ℝ) ^ 2 * I.epsilon N * K / Q := by
    convert hlast using 1
    all_goals ring
  convert hpoint.trans hlast' using 1
  dsimp [Q, K]
  ring

end
end InexactRealizations.Accuracy.Execution
