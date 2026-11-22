import InexactRealizations.Accuracy.Estimates.Decay

/-! The oracle, query and recovery first-order channels contribute at
most a condition-number constant times epsilon*N^3 after summation. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced

set_option maxHeartbeats 2000000 in
theorem oracle_cubic_point (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) (s : Fin N) :
    oracleWeight I N hN s * I.L *
      (3 / InexactRealizations.Balanced.normalizer I N s.val + 6 * theta I N s.val * distanceCoefficient I N s.val) ≤
      48 * (I.kappa / (I.kappa - 1)) * I.epsilon N * (N : ℝ) ^ 2 / (InexactRealizations.Classical.decay I) ^ 2 := by
  let q := InexactRealizations.Classical.decay I
  let R := I.L * I.epsilon N / I.delta
  let d := distanceCoefficient I N s.val
  have hq := InexactRealizations.Classical.decay_mem I
  have hq2 : 0 < q ^ 2 := sq_pos_of_pos hq.1
  have hq21 : q ^ 2 ≤ 1 := by dsimp [q]; nlinarith [hq.1, hq.2]
  have hd := distanceCoefficient_nonneg I N s.val
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have he : 0 ≤ I.epsilon N := (one_div_pos.mpr (I.den_pos N)).le
  have hR : 0 ≤ R := div_nonneg (mul_nonneg hL he) I.delta_pos.le
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hfirst : 3 * I.L * (oracleWeight I N hN s / InexactRealizations.Balanced.normalizer I N s.val) ≤
      6 * R * ((N : ℝ) + 1) := by
    have hh := mul_le_mul_of_nonneg_left (oracleWeight_normalizer I hN s) (show 0 ≤ 3 * I.L by positivity)
    convert hh using 1
    dsimp [R]
    ring
  have hsecond1 : 6 * I.L * (oracleWeight I N hN s * theta I N s.val) * d ≤
      12 * R * ((N : ℝ) + 1) * (I.den s.val * d) := by
    have hh := mul_le_mul_of_nonneg_left (oracleWeight_theta I hN s) (show 0 ≤ 6 * I.L * d by positivity)
    convert hh using 1
    all_goals try dsimp only [R]
    all_goals ring
  have hsecond : 6 * I.L * (oracleWeight I N hN s * theta I N s.val) * d ≤
      6 * R * ((N : ℝ) + 1) * ((N : ℝ) + 3) / q ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (distanceCoefficient_weighted I N s.val)
      (show 0 ≤ 12 * R * ((N : ℝ) + 1) by positivity)
    have hh' : 12 * R * ((N : ℝ) + 1) * (I.den s.val * d) ≤
        6 * R * ((N : ℝ) + 1) * ((N : ℝ) + 3) / q ^ 2 := by
      convert hh using 1
      dsimp only [q]
      ring
    exact hsecond1.trans hh'
  have hfirst' : 3 * I.L * (oracleWeight I N hN s / InexactRealizations.Balanced.normalizer I N s.val) ≤
      6 * R * ((N : ℝ) + 1) / q ^ 2 := by
    apply hfirst.trans
    exact (le_div_iff₀ hq2).mpr
      (by nlinarith [mul_le_mul_of_nonneg_left hq21 (show 0 ≤ 6 * R * ((N : ℝ) + 1) by positivity)])
  have harith : 6 * ((N : ℝ) + 1) + 6 * ((N : ℝ) + 1) * ((N : ℝ) + 3) ≤ 48 * (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((N : ℝ) - 2)]
  have hsum := add_le_add hfirst' hsecond
  have hsum' : oracleWeight I N hN s * I.L *
      (3 / InexactRealizations.Balanced.normalizer I N s.val + 6 * theta I N s.val * d) ≤
      R / q ^ 2 * (6 * ((N : ℝ) + 1) + 6 * ((N : ℝ) + 1) * ((N : ℝ) + 3)) := by
    convert hsum using 1 <;> ring
  have hlast := mul_le_mul_of_nonneg_left harith (div_nonneg hR hq2.le)
  have hscale : I.L / I.delta = I.kappa / (I.kappa - 1) := condition_ratio I
  convert hsum'.trans hlast using 1
  dsimp only [R, q]
  rw [show I.L * I.epsilon N / I.delta = (I.L / I.delta) * I.epsilon N by ring, hscale]
  ring

end
end InexactRealizations.Accuracy.Execution
