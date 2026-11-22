import InexactRealizations.Accuracy.Estimates.Decay
import InexactRealizations.Accuracy.Estimates.AverageWeights

/-! The average channels retain the mass and degree cancellations;
their first-order sum therefore grows at most cubically in N. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced

set_option maxHeartbeats 2000000 in
theorem average_cubic_point (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs2 : 2 ≤ s) (hs : s + 2 < N) :
    averageWeight I N s * I.L *
      (9 * phi I N s * distanceCoefficient I N s + 1 / mass I N (s + 2)) ≤
      46 * (I.kappa / (I.kappa - 1)) * I.epsilon N * (N : ℝ) ^ 2 /
        (InexactRealizations.Classical.decay I) ^ 2 := by
  let Q := (InexactRealizations.Classical.decay I) ^ 2
  let R := I.L * I.epsilon N / I.delta
  let d := distanceCoefficient I N s
  let k : ℝ := (N - 1 - s : ℕ)
  have hq := InexactRealizations.Classical.decay_mem I
  have hQ : 0 < Q := sq_pos_of_pos hq.1
  have hQ1 : Q ≤ 1 := by dsimp [Q]; nlinarith [hq.1, hq.2]
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hkN : k ≤ N := by
    dsimp only [k]
    exact_mod_cast (show N - 1 - s ≤ N by omega)
  have hn1 : 0 < (N : ℝ) - 1 := by linarith
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hd := distanceCoefficient_nonneg I N s
  have he : 0 ≤ I.epsilon N := (one_div_pos.mpr (I.den_pos N)).le
  have hR : 0 ≤ R := div_nonneg (mul_nonneg hL he) I.delta_pos.le
  have hden := I.den_pos N
  have hDelta := I.delta_pos
  have hcoeff : 0 ≤ 2 * (N : ℝ) * k / (((N : ℝ) - 1) * I.delta * I.den N) := by positivity
  have hphiD : averageWeight I N s * phi I N s * d ≤
      (N : ℝ) * k * ((N : ℝ) + 3) / (((N : ℝ) - 1) * I.delta * I.den N * Q) := by
    have hh := mul_le_mul_of_nonneg_right (averageWeight_phi I hN hs2 hs) hd
    have hc := mul_le_mul_of_nonneg_left (distanceCoefficient_weighted I N s) hcoeff
    have hc' : (2 * (N : ℝ) * k * I.den s / (((N : ℝ) - 1) * I.delta * I.den N)) * d ≤
        (N : ℝ) * k * ((N : ℝ) + 3) / (((N : ℝ) - 1) * I.delta * I.den N * Q) := by
      convert hc using 1
      all_goals try dsimp only [Q]
      all_goals simp only [div_eq_mul_inv, mul_inv_rev]
      all_goals ring
    exact hh.trans hc'
  have hfirst : 9 * I.L * (averageWeight I N s * phi I N s * d) ≤ 45 * R * (N : ℝ) ^ 2 / Q := by
    have hh := mul_le_mul_of_nonneg_left hphiD (show 0 ≤ 9 * I.L by positivity)
    have hratio : ((N : ℝ) + 3) / ((N : ℝ) - 1) ≤ 5 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    have hscale : 0 ≤ 9 * R * (N : ℝ) * k / Q := by positivity
    have hratio' := mul_le_mul_of_nonneg_left hratio hscale
    have hratio'' : 9 * I.L * ((N : ℝ) * k * ((N : ℝ) + 3) /
        (((N : ℝ) - 1) * I.delta * I.den N * Q)) ≤ 45 * R * (N : ℝ) * k / Q := by
      convert hratio' using 1
      all_goals try dsimp only [R]
      all_goals try unfold InexactRealizations.Operators.SpectralInterval.epsilon
      all_goals simp only [div_eq_mul_inv, mul_inv_rev]
      all_goals ring
    have hk' := mul_le_mul_of_nonneg_left hkN (show 0 ≤ 45 * R * (N : ℝ) / Q by positivity)
    exact hh.trans (hratio''.trans (by convert hk' using 1 <;> ring))
  have hsecond : I.L * (averageWeight I N s / mass I N (s + 2)) ≤ R * (N : ℝ) ^ 2 / Q := by
    have hh := mul_le_mul_of_nonneg_left (averageWeight_over_mass I hN hs2 hs) hL
    have hk' := mul_le_mul_of_nonneg_left hkN (show 0 ≤ R * (N : ℝ) by positivity)
    have hbase : I.L * (averageWeight I N s / mass I N (s + 2)) ≤ R * (N : ℝ) ^ 2 := by
      apply hh.trans
      convert hk' using 1
      all_goals try dsimp only [R, k]
      all_goals try unfold InexactRealizations.Operators.SpectralInterval.epsilon
      all_goals ring
    exact hbase.trans ((le_div_iff₀ hQ).mpr (by
      nlinarith [mul_le_mul_of_nonneg_left hQ1 (show 0 ≤ R * (N : ℝ) ^ 2 by positivity)]))
  have hh := add_le_add hfirst hsecond
  have hscale := condition_ratio I
  convert hh using 1
  · dsimp only [d]; ring
  · dsimp only [R, Q]
    rw [show I.L * I.epsilon N / I.delta = (I.L / I.delta) * I.epsilon N by ring, hscale]
    ring

end
end InexactRealizations.Accuracy.Execution
