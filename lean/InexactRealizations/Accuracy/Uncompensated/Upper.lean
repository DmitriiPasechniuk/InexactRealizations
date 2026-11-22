import InexactRealizations.Accuracy.Uncompensated.Series
import InexactRealizations.Accuracy.UncompensatedWitness

/-! Analytic, all-horizon upper bound on the extra uncorrected-average
coefficient. No computed grid or asymptotic certificate is assumed. 
-/
namespace InexactRealizations.Accuracy.Uncompensated
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
open InexactRealizations.Accuracy.Execution
open scoped BigOperators

def upperPrefactor (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : ℝ :=
  4 * (N : ℝ) * I.L / (((N : ℝ) - 1) * (1 - InexactRealizations.Classical.decay I ^ 2) * I.delta)
def limitingUpper (I : InexactRealizations.Operators.SpectralInterval) : ℝ :=
  4 * I.L * InexactRealizations.Classical.decay I ^ 2 /
    ((1 - InexactRealizations.Classical.decay I ^ 2) * (1 - InexactRealizations.Classical.decay I) ^ 2 * I.delta)

set_option maxHeartbeats 1000000 in
theorem average_response_geometric (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s + 2 < N) :
    I.L * averageWeight I N s ≤ upperPrefactor I N * geometricTerm I (N - 1 - s) := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hq := InexactRealizations.Classical.decay_mem I
  have hgap : 0 < 1 - InexactRealizations.Classical.decay I ^ 2 := by nlinarith [hq.1, hq.2]
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hd := I.delta_pos
  have hbase := mul_le_mul_of_nonneg_left (averageWeight_bound I hN hs) hL
  have hmass := scaled_mass_upper I hN (s + 2) hs
  have hcoef : 0 ≤ (N : ℝ) * (N - 1 - s : ℕ) * I.L / I.delta := by positivity
  have hh := mul_le_mul_of_nonneg_left hmass hcoef
  have hmiddle : I.L * ((N : ℝ) * (N - 1 - s : ℕ) * mass I N (s + 2) / (I.delta * I.den N)) ≤
      upperPrefactor I N * geometricTerm I (N - 1 - s) := by
    convert hh using 1
    · unfold InexactRealizations.Operators.SpectralInterval.epsilon
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · have hexp : N + 2 - (s + 2) = (N - 1 - s) + 1 := by omega
      rw [hexp]
      unfold upperPrefactor geometricTerm
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  exact hbase.trans hmiddle

set_option maxHeartbeats 1000000 in
theorem averageFactor_upper_decay (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    I.L * UncompensatedWitness.averageFactor I N ≤ ((N : ℝ) / ((N : ℝ) - 1)) * limitingUpper I := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hq := InexactRealizations.Classical.decay_mem I
  have hgap : 0 < 1 - InexactRealizations.Classical.decay I ^ 2 := by nlinarith [hq.1, hq.2]
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hDelta := I.delta_pos.le
  have hn1 : 0 < (N : ℝ) - 1 := by linarith
  have hA : 0 ≤ upperPrefactor I N := by unfold upperPrefactor; positivity
  have hpoint (s : Fin (N - 2)) :
      I.L * (if 2 ≤ s.val then averageWeight I N s.val else 0) ≤
        upperPrefactor I N * geometricTerm I (N - 1 - s.val) := by
    split_ifs
    · exact average_response_geometric I hN (by have := s.isLt; omega)
    · simp only [mul_zero]
      exact mul_nonneg hA (geometricTerm_nonneg I _)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ ↦ hpoint s)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hh
  have hgeom := mul_le_mul_of_nonneg_left (reversed_geometric_sum_le I hN) hA
  have hactual : I.L * UncompensatedWitness.averageFactor I N ≤
      upperPrefactor I N * (∑ s : Fin (N - 2), geometricTerm I (N - 1 - s.val)) := hh
  convert hactual.trans hgeom using 1
  unfold upperPrefactor limitingUpper
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

set_option maxHeartbeats 1000000 in
theorem limitingUpper_condition (I : InexactRealizations.Operators.SpectralInterval) :
    limitingUpper I = (I.kappa - 1) * Real.sqrt I.kappa / 4 := by
  have hk := kappa_gt_one I
  have hs2 := Real.sq_sqrt (show 0 ≤ I.kappa by linarith)
  have hs0 := Real.sqrt_nonneg I.kappa
  have hs1 : 1 < Real.sqrt I.kappa := by nlinarith
  have he : limitingUpper I = 4 * (I.L / I.delta) * InexactRealizations.Classical.decay I ^ 2 /
      ((1 - InexactRealizations.Classical.decay I ^ 2) * (1 - InexactRealizations.Classical.decay I) ^ 2) := by
    unfold limitingUpper
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he, condition_ratio, decay_eq_condition]
  let t := Real.sqrt I.kappa
  have ht2 : t ^ 2 = I.kappa := hs2
  have ht1 : 1 < t := hs1
  change 4 * (I.kappa / (I.kappa - 1)) * ((t - 1) / (t + 1)) ^ 2 /
      ((1 - ((t - 1) / (t + 1)) ^ 2) * (1 - (t - 1) / (t + 1)) ^ 2) = (I.kappa - 1) * t / 4
  rw [← ht2]
  field_simp [(show t + 1 ≠ 0 by linarith), (show t ^ 2 - 1 ≠ 0 by nlinarith),
    (show t ≠ 0 by linarith)]
  linear_combination (4 - 8 * t ^ 2 + 4 * t ^ 4) *
    (mul_inv_cancel₀ (show t ≠ 0 by linarith))

theorem averageFactor_upper (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    I.L * UncompensatedWitness.averageFactor I N ≤
      (N : ℝ) * (I.kappa - 1) * Real.sqrt I.kappa / (4 * N - 4) := by
  have hh := averageFactor_upper_decay I hN
  rw [limitingUpper_condition] at hh
  convert hh using 1
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  field_simp [(show (N : ℝ) - 1 ≠ 0 by linarith)]

end
end InexactRealizations.Accuracy.Uncompensated
