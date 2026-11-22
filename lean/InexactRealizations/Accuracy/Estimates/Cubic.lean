import InexactRealizations.Accuracy.Bounds.Finite
import InexactRealizations.Accuracy.Estimates.CubicOracle
import InexactRealizations.Accuracy.Estimates.CubicAverage
import InexactRealizations.Accuracy.Estimates.CubicPrefix

/-! The O_kappa(delta*N^3) coefficient in the article, with an explicit
constant independent of N, dimension and the spectral scale. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open scoped BigOperators

def cubicConstant (kappa : ℝ) : ℝ :=
  1000 * (1 + kappa / (kappa - 1)) /
    ((Real.sqrt kappa - 1) / (Real.sqrt kappa + 1)) ^ 2

set_option maxHeartbeats 2000000 in
theorem finiteInitialCoefficient_bound (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    finiteInitialCoefficient I N hN ≤ cubicConstant I.kappa * I.epsilon N * (N : ℝ) ^ 3 := by
  let K := I.kappa / (I.kappa - 1)
  let Q := (InexactRealizations.Classical.decay I) ^ 2
  let F := I.epsilon N * (N : ℝ) ^ 2 / Q
  have hk := kappa_gt_one I
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hQ : 0 < Q := sq_pos_of_pos (InexactRealizations.Classical.decay_mem I).1
  have he : 0 ≤ I.epsilon N := (one_div_pos.mpr (I.den_pos N)).le
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hO (s : Fin N) : oracleWeight I N hN s * I.L * hatInitialCoefficient I N s.val ≤ 48 * K * F := by
    convert oracle_cubic_point I hN s using 1
    all_goals try dsimp [K, F, Q, hatInitialCoefficient]
    all_goals ring
  have hA (s : Fin (N - 2)) : averageWeight I N s.val * I.L * averageInitialCoefficient I N s.val ≤ 46 * K * F := by
    have hs : s.val + 2 < N := by have := s.isLt; omega
    by_cases hsmall : s.val < 2
    · simp only [averageInitialCoefficient, hsmall, ite_true, mul_zero]
      positivity
    · simp only [averageInitialCoefficient, hsmall, ite_false]
      convert average_cubic_point I hN (show 2 ≤ s.val by omega) hs using 1
      all_goals try dsimp [K, F, Q]
      all_goals ring
  have hX (s : Fin N) : stateWeight I N s.val * prefixInitialCoefficient I s.val ≤ (11 + 8 * K) * F := by
    convert prefix_cubic_point I hN s using 1
    all_goals try dsimp [K, F, Q]
    all_goals ring
  have hsO := Finset.sum_le_sum (s := Finset.univ) (fun s _ ↦ hO s)
  have hsA := Finset.sum_le_sum (s := Finset.univ) (fun s _ ↦ hA s)
  have hsX := Finset.sum_le_sum (s := Finset.univ) (fun s _ ↦ hX s)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsO hsA hsX
  have hn : ((N - 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast (show N - 2 ≤ N by omega)
  have hsA' : (∑ s : Fin (N - 2), averageWeight I N s.val * I.L * averageInitialCoefficient I N s.val) ≤
      (N : ℝ) * (46 * K * F) := hsA.trans (mul_le_mul_of_nonneg_right hn (by positivity))
  have hsum : finiteInitialCoefficient I N hN ≤ (N : ℝ) * F * (102 * K + 11) := by
    unfold finiteInitialCoefficient
    nlinarith
  have harith : 102 * K + 11 ≤ 1000 * (1 + K) := by linarith
  have hlast := mul_le_mul_of_nonneg_left harith (show 0 ≤ (N : ℝ) * F by positivity)
  convert hsum.trans hlast using 1
  unfold cubicConstant
  rw [← decay_eq_condition I]
  dsimp [F, Q, K]
  ring

end
end InexactRealizations.Accuracy.Execution
