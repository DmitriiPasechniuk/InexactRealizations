import InexactRealizations.Accuracy.Estimates.AverageWeights
import InexactRealizations.Accuracy.Bounds.Finite

/-! Uniform quadratic remainder constants depending only on N,kappa. -/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
open scoped BigOperators

def quadraticConstant (kappa : ℝ) (N : ℕ) : ℝ :=
  kappa * (queryEnvelope kappa N + queryRemainder kappa N + recoveryRemainder kappa N) +
  (kappa / (kappa - 1)) * (N : ℝ) ^ 3 * (gradientRemainder kappa N + averageRemainder kappa N) +
  (Real.sqrt kappa + 1) ^ 2 / 4 * prefixRemainder kappa N

set_option maxHeartbeats 1000000 in
theorem average_coupling_point (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s + 2 < N) :
    averageWeight I N s * I.L ≤ (I.kappa / (I.kappa - 1)) * (N : ℝ) ^ 2 := by
  let K := I.kappa / (I.kappa - 1)
  let k : ℝ := (N - 1 - s : ℕ)
  have hk := kappa_gt_one I
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hkN : k ≤ N := by dsimp only [k]; exact_mod_cast (show N - 1 - s ≤ N by omega)
  have hmN : mass I N (s + 2) ≤ I.den N := (mass_next_upper I hN hs).trans
    ((den_strictMono I).monotone (by omega))
  have hfrac : mass I N (s + 2) / I.den N ≤ 1 := (div_le_one (I.den_pos N)).mpr hmN
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hh := mul_le_mul_of_nonneg_right (averageWeight_bound I hN hs) hL
  have hfrac' := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ K * (N : ℝ) * k by positivity)
  have hfrac'' : (N : ℝ) * k * mass I N (s + 2) / (I.delta * I.den N) * I.L ≤ K * (N : ℝ) * k := by
    convert hfrac' using 1
    all_goals try dsimp only [K]
    all_goals try rw [← condition_ratio I]
    all_goals simp only [div_eq_mul_inv, mul_inv_rev]
    all_goals ring
  have hlast := mul_le_mul_of_nonneg_left hkN (show 0 ≤ K * (N : ℝ) by positivity)
  exact hh.trans (hfrac''.trans (by
    convert hlast using 1
    ring))

set_option maxHeartbeats 1000000 in
theorem average_coupling_sum (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    (∑ s : Fin (N - 2), averageWeight I N s.val * I.L) ≤
      (I.kappa / (I.kappa - 1)) * (N : ℝ) ^ 3 := by
  have hk := kappa_gt_one I
  have hK : 0 ≤ I.kappa / (I.kappa - 1) := by positivity
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun (s : Fin (N - 2)) _ ↦
    average_coupling_point I (s := s.val) hN (by have := s.isLt; omega))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  have hn : ((N - 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast (show N - 2 ≤ N by omega)
  have hn' := mul_le_mul_of_nonneg_right hn (show 0 ≤ (I.kappa / (I.kappa - 1)) * (N : ℝ) ^ 2 by positivity)
  exact hh.trans (by
    convert hn' using 1
    ring)

set_option maxHeartbeats 1000000 in
theorem finiteQuadraticCoefficient_bound (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    finiteQuadraticCoefficient I N hN ≤ quadraticConstant I.kappa N := by
  have hk := kappa_gt_one I
  have hnonneg := remainders_nonneg I N
  have hCh : 0 ≤ queryEnvelope I.kappa N + queryRemainder I.kappa N + recoveryRemainder I.kappa N :=
    add_nonneg (add_nonneg (envelopes_nonneg I N).1 hnonneg.1) hnonneg.2.1
  have hCa : 0 ≤ gradientRemainder I.kappa N + averageRemainder I.kappa N :=
    add_nonneg hnonneg.2.2.2.1 hnonneg.2.2.1
  have hCx := hnonneg.2.2.2.2.1
  have hW : (∑ s : Fin N, oracleWeight I N hN s * I.L) ≤ I.kappa := by
    have hsum : (∑ s : Fin N, oracleWeight I N hN s) = InexactRealizations.Lower.additiveScale I N :=
      InexactRealizations.Roundoff.balanced_response_abs_sum I N hN
    rw [← Finset.sum_mul, hsum]
    have hh := (additive_condition_bound I N).le
    nlinarith
  have ha := mul_le_mul_of_nonneg_right (average_coupling_sum I hN) hCa
  have hw := mul_le_mul_of_nonneg_right hW hCh
  have hx := mul_le_mul_of_nonneg_right (prefixFactor_condition_bound I N).le hCx
  unfold finiteQuadraticCoefficient quadraticConstant
  linarith

end
end InexactRealizations.Accuracy.Execution
