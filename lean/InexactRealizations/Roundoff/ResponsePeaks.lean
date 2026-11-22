import InexactRealizations.Roundoff.ParitySum
import InexactRealizations.Algorithms.AveragedBalancedBounds
import InexactRealizations.Balanced.Bounds
import InexactRealizations.Comparisons.Classical.Bounds

/-! The explicit spectral response peaks printed in current. -/
namespace InexactRealizations.Roundoff
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators
open InexactRealizations.Algorithms.AveragedBalanced

def averageChart (k : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (k / 2), U ℝ ((k - 2 * (i + 1) : ℕ) : ℤ)

theorem averageChart_endpoint (k : ℕ) : (averageChart k).eval 1 = ((k ^ 2 / 4 : ℕ) : ℝ) := by
  simp only [averageChart, eval_finsetSum, U_eval_one, Int.cast_natCast]
  exact parity_endpoint_sum_real k

theorem averageChart_bound (k : ℕ) {z : ℝ} (hz : |z| ≤ 1) :
    |(averageChart k).eval z| ≤ ((k ^ 2 / 4 : ℕ) : ℝ) := by
  simp only [averageChart, eval_finsetSum]
  calc
    _ ≤ ∑ i ∈ Finset.range (k / 2), |(U ℝ ((k - 2 * (i + 1) : ℕ) : ℤ)).eval z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k / 2), (((k - 2 * (i + 1) : ℕ) : ℝ) + 1) :=
      Finset.sum_le_sum fun i _ ↦ InexactRealizations.Operators.abs_U_eval_le _ hz
    _ = _ := parity_endpoint_sum_real k

def averageScale (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ :=
  4 * mass I N (s + 2) / (I.delta * InexactRealizations.Balanced.omega N (s + 2) * I.den N)

def averageResponse (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ[X] :=
  C (averageScale I N s) * (averageChart (N - 1 - s)).comp (C I.eta - C (2 / I.delta) * X)

theorem averageScale_nonneg (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s + 2 < N) : 0 ≤ averageScale I N s :=
  div_nonneg (mul_nonneg (by norm_num) (mass_nonneg I hN hs))
    (mul_pos (mul_pos I.delta_pos (InexactRealizations.Balanced.omega_pos hN hs)) (I.den_pos N)).le

theorem averageResponse_eval (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (lam : ℝ) :
    (averageResponse I N s).eval lam = averageScale I N s * (averageChart (N - 1 - s)).eval (I.z lam) := by
  have hc : I.eta - 2 / I.delta * lam = I.z lam := by
    unfold InexactRealizations.Operators.SpectralInterval.z InexactRealizations.Operators.SpectralInterval.eta
    ring
  simp only [averageResponse, eval_mul, eval_C, eval_comp, eval_sub, eval_X, hc]

theorem averageResponse_endpoint (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    (averageResponse I N s).eval I.mu =
      averageScale I N s * (((N - 1 - s) ^ 2 / 4 : ℕ) : ℝ) := by
  rw [averageResponse_eval, I.z_mu, averageChart_endpoint]

theorem averageResponse_peak (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s + 2 < N) {lam : ℝ} (hlam : lam ∈ Set.Icc I.mu I.L) :
    |(averageResponse I N s).eval lam| ≤ (averageResponse I N s).eval I.mu := by
  rw [averageResponse_eval, abs_mul, abs_of_nonneg (averageScale_nonneg I hN hs), averageResponse_endpoint]
  exact mul_le_mul_of_nonneg_left (averageChart_bound _ (abs_le.mpr (I.z_mem hlam)))
    (averageScale_nonneg I hN hs)

theorem prefix_state_scale (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (s : Fin N) :
    (alpha I s.val)⁻¹ * InexactRealizations.Classical.responseBound I N s.val =
      ((N : ℝ) - s.val) * I.den (s.val + 1) / I.den N := by
  rcases s with ⟨s, hs⟩
  cases s with
  | zero =>
    simp only [alpha, InexactRealizations.Classical.responseBound, InexactRealizations.Classical.initialWeight,
      ite_true, I.den_zero, I.den_one, Nat.cast_zero, sub_zero]
    unfold InexactRealizations.Operators.SpectralInterval.epsilon InexactRealizations.Operators.SpectralInterval.eta
    field_simp [I.sum_pos.ne', I.delta_pos.ne', I.den_ne N]
    ring
  | succ s =>
    simp only [alpha, ratio_eq, InexactRealizations.Classical.responseBound, InexactRealizations.Classical.initialWeight,
      Nat.succ_ne_zero, ite_false]
    unfold InexactRealizations.Operators.SpectralInterval.epsilon
    field_simp [I.delta_pos.ne', I.den_ne N, I.den_ne (s + 1), I.den_ne (s + 2)]

theorem prefix_state_response_endpoint (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (s : Fin N) :
    |(alpha I s.val)⁻¹ * ((InexactRealizations.Classical.history I N).response s).eval I.mu| =
      ((N : ℝ) - s.val) * I.den (s.val + 1) / I.den N := by
  rw [InexactRealizations.Classical.response_endpoint I N hN, abs_mul, abs_inv,
    abs_of_pos (alpha_bounds I s.val).1, abs_neg,
    abs_of_pos (InexactRealizations.Classical.responseBound_pos I s), prefix_state_scale]

theorem prefix_state_response_peak (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (s : Fin N) {lam : ℝ} (hlam : lam ∈ Set.Icc I.mu I.L) :
    |(alpha I s.val)⁻¹ * ((InexactRealizations.Classical.history I N).response s).eval lam| ≤
      ((N : ℝ) - s.val) * I.den (s.val + 1) / I.den N := by
  rw [abs_mul, abs_inv, abs_of_pos (alpha_bounds I s.val).1, ← prefix_state_scale I N s]
  exact mul_le_mul_of_nonneg_left (InexactRealizations.Classical.response_bound I N hN s hlam)
    (inv_nonneg.mpr (alpha_bounds I s.val).1.le)

theorem balanced_response_abs_sum (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (∑ s, |((InexactRealizations.Balanced.history I N hN).response s).eval I.mu|) = InexactRealizations.Lower.additiveScale I N := by
  have hsign (s : Fin N) : ((InexactRealizations.Balanced.history I N hN).response s).eval I.mu < 0 := by
    rw [InexactRealizations.Balanced.response_endpoint]
    exact neg_neg_of_pos (InexactRealizations.Balanced.responseBound_pos I hN s.isLt)
  simp_rw [abs_of_neg (hsign _)]
  rw [Finset.sum_neg_distrib, InexactRealizations.Lower.response_sum_mu _ I (InexactRealizations.Balanced.history_exact I N hN), neg_neg]

end
end InexactRealizations.Roundoff
