import InexactRealizations.Accuracy.AverageExecution
import InexactRealizations.Accuracy.AverageSign
import InexactRealizations.Accuracy.LocalExecutionMap
import InexactRealizations.Accuracy.PolynomialRemainder

/-! A literal finite-horizon uncompensated-rounding witness. The variable
X records the unit roundoff. Only the final average additions round, with
the alternating relative factors printed in the proof.
All other operations and prepared scalars have zero rounding errors. 
-/
namespace InexactRealizations.Accuracy.UncompensatedWitness
noncomputable section
open Polynomial
open scoped BigOperators
open InexactRealizations.Roundoff

def hessian (L : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] := L • LinearMap.id
def sign (N s : ℕ) : ℝ := (-1 : ℝ) ^ (N - 1 - s)
def rounding (N s : ℕ) (v : ℝ[X]) : ℝ[X] := -sign N s • (X * v)
def actual (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (rho : ℝ) :=
  AverageExecution.execution I N (hessian I.L) (C rho) (C rho) (rounding N)

theorem rounding_eval (N s : ℕ) (v : ℝ[X]) (u : ℝ) :
    (v + rounding N s v).eval u = (1 - sign N s * u) * v.eval u := by
  simp only [rounding, eval_add, eval_smul, eval_mul, eval_X, smul_eq_mul]
  ring

theorem scalar_action (L : ℝ) (p v : ℝ[X]) :
    (aeval (hessian L) p) v = p.eval L • v := by
  change (aeval (algebraMap ℝ (Module.End ℝ ℝ[X]) L) p) v = _
  rw [aeval_algebraMap_apply_eq_algebraMap_eval]
  rfl

theorem mapped_errors_zero (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (rho : ℝ) :
    (AverageExecution.localErrors I N (hessian I.L) (C rho) (C rho) (rounding N)).map
      (Polynomial.lcoeff ℝ 0) = zeroErrors ℝ := by
  have hh (s : ℕ) : (Polynomial.lcoeff ℝ 0)
      ((AverageExecution.localErrors I N (hessian I.L) (C rho) (C rho) (rounding N)).average s) = 0 := by
    change (if s < 2 then 0 else rounding N s _).coeff 0 = 0
    split_ifs <;> simp [rounding]
  unfold LocalErrorStreams.map zeroErrors
  congr 1
  exact funext hh

theorem actual_average_constant (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (rho : ℝ) (s : ℕ) (hs : s + 2 < N) : ((actual I N rho).average s).coeff 0 = rho := by
  let u := (actual I N rho).map (Polynomial.lcoeff ℝ 0) (I.L • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
    (by intro v; simp [hessian])
  have hh : (Polynomial.lcoeff ℝ 0) ((actual I N rho).average s) =
      (Polynomial.lcoeff ℝ 0) (C rho) := by
    exact u.zero_error_average_of_eq (mapped_errors_zero I N rho) hN s hs
  simpa only [Polynomial.lcoeff_apply, coeff_C_zero] using hh

theorem ideal_average_constant (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (rho : ℝ) (s : ℕ) (hs : s + 2 < N) :
    (AverageExecution.idealAverage I N s
      (AverageExecution.states I N (hessian I.L) (C rho) (C rho) (rounding N) s)).coeff 0 = rho := by
  have hh := actual_average_constant I hN rho s hs
  change ((AverageExecution.states I N (hessian I.L) (C rho) (C rho) (rounding N) (s + 1)).recentAverage).coeff 0 = rho at hh
  simp only [AverageExecution.states, AverageExecution.step, hs, ite_true, coeff_add] at hh
  have hz : (if s < 2 then 0 else rounding N s
      (AverageExecution.idealAverage I N s
        (AverageExecution.states I N (hessian I.L) (C rho) (C rho) (rounding N) s))).coeff 0 = 0 := by
    split_ifs <;> simp [rounding]
  simpa only [hz, add_zero] using hh

def averageFactor (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : ℝ :=
  ∑ s : Fin (N - 2), if 2 ≤ s.val then (averageResponse I N s.val).eval I.mu else 0

theorem actual_terminal_first_order (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (rho : ℝ) : ((actual I N rho).x N - C rho).coeff 1 = I.L * averageFactor I N * rho := by
  have hi := exact_local_error_identity I hN (hessian I.L) (C rho) (C rho)
    (AverageExecution.localErrors I N (hessian I.L) (C rho) (C rho) (rounding N)) (actual I N rho)
  have hw : hatNoise I N (hessian I.L)
      (AverageExecution.localErrors I N (hessian I.L) (C rho) (C rho) (rounding N)) = 0 := by
    funext s
    simp [hatNoise, combinedOracleError, AverageExecution.localErrors]
  rw [sub_self, map_zero, zero_add, hw] at hi
  simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero, zero_add,
    AverageExecution.localErrors, smul_zero, sub_zero] at hi
  have hh := congrArg (fun p : ℝ[X] ↦ p.coeff 1) hi
  simp only [finsetSum_coeff] at hh
  rw [hh, averageFactor, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  have hs : s.val + 2 < N := by have := s.isLt; omega
  rw [averageNoise, combinedAverageError, scalar_action]
  simp only [zero_sub]
  change ((averageResponse I N s.val).eval I.L • (-(I.L •
    (if s.val < 2 then 0 else rounding N s.val (AverageExecution.idealAverage I N s.val
      (AverageExecution.states I N (hessian I.L) (C rho) (C rho) (rounding N) s.val)))))).coeff 1 = _
  simp only [coeff_smul, coeff_neg, smul_eq_mul]
  by_cases hsmall : s.val < 2
  · simp only [hsmall, ite_true, coeff_zero, mul_zero, zero_mul, neg_zero,
      show ¬2 ≤ s.val by omega, ite_false]
  · simp only [hsmall, ite_false, rounding, coeff_smul, coeff_X_mul, smul_eq_mul,
      show 2 ≤ s.val by omega, ite_true]
    rw [ideal_average_constant I hN rho s.val hs, Accuracy.averageResponse_at_L]
    have hp : sign N s.val ^ 2 = 1 := by
      unfold sign
      rw [← pow_mul, Nat.mul_comm _ 2, pow_mul]
      norm_num
    change ((-1 : ℝ) ^ (N - 1 - s.val) * (averageResponse I N s.val).eval I.mu) *
      (-(I.L * (-sign N s.val * rho))) = _
    change sign N s.val ^ 2 = 1 at hp
    calc
      _ = sign N s.val ^ 2 * (I.L * (averageResponse I N s.val).eval I.mu * rho) := by
        unfold sign
        ring
      _ = _ := by rw [hp, one_mul]

theorem actual_terminal_constant (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (rho : ℝ) : ((actual I N rho).x N - C rho).coeff 0 = 0 := by
  let u := (actual I N rho).map (Polynomial.lcoeff ℝ 0) (I.L • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
    (by intro v; simp [hessian])
  have hh : (Polynomial.lcoeff ℝ 0) ((actual I N rho).x N) = (Polynomial.lcoeff ℝ 0) (C rho) :=
    u.zero_error_state_of_eq (mapped_errors_zero I N rho) hN N le_rfl
  simpa only [Polynomial.lcoeff_apply, coeff_sub, sub_eq_zero] using hh

theorem actual_terminal_expansion (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (rho : ℝ) : ∃ q : ℝ[X], ∀ u : ℝ,
      ((actual I N rho).x N - C rho).eval u =
        u * (I.L * averageFactor I N * rho) + u ^ 2 * q.eval u := by
  obtain ⟨q, hq⟩ := Accuracy.polynomial_quadratic_remainder ((actual I N rho).x N - C rho)
  refine ⟨q, fun u ↦ ?_⟩
  rw [hq, actual_terminal_constant I hN rho, actual_terminal_first_order I hN rho, zero_add]

def atScale (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (rho u : ℝ) :=
  (actual I N rho).map (Polynomial.aeval u).toLinearMap
    (I.L • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) (by intro v; simp [hessian])

theorem atScale_output_expansion (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (rho : ℝ) : ∃ q : ℝ[X], ∀ u : ℝ,
      (atScale I N rho u).x N - rho =
        u * (I.L * averageFactor I N * rho) + u ^ 2 * q.eval u := by
  obtain ⟨q, hq⟩ := actual_terminal_expansion I hN rho
  refine ⟨q, fun u ↦ ?_⟩
  change ((actual I N rho).x N).eval u - rho = _
  simpa only [eval_sub, eval_C] using hq u

theorem averageFactor_nonneg (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    0 ≤ averageFactor I N := by
  apply Finset.sum_nonneg
  intro s _
  split_ifs
  · rw [averageResponse_endpoint]
    exact mul_nonneg (averageScale_nonneg I hN (by have := s.isLt; omega)) (Nat.cast_nonneg _)
  · exact le_rfl

end
end InexactRealizations.Accuracy.UncompensatedWitness
