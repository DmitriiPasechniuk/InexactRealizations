import InexactRealizations.Accuracy.Execution.Run
import InexactRealizations.Analysis.Spectral

/-! The exact error identity gives a dimension-uniform terminal norm
bound with the three printed response weights. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open Polynomial InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Roundoff
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def oracleWeight (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (s : Fin N) : ℝ :=
  |((InexactRealizations.Balanced.history I N hN).response s).eval I.mu|
def averageWeight (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ :=
  (averageResponse I N s).eval I.mu
def stateWeight (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ :=
  ((N : ℝ) - s) * I.den (s + 1) / I.den N

theorem oracleWeight_nonneg (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) (s : Fin N) :
    0 ≤ oracleWeight I N hN s := abs_nonneg _
theorem averageWeight_nonneg (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s + 2 < N) :
    0 ≤ averageWeight I N s := by
  rw [averageWeight, averageResponse_endpoint]
  exact mul_nonneg (averageScale_nonneg I hN hs) (Nat.cast_nonneg _)
theorem stateWeight_nonneg (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hs : s < N) :
    0 ≤ stateWeight I N s := by
  have hs' : (s : ℝ) < N := by exact_mod_cast hs
  unfold stateWeight
  exact div_nonneg (mul_nonneg (by linarith) (I.den_pos _).le) (I.den_pos _).le

theorem state_action_bound (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (s : Fin N) (z : E) :
    ‖(alpha I s.val)⁻¹ • (aeval H ((InexactRealizations.Classical.history I N).response s)) z‖ ≤
      stateWeight I N s.val * ‖z‖ := by
  have hp (lam : ℝ) (hlam : lam ∈ Set.Icc I.mu I.L) :
      |(C (alpha I s.val)⁻¹ * (InexactRealizations.Classical.history I N).response s).eval lam| ≤ stateWeight I N s.val := by
    simpa only [eval_mul, eval_C, stateWeight] using prefix_state_response_peak I N (by omega) s hlam
  have hh := InexactRealizations.Analysis.polynomial_action_bound I H hH
    (C (alpha I s.val)⁻¹ * (InexactRealizations.Classical.history I N).response s)
    (stateWeight I N s.val) (stateWeight_nonneg I s.isLt) hp z
  simpa only [map_mul, aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply] using hh

theorem Run.terminal_norm_bound {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ} {p : Prepared I N u}
    {H : E →ₗ[ℝ] E} {initial target : E} (v : Run p H initial target uO)
    (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H) :
    ‖v.x N - target‖ ≤ I.epsilon N * ‖initial - target‖ +
      (∑ s : Fin N, oracleWeight I N hN s * ‖hatNoise I N H v.localErrors s.val‖) +
      (∑ s : Fin (N - 2), averageWeight I N s.val * ‖averageNoise H v.localErrors s.val‖) +
      ∑ s : Fin N, stateWeight I N s.val * ‖v.localErrors.state (s.val + 1)‖ := by
  have hpeaks := journal_response_peaks I hN
  have hb (s : Fin N) := InexactRealizations.Analysis.polynomial_action_bound I H hH
    ((InexactRealizations.Balanced.history I N hN).response s) (oracleWeight I N hN s)
    (oracleWeight_nonneg I hN s) (hpeaks.1 s) (hatNoise I N H v.localErrors s.val)
  have hav (s : Fin (N - 2)) := InexactRealizations.Analysis.polynomial_action_bound I H hH
    (averageResponse I N s.val) (averageWeight I N s.val)
    (averageWeight_nonneg I hN (by have := s.isLt; omega)) (hpeaks.2.2.1 s)
    (averageNoise H v.localErrors s.val)
  have hid := exact_local_error_identity I hN H initial target v.localErrors v.execution
  change v.x N - target = _ at hid
  rw [hid]
  have hn := norm_sub_le
    ((aeval H (I.residual N)) (initial - target) +
      (∑ s : Fin N, (aeval H ((InexactRealizations.Balanced.history I N hN).response s)) (hatNoise I N H v.localErrors s.val)) +
      (∑ s : Fin (N - 2), (aeval H (averageResponse I N s.val)) (averageNoise H v.localErrors s.val)))
    (∑ s : Fin N, (alpha I s.val)⁻¹ •
      (aeval H ((InexactRealizations.Classical.history I N).response s)) (v.localErrors.state (s.val + 1)))
  have hfirst := InexactRealizations.Analysis.residual_action_bound I H hH N (initial - target)
  have hsumB := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun s _ ↦ hb s))
  have hsumA := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun s _ ↦ hav s))
  have hsumX := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum
    (fun s _ ↦ state_action_bound I hN H hH s (v.localErrors.state (s.val + 1))))
  have hab := norm_add_le ((aeval H (I.residual N)) (initial - target))
    (∑ s : Fin N, (aeval H ((InexactRealizations.Balanced.history I N hN).response s)) (hatNoise I N H v.localErrors s.val))
  have habc := norm_add_le
    ((aeval H (I.residual N)) (initial - target) +
      (∑ s : Fin N, (aeval H ((InexactRealizations.Balanced.history I N hN).response s)) (hatNoise I N H v.localErrors s.val)))
    (∑ s : Fin (N - 2), (aeval H (averageResponse I N s.val)) (averageNoise H v.localErrors s.val))
  linarith

end
end InexactRealizations.Accuracy.Execution
