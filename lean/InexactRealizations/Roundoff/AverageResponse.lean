import InexactRealizations.Roundoff.ResponsePeaks
import InexactRealizations.Roundoff.ErrorFilter
import InexactRealizations.Roundoff.ParityReindex

/-! The exact average-error channel, as a polynomial
operator identity on every real module. 
-/
namespace InexactRealizations.Roundoff
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def physicalU (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) : ℝ[X] :=
  (U ℝ k).comp (C I.eta - C (2 / I.delta) * X)

theorem physicalU_eval (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) (lam : ℝ) :
    (physicalU I k).eval lam = (U ℝ k).eval (I.z lam) := by
  have hc : I.eta - 2 / I.delta * lam = I.z lam := by
    unfold InexactRealizations.Operators.SpectralInterval.z InexactRealizations.Operators.SpectralInterval.eta
    ring
  simp only [physicalU, eval_comp, eval_sub, eval_C, eval_mul, eval_X, hc]

theorem prefix_response_deweight (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (s : Fin N) (hs : 0 < s.val) :
    C (-(I.den s.val)⁻¹) * (InexactRealizations.Classical.history I N).response s =
      C (4 * I.epsilon N / I.delta) * physicalU I (N - 1 - s.val) := by
  apply Polynomial.funext
  intro lam
  rw [eval_mul, eval_C, InexactRealizations.Classical.response_eval I N hN, eval_mul, eval_C, physicalU_eval]
  simp only [InexactRealizations.Classical.initialWeight, ne_of_gt hs, ite_false, one_mul]
  field_simp [I.den_ne s.val]

theorem prefix_response_deweight_action (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (s : Fin N) (hs : 0 < s.val) (H : E →ₗ[ℝ] E) (v : E) :
    -(I.den s.val)⁻¹ • (aeval H ((InexactRealizations.Classical.history I N).response s)) v =
      (4 * I.epsilon N / I.delta) • (aeval H (physicalU I (N - 1 - s.val))) v := by
  have hh := congrArg (fun p : ℝ[X] ↦ (aeval H p) v) (prefix_response_deweight I N hN s hs)
  simpa only [map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply] using hh

theorem averageScale_weight (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    averageScale I N s = (4 * I.epsilon N / I.delta) * averageWeight I N s := by
  unfold averageScale averageWeight InexactRealizations.Operators.SpectralInterval.epsilon
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem averageResponse_polynomial (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    averageResponse I N s =
      ∑ i : Fin ((N - 1 - s) / 2), C (averageScale I N s) * physicalU I (N - 1 - s - 2 * (i.val + 1)) := by
  apply Polynomial.funext
  intro lam
  rw [averageResponse_eval]
  simp only [eval_finsetSum, eval_mul, eval_C, physicalU_eval]
  rw [← Finset.mul_sum]
  congr 1
  simp only [averageChart, eval_finsetSum]
  exact (Fin.sum_univ_eq_sum_range
    (fun i ↦ (U ℝ ((N - 1 - s - 2 * (i + 1) : ℕ) : ℤ)).eval (I.z lam)) ((N - 1 - s) / 2)).symm

theorem averageResponse_action (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ)
    (H : E →ₗ[ℝ] E) (v : E) :
    (aeval H (averageResponse I N s)) v =
      ∑ i : Fin ((N - 1 - s) / 2), (4 * I.epsilon N / I.delta) •
        (averageWeight I N s • (aeval H (physicalU I (N - 1 - s - 2 * (i.val + 1)))) v) := by
  rw [averageResponse_polynomial, map_sum, LinearMap.sum_apply]
  simp only [map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, averageScale_weight, smul_smul]

theorem average_filter_response (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (iota : ℕ → E) :
    (∑ s : Fin N, (aeval H ((InexactRealizations.Classical.history I N).response s)) (recoveredError I N 0 iota s.val)) =
      ∑ s : Fin (N - 2), (aeval H (averageResponse I N s.val)) (iota s.val) := by
  calc
    _ = ∑ j : Fin N, ∑ i : Fin (j.val / 2), (4 * I.epsilon N / I.delta) •
        (averageWeight I N (j.val - 2 * (i.val + 1)) •
          (aeval H (physicalU I (N - 1 - j.val))) (iota (j.val - 2 * (i.val + 1)))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [recovered_iota_sum I hN j.isLt, map_smul, map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [prefix_response_deweight_action I N (by omega) j (by have := i.isLt; omega), map_smul]
    _ = ∑ s : Fin (N - 2), ∑ i : Fin ((N - 1 - s.val) / 2), (4 * I.epsilon N / I.delta) •
        (averageWeight I N s.val • (aeval H (physicalU I (N - 1 - (s.val + 2 * (i.val + 1))))) (iota s.val)) :=
      parity_triangle_sum N (fun s j ↦ (4 * I.epsilon N / I.delta) •
        (averageWeight I N s • (aeval H (physicalU I (N - 1 - j))) (iota s)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [averageResponse_action]
      apply Finset.sum_congr rfl
      intro i _
      have he : N - 1 - (s.val + 2 * (i.val + 1)) = N - 1 - s.val - 2 * (i.val + 1) := by omega
      rw [he]

end
end InexactRealizations.Roundoff
