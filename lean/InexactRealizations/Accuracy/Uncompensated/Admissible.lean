import InexactRealizations.Accuracy.Uncompensated.Sharpness

/-! The witness's only rounded instruction is the final average addition.
Its actual real result is a BlendStep satisfying the individual operation
error model. The preceding subtraction and prepared product are exact. 
-/
namespace InexactRealizations.Accuracy.Uncompensated
noncomputable section
open Polynomial InexactRealizations.Algorithms.AveragedBalanced

def lastAdditionStep (N s : ℕ) (x b phi u : ℝ) (hu : 0 ≤ u) : BlendStep x b phi u where
  difference := x - b
  product := phi * (x - b)
  result := (1 - UncompensatedWitness.sign N s * u) * (b + phi * (x - b))
  difference_error := by simp only [sub_self, norm_zero]; positivity
  product_error := by simp only [smul_eq_mul, sub_self, norm_zero]; positivity
  result_error := by
    have hs : |UncompensatedWitness.sign N s| = 1 := by simp [UncompensatedWitness.sign, abs_pow]
    have he : (1 - UncompensatedWitness.sign N s * u) * (b + phi * (x - b)) -
        (b + phi * (x - b)) = -UncompensatedWitness.sign N s * u * (b + phi * (x - b)) := by ring
    simp only [Real.norm_eq_abs, he, abs_mul, abs_neg, hs, one_mul, abs_of_nonneg hu, le_refl]

theorem actual_average_instruction (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (rho : ℝ) {u : ℝ} (hu : 0 ≤ u) (hs2 : 2 ≤ s) (hsN : s + 2 < N) :
    let v := AverageExecution.states I N (UncompensatedWitness.hessian I.L) (C rho) (C rho)
      (UncompensatedWitness.rounding N) s
    (UncompensatedWitness.atScale I N rho u).average s =
      (lastAdditionStep N s (v.x.eval u) ((AverageExecution.oldAverage s v).eval u) (phi I N s) u hu).result := by
  let v := AverageExecution.states I N (UncompensatedWitness.hessian I.L) (C rho) (C rho)
    (UncompensatedWitness.rounding N) s
  change ((AverageExecution.states I N (UncompensatedWitness.hessian I.L) (C rho) (C rho)
    (UncompensatedWitness.rounding N) (s + 1)).recentAverage).eval u = _
  simp only [AverageExecution.states, AverageExecution.step, hsN, ite_true,
    show ¬s < 2 by omega, ite_false]
  rw [UncompensatedWitness.rounding_eval]
  simp only [lastAdditionStep, AverageExecution.idealAverage, eval_add, eval_smul, eval_sub, smul_eq_mul]

end
end InexactRealizations.Accuracy.Uncompensated
