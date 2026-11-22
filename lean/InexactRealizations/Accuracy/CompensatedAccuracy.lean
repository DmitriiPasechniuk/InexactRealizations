import InexactRealizations.Accuracy.Estimates.Cubic
import InexactRealizations.Accuracy.Estimates.Quadratic

/-! for the literal rounded execution. Both big-O
constants are explicit functions of exactly the parameters allowed in
the article. The bounds are uniform over dimensions and admissible
rounding choices on the fixed neighborhood 0<=u<=1/2,0<=uO<=1. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 1000000 in
theorem compensated_accuracy {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ} {p : Prepared I N u}
    {H : E →ₗ[ℝ] E} {initial target : E}
    (v : Run p H initial target uO) (hc : v.Compensated) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hH : InexactRealizations.Analysis.Admissible I H) :
    ‖v.x N - target‖ ≤
      I.epsilon N * (1 + cubicConstant I.kappa * (u + uO) * (N : ℝ) ^ 3) * ‖initial - target‖ +
      (2 * (u + uO) * I.L * InexactRealizations.Lower.additiveScale I N + 8 * u * prefixFactor I N) * ‖target‖ +
      (u + uO) ^ 2 * quadraticConstant I.kappa N * (‖initial - target‖ + ‖target‖) := by
  have hh := v.finite_accuracy hc hN hu hu2 huO huO1 hH
  have hdelta := add_nonneg hu huO
  have hi := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (finiteInitialCoefficient_bound I hN) hdelta) (norm_nonneg (initial - target))
  have hq := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (finiteQuadraticCoefficient_bound I hN) (sq_nonneg (u + uO)))
    (add_nonneg (norm_nonneg (initial - target)) (norm_nonneg target))
  have hb := hh.trans (add_le_add (add_le_add (add_le_add le_rfl hi) le_rfl) hq)
  convert hb using 1
  ring

end
end InexactRealizations.Accuracy.Execution
