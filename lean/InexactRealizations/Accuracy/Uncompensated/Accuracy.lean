import InexactRealizations.Accuracy.Uncompensated.Finite
import InexactRealizations.Accuracy.Execution.Componentwise
import InexactRealizations.Accuracy.Uncompensated.Upper

/-! Uniform uncompensated upper accuracy, retaining the exact additional
u*L*F_av target coefficient and the same permitted big-O dependencies. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
open scoped BigOperators

def uncompensatedQuadraticConstant (kappa : ℝ) (N : ℕ) : ℝ :=
  kappa * (queryEnvelope kappa N + queryRemainder kappa N + recoveryRemainder kappa N) +
  (kappa / (kappa - 1)) * (N : ℝ) ^ 3 * (gradientRemainder kappa N + uncompensatedRemainder kappa N) +
  (Real.sqrt kappa + 1) ^ 2 / 4 * prefixRemainder kappa N

set_option maxHeartbeats 1000000 in
theorem finiteUncompensatedInitialCoefficient_bound (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    finiteUncompensatedInitialCoefficient I N hN ≤ 2 * cubicConstant I.kappa * I.epsilon N * (N : ℝ) ^ 3 := by
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hO : 0 ≤ ∑ s : Fin N, oracleWeight I N hN s * I.L * hatInitialCoefficient I N s.val := by
    apply Finset.sum_nonneg
    intro s _
    have hz := (InexactRealizations.Balanced.normalizer_pos I hN s.isLt).le
    have ht := (theta_unit I hN s.isLt).1.le
    have hd := distanceCoefficient_nonneg I N s.val
    unfold hatInitialCoefficient
    exact mul_nonneg (mul_nonneg (oracleWeight_nonneg I hN s) hL) (by positivity)
  have hX : 0 ≤ ∑ s : Fin N, stateWeight I N s.val * prefixInitialCoefficient I s.val :=
    Finset.sum_nonneg (fun s _ ↦ mul_nonneg (stateWeight_nonneg I s.isLt) (prefixInitialCoefficient_nonneg I s.val))
  have hA : (∑ s : Fin (N - 2), averageWeight I N s.val * I.L * uncompensatedInitialCoefficient I N s.val) ≤
      2 * ∑ s : Fin (N - 2), averageWeight I N s.val * I.L * averageInitialCoefficient I N s.val := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    have hs : s.val + 2 < N := by have := s.isLt; omega
    have hw := mul_nonneg (averageWeight_nonneg I (s := s.val) hN hs) hL
    have hh : uncompensatedInitialCoefficient I N s.val ≤ 2 * averageInitialCoefficient I N s.val := by
      by_cases hsmall : s.val < 2
      · simp only [uncompensatedInitialCoefficient, averageInitialCoefficient, hsmall, ite_true, mul_zero, le_refl]
      · simp only [uncompensatedInitialCoefficient, averageInitialCoefficient, hsmall, ite_false]
        have hp := (phi_unit I hN (show 2 ≤ s.val by omega) hs).1.le
        have hd := distanceCoefficient_nonneg I N s.val
        simp only [div_eq_mul_inv]
        nlinarith [mul_nonneg hp hd]
    have hh' := mul_le_mul_of_nonneg_left hh hw
    convert hh' using 1
    ring
  have hcmp : finiteUncompensatedInitialCoefficient I N hN ≤ 2 * finiteInitialCoefficient I N hN := by
    unfold finiteUncompensatedInitialCoefficient finiteInitialCoefficient
    nlinarith
  have hh := mul_le_mul_of_nonneg_left (finiteInitialCoefficient_bound I hN) (show (0 : ℝ) ≤ 2 by norm_num)
  convert hcmp.trans hh using 1
  ring

theorem finiteUncompensatedQuadraticCoefficient_bound (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    finiteUncompensatedQuadraticCoefficient I N hN ≤ uncompensatedQuadraticConstant I.kappa N := by
  have hnonneg := remainders_nonneg I N
  have hCh : 0 ≤ queryEnvelope I.kappa N + queryRemainder I.kappa N + recoveryRemainder I.kappa N :=
    add_nonneg (add_nonneg (envelopes_nonneg I N).1 hnonneg.1) hnonneg.2.1
  have hCa : 0 ≤ gradientRemainder I.kappa N + uncompensatedRemainder I.kappa N :=
    add_nonneg hnonneg.2.2.2.1 hnonneg.2.2.2.2.2
  have hCx := hnonneg.2.2.2.2.1
  have hW : (∑ s : Fin N, oracleWeight I N hN s * I.L) ≤ I.kappa := by
    have hsum : (∑ s : Fin N, oracleWeight I N hN s) = InexactRealizations.Lower.additiveScale I N :=
      InexactRealizations.Roundoff.balanced_response_abs_sum I N hN
    rw [← Finset.sum_mul, hsum]
    nlinarith [additive_condition_bound I N]
  have ha := mul_le_mul_of_nonneg_right (average_coupling_sum I hN) hCa
  have hw := mul_le_mul_of_nonneg_right hW hCh
  have hx := mul_le_mul_of_nonneg_right (prefixFactor_condition_bound I N).le hCx
  unfold finiteUncompensatedQuadraticCoefficient uncompensatedQuadraticConstant
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem uncompensated_accuracy {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ} {p : Prepared I N u}
    {H : E →ₗ[ℝ] E} {initial target : E}
    (v : Run p H initial target uO) (hc : v.Uncompensated) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hH : InexactRealizations.Analysis.Admissible I H) :
    ‖v.x N - target‖ ≤
      I.epsilon N * (1 + 2 * cubicConstant I.kappa * (u + uO) * (N : ℝ) ^ 3) * ‖initial - target‖ +
      (2 * (u + uO) * I.L * InexactRealizations.Lower.additiveScale I N + 8 * u * prefixFactor I N +
        u * I.L * UncompensatedWitness.averageFactor I N) * ‖target‖ +
      (u + uO) ^ 2 * uncompensatedQuadraticConstant I.kappa N * (‖initial - target‖ + ‖target‖) := by
  have hh := v.finite_uncompensated_accuracy hc hN hu hu2 huO huO1 hH
  have hi := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (finiteUncompensatedInitialCoefficient_bound I hN) (add_nonneg hu huO))
    (norm_nonneg (initial - target))
  have hq := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (finiteUncompensatedQuadraticCoefficient_bound I hN) (sq_nonneg (u + uO)))
    (add_nonneg (norm_nonneg (initial - target)) (norm_nonneg target))
  have hb := hh.trans (add_le_add (add_le_add (add_le_add le_rfl hi) le_rfl) hq)
  convert hb using 1
  ring

end
end InexactRealizations.Accuracy.Execution
