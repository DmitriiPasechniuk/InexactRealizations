import InexactRealizations.Accuracy.Bounds.ReferenceFrame
import InexactRealizations.Accuracy.Operations.ReferenceState

/-! Explicit uniform local quadratic-remainder coefficients. They depend
only on the horizon and condition number; gradients carry an external L. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section

def queryRemainder (kappa : ℝ) (N : ℕ) : ℝ :=
  14 * variationEnvelope kappa N + 600 * stateEnvelope kappa N
def recoveryRemainder (kappa : ℝ) (N : ℕ) : ℝ :=
  9 * (answerEnvelope kappa N + variationEnvelope kappa N) + 2000000 * stateEnvelope kappa N
def averageRemainder (kappa : ℝ) (N : ℕ) : ℝ :=
  24 * variationEnvelope kappa N + 120800 * stateEnvelope kappa N
def gradientRemainder (kappa : ℝ) (N : ℕ) : ℝ :=
  7 * (recoveryEnvelope kappa N + variationEnvelope kappa N) +
    440000000 * parameterBound kappa N * stateEnvelope kappa N
def prefixRemainder (kappa : ℝ) (N : ℕ) : ℝ :=
  13 * variationEnvelope kappa N + 3 * parameterBound kappa N * recoveryEnvelope kappa N +
    200 * stateEnvelope kappa N + 2000000000 * parameterBound kappa N ^ 2 * stateEnvelope kappa N
def uncompensatedRemainder (kappa : ℝ) (N : ℕ) : ℝ :=
  14 * variationEnvelope kappa N + 44 * stateEnvelope kappa N

theorem envelopes_nonneg (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    0 ≤ queryEnvelope I.kappa N ∧ 0 ≤ answerEnvelope I.kappa N ∧ 0 ≤ recoveryEnvelope I.kappa N := by
  have hE : 0 ≤ stateEnvelope I.kappa N := le_trans zero_le_one (stateEnvelope_one I N)
  have hF := variationEnvelope_nonneg I N
  have hA : 0 ≤ parameterBound I.kappa N := le_trans zero_le_one (parameterBound_one I N)
  refine ⟨?_, ?_, ?_⟩
  · unfold queryEnvelope; positivity
  · unfold answerEnvelope; positivity
  · unfold recoveryEnvelope; positivity

theorem remainders_nonneg (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    0 ≤ queryRemainder I.kappa N ∧ 0 ≤ recoveryRemainder I.kappa N ∧
    0 ≤ averageRemainder I.kappa N ∧ 0 ≤ gradientRemainder I.kappa N ∧
    0 ≤ prefixRemainder I.kappa N ∧ 0 ≤ uncompensatedRemainder I.kappa N := by
  have hE : 0 ≤ stateEnvelope I.kappa N := le_trans zero_le_one (stateEnvelope_one I N)
  have hF := variationEnvelope_nonneg I N
  have hA : 0 ≤ parameterBound I.kappa N := le_trans zero_le_one (parameterBound_one I N)
  have hG := (envelopes_nonneg I N).2.1
  have hR := (envelopes_nonneg I N).2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold queryRemainder; positivity
  · unfold recoveryRemainder; positivity
  · unfold averageRemainder; positivity
  · unfold gradientRemainder; positivity
  · unfold prefixRemainder; positivity
  · unfold uncompensatedRemainder; positivity

end
end InexactRealizations.Accuracy.Execution
