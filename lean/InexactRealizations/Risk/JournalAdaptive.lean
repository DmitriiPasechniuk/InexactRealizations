import InexactRealizations.Risk.AdaptiveUniform
import InexactRealizations.Risk.JournalAllLinear

/-! Current: the arbitrary-adaptive-method clause, together
with the already proved exact value for both linear comparison classes.
All randomness is modeled by actual probability measures and executions;
the estimator has no access to the hidden minimizer. 
-/
namespace InexactRealizations.Risk.AllLinear
noncomputable section
open MeasureTheory
variable {N : ℕ} {U : Type} [MeasurableSpace U]

theorem journal_arbitrary_adaptive_lower (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N)
    (r sigma : ℝ) (_hr : 0 ≤ r) (_hsigma : 0 ≤ sigma)
    (hdom : (sigma ^ 2 / (I.mu ^ 2 * N)) * (1 - I.epsilon N) > I.epsilon N * r ^ 2)
    (M : InexactRealizations.Risk.Adaptive.Family N U) (P : Measure U) [IsProbabilityMeasure P] :
    ENNReal.ofReal (allLinearValue I N r sigma) ≤ InexactRealizations.Risk.Adaptive.mseRisk M P I r sigma :=
  InexactRealizations.Risk.Adaptive.no_uniform_adaptive_improvement M P I (by omega) r sigma hdom

theorem journal_arbitrary_adaptive_lower_at (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N)
    (r sigma x0 : ℝ) (_hr : 0 ≤ r) (_hsigma : 0 ≤ sigma)
    (hdom : (sigma ^ 2 / (I.mu ^ 2 * N)) * (1 - I.epsilon N) > I.epsilon N * r ^ 2)
    (M : InexactRealizations.Probability.AdaptiveMethod N ℝ U) (P : Measure U) [IsProbabilityMeasure P] :
    ENNReal.ofReal (allLinearValue I N r sigma) ≤
      InexactRealizations.Risk.Adaptive.scalarMseRisk (M.recenter x0) P I r sigma :=
  InexactRealizations.Risk.Adaptive.no_adaptive_improvement (M.recenter x0) P I (by omega) r sigma hdom

end
end InexactRealizations.Risk.AllLinear
