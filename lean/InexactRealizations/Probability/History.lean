import InexactRealizations.Probability.FiniteResponse
import InexactRealizations.History.Execution
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace InexactRealizations.History
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {N : ℕ}

/-- The deterministic physical response of an actual oracle call, as a continuous operator.
Use: the martingale calculation is applied to `Phi_s(H)` from the actual history. 
-/
def responseOperator (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (s : Fin N) : E →L[ℝ] E :=
  (aeval H (h.response s)).toContinuousLinearMap

omit [CompleteSpace E] in
/-- The continuous physical response is exactly polynomial evaluation in the Hessian.
Use: transports the deterministic execution identity into probability theory. 
-/
@[simp] theorem responseOperator_apply (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (s : Fin N) (v : E) : h.responseOperator H s v = (aeval H (h.response s)) v := rfl

/-- The actual random output produced by the causal noisy oracle history.
Use: this is the terminal error whose expectation and MSE are bounded. 
-/
def stochasticOutput (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (w : ℕ → Ω → E) (ω : Ω) : E :=
  (h.run H initial (fun s => w s.val ω)).output

omit [CompleteSpace E] in
/-- Every sample of the actual terminal has the exact physical-response decomposition.
Use: introduces no probabilistic surrogate or additional oracle execution. 
-/
theorem stochasticOutput_response (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (w : ℕ → Ω → E) (ω : Ω) :
    h.stochasticOutput H initial w ω = (aeval H h.terminal) initial +
      ∑ s : Fin N, h.responseOperator H s (w s.val ω) := by
  exact h.physical_response H initial (fun s => w s.val ω)
    (h.run H initial (fun s => w s.val ω))

/-- Exact MSE of the actual history under martingale oracle assumptions.
Use: the stochastic part, before inserting the Flat response bound. 
-/
theorem integral_stochasticOutput_norm_sq (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (initial : E) {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ) [IsProbabilityMeasure μ] :
    (∫ ω, ‖h.stochasticOutput H initial w ω‖ ^ 2 ∂μ) =
      ‖(aeval H h.terminal) initial‖ ^ 2 +
        ∑ s : Fin N, ∫ ω, ‖h.responseOperator H s (w s.val ω)‖ ^ 2 ∂μ := by
  simp_rw [h.stochasticOutput_response H initial w]
  exact hw.integral_norm_sq_finite_response _ _

/-- The article's conditional variance budget bounds the actual terminal MSE.
Use: applicable to temporally dependent errors with deterministic history coefficients. 
-/
theorem integral_stochasticOutput_norm_sq_le (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (initial : E) {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ) [IsProbabilityMeasure μ]
    (σ : ℝ) (hσ : ∀ s, s < N →
      μ[fun ω => ‖w s ω‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ => σ ^ 2) :
    (∫ ω, ‖h.stochasticOutput H initial w ω‖ ^ 2 ∂μ) ≤
      ‖(aeval H h.terminal) initial‖ ^ 2 +
        σ ^ 2 * ∑ s : Fin N, ‖h.responseOperator H s‖ ^ 2 := by
  simp_rw [h.stochasticOutput_response H initial w]
  exact hw.integral_norm_sq_finite_response_le _ _ σ hσ

end
end InexactRealizations.History
