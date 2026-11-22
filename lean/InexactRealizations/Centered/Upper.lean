import InexactRealizations.Centered.Moments
import InexactRealizations.Centered.Spectral

/-! A dimension-uniform finite-scale bound with the exact leading spectral
coefficient. The supremum over all adapted streams precedes the limit. 
-/
namespace InexactRealizations.Centered
noncomputable section
open Polynomial MeasureTheory Filter InexactRealizations.Analysis
open scoped BigOperators
variable {N : ℕ} {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}

def deviation (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E) (w : ℕ → Ω → E) (ω : Ω) : E :=
  h.stochasticOutput H initial w ω - (aeval H h.terminal) initial

theorem deviation_second (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ) :
    (∫ ω, ‖deviation h H initial w ω‖ ^ 2 ∂μ) =
      ∑ s : Fin N, ∫ ω, ‖h.responseOperator H s (w s.val ω)‖ ^ 2 ∂μ := by
  simp only [deviation, h.stochasticOutput_response, add_sub_cancel_left]
  have hh := hw.integral_norm_sq_finite_response (0 : E) (h.responseOperator H)
  simpa only [zero_add, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using hh

omit [IsProbabilityMeasure μ] [CompleteSpace E] in
theorem response_second_le (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ) (s : Fin N) :
    (∫ ω, ‖h.responseOperator H s (w s.val ω)‖ ^ 2 ∂μ) ≤
      responsePeak h I s ^ 2 * ∫ ω, ‖w s.val ω‖ ^ 2 ∂μ := by
  have hw2 := hw.squareIntegrable s.val s.isLt
  have hi := hw2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  calc
    _ ≤ ∫ ω, responsePeak h I s ^ 2 * ‖w s.val ω‖ ^ 2 ∂μ := by
      apply integral_mono_ae ((hw2.continuousLinearMap_comp (h.responseOperator H s)).integrable_norm_pow
        (by norm_num : (2 : ℕ) ≠ 0)) (hi.const_mul _)
      exact Eventually.of_forall (fun ω ↦ by
        have hb := polynomial_action_bound I H hH (h.response s) (responsePeak h I s)
          ((responsePeak_bounds h I).1 s) ((responsePeak_bounds h I).2 s) (w s.val ω)
        have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ((responsePeak_bounds h I).1 s) (norm_nonneg _))).mpr hb
        simpa only [InexactRealizations.History.responseOperator_apply, mul_pow] using hh)
    _ = _ := integral_const_mul _ _

def varianceRemainder (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (t0 : ℝ) : ℝ :=
  ∑ s, responsePeak h I s ^ 2 * deviationMajorant h I.L t0 s ^ 2

theorem finite_upper (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (initial : E)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ)
    (r t t0 : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) (htt0 : t ≤ t0) (hi : ‖initial‖ ≤ r)
    (hvar : RelativeVariance h H initial w 𝓕 μ t) :
    (∫ ω, ‖deviation h H initial w ω‖ ^ 2 ∂μ) ≤
      t ^ 2 * r ^ 2 * centeredCoefficient h I + t ^ 4 * r ^ 2 * varianceRemainder h I t0 := by
  rw [deviation_second h H initial hw]
  calc
    _ ≤ ∑ s : Fin N, responsePeak h I s ^ 2 *
        (t ^ 2 * ‖(aeval H (h.query s)) initial‖ ^ 2 + t ^ 4 * r ^ 2 * deviationMajorant h I.L t0 s ^ 2) := by
      apply Finset.sum_le_sum
      intro s _
      exact (response_second_le h I H hH hw s).trans (mul_le_mul_of_nonneg_left
        (noise_second_bound h I H hH initial hw r t t0 hr ht htt0 hi hvar s) (sq_nonneg _))
    _ = t ^ 2 * (∑ s : Fin N, responsePeak h I s ^ 2 * ‖(aeval H (h.query s)) initial‖ ^ 2) +
        t ^ 4 * r ^ 2 * varianceRemainder h I t0 := by
      rw [varianceRemainder, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ _ := by
      have hh := (weighted_query_energy_le h I H hH initial).trans
        (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg initial) hr).mpr hi)
          (centeredCoefficient_nonneg h I))
      have ht2 := mul_le_mul_of_nonneg_left hh (sq_nonneg t)
      nlinarith

end
end InexactRealizations.Centered
