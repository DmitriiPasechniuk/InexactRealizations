import InexactRealizations.Probability.InitialState
import InexactRealizations.Risk.Bounds

namespace InexactRealizations.History
noncomputable section
open MeasureTheory Filter Polynomial
open scoped BigOperators
variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {N : ℕ} {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E} [IsProbabilityMeasure μ]

theorem integral_randomInitial_stochasticOutput_le (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H)
    (V : Ω → E) (hV : StronglyMeasurable[𝓕 0] V) (hV₂ : MemLp V 2 μ)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ)
    (r σ C : ℝ) (hC : 0 ≤ C)
    (hp : ∀ x ∈ Set.Icc I.mu I.L, |h.terminal.eval x| ≤ C)
    (P : Fin N → ℝ) (hP : InexactRealizations.Risk.ResponseBounds h I P)
    (hr : (∫ ω, ‖V ω‖ ^ 2 ∂μ) ≤ r ^ 2)
    (hσ : ∀ s, s < N → μ[fun ω ↦ ‖w s ω‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ ↦ σ ^ 2) :
    (∫ ω, ‖h.stochasticOutput H (V ω) w ω‖ ^ 2 ∂μ) ≤ C ^ 2 * r ^ 2 + σ ^ 2 * ∑ s, P s ^ 2 := by
  let B : E →L[ℝ] E := (aeval H h.terminal).toContinuousLinearMap
  have hbi := (hV₂.continuousLinearMap_comp B).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hvi := hV₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hb : (∫ ω, ‖B (V ω)‖ ^ 2 ∂μ) ≤ C ^ 2 * r ^ 2 := by
    calc
      _ ≤ ∫ ω, C ^ 2 * ‖V ω‖ ^ 2 ∂μ := by
        apply integral_mono_ae hbi (hvi.const_mul _)
        filter_upwards with ω
        rw [← mul_pow]
        exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr
          (InexactRealizations.Analysis.polynomial_action_bound I H hH h.terminal C hC hp (V ω))
      _ = C ^ 2 * ∫ ω, ‖V ω‖ ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (sq_nonneg C)
  have hnorm (s : Fin N) : ‖h.responseOperator H s‖ ≤ P s :=
    InexactRealizations.Analysis.polynomial_operator_bound I H hH _ _ (hP.1 s) (hP.2 s)
  have hn : (∑ s : Fin N, ∫ ω, ‖h.responseOperator H s (w s.val ω)‖ ^ 2 ∂μ) ≤
      σ ^ 2 * ∑ s, P s ^ 2 := by
    calc
      _ ≤ ∑ s : Fin N, ‖h.responseOperator H s‖ ^ 2 * σ ^ 2 :=
        Finset.sum_le_sum (fun s _ ↦ hw.integral_response_energy_le _ σ hσ s.val s.isLt)
      _ ≤ ∑ s : Fin N, P s ^ 2 * σ ^ 2 := by
        apply Finset.sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) (hP.1 s)).mpr (hnorm s)) (sq_nonneg σ)
      _ = _ := by rw [← Finset.sum_mul]; ring
  rw [integral_randomInitial_stochasticOutput h H V hV hV₂ hw]
  exact add_le_add hb hn

end
end InexactRealizations.History
