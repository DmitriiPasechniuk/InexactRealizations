import InexactRealizations.Prose.RawMoments

/-! The literal random-initial MSE comparison class has only the stated
nonnegative mean-square budget. Its L2 property follows from that budget.
The fixed method has oracle access only; these definitions give it no
access to the random hidden minimizer. 
-/
namespace InexactRealizations.Prose
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
variable {N : ℕ}

inductive RawRandomMseValue (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r σ : ℝ) : ℝ → Prop where
  | model (E Ω : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (𝓕 : Filtration ℕ mΩ) (w : ℕ → Ω → E) (hw : RawAdditiveLaw N 𝓕 w μ σ)
      (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H)
      (V : Ω → E) (hV : StronglyMeasurable[𝓕 0] V)
      (hr : (∫⁻ ω, ENNReal.ofReal (‖V ω‖ ^ 2) ∂μ) ≤ ENNReal.ofReal (r ^ 2)) :
      RawRandomMseValue h I r σ (∫ ω, ‖h.stochasticOutput H (V ω) w ω‖ ^ 2 ∂μ)

theorem rawRandomMseValue_iff (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r σ v : ℝ) :
    RawRandomMseValue h I r σ v ↔ InexactRealizations.Risk.AllLinear.RandomMseValue h I r σ v := by
  constructor
  · intro hv
    cases hv with
    | model E Ω μ 𝓕 w hw H hH V hV hr =>
      have hV₂ := raw_second_moment_memLp ((hV.mono (𝓕.le 0)).aestronglyMeasurable) r hr
      have hi := hV₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
      have he := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ ↦ sq_nonneg _)
      rw [← he] at hr
      exact InexactRealizations.Risk.AllLinear.RandomMseValue.model E Ω μ 𝓕 w hw.martingale hw.bochner H hH V hV hV₂
        ((ENNReal.ofReal_le_ofReal_iff (sq_nonneg r)).mp hr)
  · intro hv
    cases hv with
    | model E Ω μ 𝓕 w hw hσ H hH V hV hV₂ hr =>
      apply RawRandomMseValue.model E Ω μ 𝓕 w (rawAdditiveLawOfMartingale hw hσ) H hH V hV
      rw [← ofReal_integral_eq_lintegral_ofReal
        (hV₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)) (Eventually.of_forall fun _ ↦ sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hr

theorem randomMseRisk_raw_supremum (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r σ : ℝ) (hr : 0 ≤ r) : InexactRealizations.Risk.AllLinear.randomMseRisk h I r σ =
      sSup {v | RawRandomMseValue h I r σ v} := by
  rw [InexactRealizations.Risk.AllLinear.randomMseRisk_eq_sSup h I r σ hr]
  congr 1
  ext v
  exact (rawRandomMseValue_iff h I r σ v).symm

end
end InexactRealizations.Prose
