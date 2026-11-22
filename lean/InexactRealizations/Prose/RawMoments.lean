import InexactRealizations.Centered.RawModel
import InexactRealizations.Risk.RandomSupremum

/-! The raw conditional moment bounds stated in the article imply L2.
Neither the additive risk nor the random-initial comparison class gains
an extra integrability assumption. F0-measurability here specifies the
probability model; the fixed history receives no random minimizer input. 
-/
namespace InexactRealizations.Prose
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ENNReal
variable {N : ℕ} {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E} {σ : ℝ}

structure RawAdditiveLaw (N : ℕ) (𝓕 : Filtration ℕ mΩ) (w : ℕ → Ω → E)
    (μ : Measure Ω) (σ : ℝ) : Prop where
  adapted : ∀ s, s < N → StronglyMeasurable[𝓕 (s + 1)] (w s)
  centered : ∀ s, s < N → μ[w s | 𝓕 s] =ᵐ[μ] 0
  variance : ∀ s, s < N → μ⁻[fun ω ↦ ENNReal.ofReal (‖w s ω‖ ^ 2) | 𝓕 s] ≤ᵐ[μ]
    fun _ ↦ ENNReal.ofReal (σ ^ 2)

omit [IsProbabilityMeasure μ] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem raw_second_moment_memLp {V : Ω → E} (hV : AEStronglyMeasurable V μ) (r : ℝ)
    (hr : (∫⁻ ω, ENNReal.ofReal (‖V ω‖ ^ 2) ∂μ) ≤ ENNReal.ofReal (r ^ 2)) : MemLp V 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hV).mpr
  exact ⟨hV.norm.pow 2, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ ↦ sq_nonneg _)).mpr
    (hr.trans_lt ENNReal.ofReal_lt_top)⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem RawAdditiveLaw.squareIntegrable (hw : RawAdditiveLaw N 𝓕 w μ σ) (s : ℕ) (hs : s < N) :
    MemLp (w s) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm ((hw.adapted s hs).mono (𝓕.le (s + 1))).aestronglyMeasurable).mpr
  refine ⟨((hw.adapted s hs).mono (𝓕.le (s + 1))).aestronglyMeasurable.norm.pow 2, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ ↦ sq_nonneg _)).mpr
  rw [← lintegral_condLExp (𝓕.le s) μ]
  exact (lintegral_mono_ae (hw.variance s hs)).trans_lt (by simp)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem RawAdditiveLaw.bochner (hw : RawAdditiveLaw N 𝓕 w μ σ) (s : ℕ) (hs : s < N) :
    μ[fun ω ↦ ‖w s ω‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ ↦ σ ^ 2 := by
  have hc := condLExp_ofReal (𝓕 s) ((hw.squareIntegrable s hs).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    (Eventually.of_forall fun _ ↦ sq_nonneg _)
  filter_upwards [hc, hw.variance s hs] with ω he hv
  rw [he] at hv
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg σ)).mp hv

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem RawAdditiveLaw.martingale (hw : RawAdditiveLaw N 𝓕 w μ σ) :
    InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ where
  adapted := hw.adapted
  centered := hw.centered
  squareIntegrable := hw.squareIntegrable

omit [IsProbabilityMeasure μ] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem rawAdditiveLawOfMartingale (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ)
    (hv : ∀ s, s < N → μ[fun ω ↦ ‖w s ω‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ ↦ σ ^ 2) :
    RawAdditiveLaw N 𝓕 w μ σ where
  adapted := hw.adapted
  centered := hw.centered
  variance s hs := by
    have hc := condLExp_ofReal (𝓕 s) ((hw.squareIntegrable s hs).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
      (Eventually.of_forall fun _ ↦ sq_nonneg _)
    filter_upwards [hc, hv s hs] with ω he hv
    exact he.trans_le (ENNReal.ofReal_le_ofReal hv)

inductive RawMseValue (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r σ : ℝ) : ℝ → Prop where
  | model (E Ω : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (𝓕 : Filtration ℕ mΩ) (w : ℕ → Ω → E) (hw : RawAdditiveLaw N 𝓕 w μ σ)
      (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (initial : E) (hi : ‖initial‖ ≤ r) :
      RawMseValue h I r σ (∫ ω, ‖h.stochasticOutput H initial w ω‖ ^ 2 ∂μ)

theorem rawMseValue_iff (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r σ v : ℝ) :
    RawMseValue h I r σ v ↔ InexactRealizations.Risk.MseValue h I r σ v := by
  constructor
  · intro hv
    cases hv with
    | model E Ω μ 𝓕 w hw H hH initial hi =>
      exact InexactRealizations.Risk.MseValue.model E Ω μ 𝓕 w hw.martingale hw.bochner H hH initial hi
  · intro hv
    cases hv with
    | model E Ω μ 𝓕 w hw hσ H hH initial hi =>
      exact RawMseValue.model E Ω μ 𝓕 w (rawAdditiveLawOfMartingale hw hσ) H hH initial hi

theorem mseRisk_raw_supremum (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (r σ : ℝ) (hr : 0 ≤ r) :
    InexactRealizations.Risk.mseRisk h I r σ = sSup {v | RawMseValue h I r σ v} := by
  rw [InexactRealizations.Risk.mseRisk_eq_sSup h I he r σ hr]
  congr 1
  ext v
  exact (rawMseValue_iff h I r σ v).symm

end
end InexactRealizations.Prose
