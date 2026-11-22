import InexactRealizations.Risk.AllLinearClass

/-! Literal supremum over actual physical probability models, including
an F0-measurable random initial error. The history coefficients and causal
oracle access are fixed before this random hidden problem is drawn. 
-/
namespace InexactRealizations.Risk.AllLinear
noncomputable section
open MeasureTheory Set
variable {N : ℕ}

inductive RandomMseValue (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r σ : ℝ) : ℝ → Prop where
  | model (E Ω : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (𝓕 : Filtration ℕ mΩ) (w : ℕ → Ω → E)
      (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ)
      (hσ : ∀ s, s < N → μ[fun ξ ↦ ‖w s ξ‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ ↦ σ ^ 2)
      (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H)
      (V : Ω → E) (hV : StronglyMeasurable[𝓕 0] V) (hV₂ : MemLp V 2 μ)
      (hr : (∫ ξ, ‖V ξ‖ ^ 2 ∂μ) ≤ r ^ 2) :
      RandomMseValue h I r σ (∫ ξ, ‖h.stochasticOutput H (V ξ) w ξ‖ ^ 2 ∂μ)

def randomMseValues (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r σ : ℝ) : Set ℝ :=
  {v | RandomMseValue h I r σ v}

theorem mseValue_is_randomMseValue (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    {r σ v : ℝ} (hr : 0 ≤ r) (hv : InexactRealizations.Risk.MseValue h I r σ v) : RandomMseValue h I r σ v := by
  cases hv with
  | model E Ω μ 𝓕 w hw hσ H hH initial hi =>
    apply RandomMseValue.model E Ω μ 𝓕 w hw hσ H hH (fun _ ↦ initial)
      stronglyMeasurable_const (memLp_const initial)
    have hh := (sq_le_sq₀ (norm_nonneg initial) hr).mpr hi
    simpa only [integral_const, probReal_univ, one_smul] using hh

theorem randomMseValues_upperBounds (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r σ : ℝ) : upperBounds (randomMseValues h I r σ) = {C | RandomMseBound h I r σ C} := by
  ext C
  constructor
  · intro hb E Ω _ _ _ _ _ μ _ 𝓕 w hw hσ H hH V hV hV₂ hr
    exact hb (RandomMseValue.model E Ω μ 𝓕 w hw hσ H hH V hV hV₂ hr)
  · intro hb v hv
    cases hv with
    | model E Ω μ 𝓕 w hw hσ H hH V hV hV₂ hr => exact hb E Ω μ 𝓕 w hw hσ H hH V hV hV₂ hr

theorem randomMseRisk_eq_sSup (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r σ : ℝ) (hr : 0 ≤ r) : randomMseRisk h I r σ = sSup (randomMseValues h I r σ) := by
  have hne : (randomMseValues h I r σ).Nonempty :=
    ⟨0, mseValue_is_randomMseValue h I hr (InexactRealizations.Risk.zero_mem_mseValues h I r σ hr)⟩
  obtain ⟨C, hC⟩ := randomMseBounds_nonempty h I r σ
  have hbd : BddAbove (randomMseValues h I r σ) := by
    refine ⟨C, ?_⟩
    rw [randomMseValues_upperBounds]
    exact hC
  unfold randomMseRisk
  rw [← randomMseValues_upperBounds]
  exact csInf_upperBounds_eq_csSup hbd hne

end
end InexactRealizations.Risk.AllLinear
