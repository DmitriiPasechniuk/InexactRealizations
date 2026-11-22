import InexactRealizations.Risk.Minimax

namespace InexactRealizations.Risk
noncomputable section
open MeasureTheory
open scoped BigOperators
variable {N : ℕ}

/-- An actually achieved martingale MSE in the full probability comparison class.
Use: includes arbitrary probability spaces and adapted dependent errors obeying
the conditional variance budget, exactly as in the article. 
-/
inductive MseValue (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r σ : ℝ) : ℝ → Prop where
  | model (E Ω : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E] [FiniteDimensional ℝ E] [mΩ : MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (𝓕 : Filtration ℕ mΩ)
      (w : ℕ → Ω → E) (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ)
      (hσ : ∀ s, s < N → μ[fun ω => ‖w s ω‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ => σ ^ 2)
      (H : E →ₗ[ℝ] E) (hH : Analysis.Admissible I H) (initial : E) (hi : ‖initial‖ ≤ r) :
      MseValue h I r σ (∫ ω, ‖h.stochasticOutput H initial w ω‖ ^ 2 ∂μ)

/-- All MSEs produced by actual admissible martingale oracle models.
Use: the literal domain of the martingale worst-case supremum. 
-/
def mseValues (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r σ : ℝ) : Set ℝ :=
  {v | MseValue h I r σ v}

/-- Universal MSE bounds are exactly upper bounds on actually achieved model MSEs.
Use: all probability and dimension quantifiers agree with the literal article class. 
-/
theorem mseValues_upperBounds (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r σ : ℝ) : upperBounds (mseValues h I r σ) = {C | MseBound h I r σ C} := by
  ext C
  constructor
  · intro hb E Ω _ _ _ _ _ μ _ 𝓕 w hw hσ H hH initial hi
    exact hb (MseValue.model E Ω μ 𝓕 w hw hσ H hH initial hi)
  · intro hb v hv
    cases hv with
    | model E Ω μ 𝓕 w hw hσ H hH initial hi => exact hb E Ω μ 𝓕 w hw hσ H hH initial hi

/-- A zero martingale on a genuine probability space actually achieves zero MSE.
Use: nonemptiness of the full stochastic risk domain at every variance bound. 
-/
theorem zero_mem_mseValues (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r σ : ℝ) (hr : 0 ≤ r) : 0 ∈ mseValues h I r σ := by
  let H := InexactRealizations.History.scalarOperator I.mu
  have hzero : ∀ s ω, InexactRealizations.Probability.Signs.stream N 0 s ω = 0 := by
    intro s ω
    simp [InexactRealizations.Probability.Signs.stream, InexactRealizations.Probability.Signs.error, InexactRealizations.Probability.Signs.value]
  have hout : (∫ ω, ‖h.stochasticOutput H 0 (InexactRealizations.Probability.Signs.stream N 0) ω‖ ^ 2
      ∂InexactRealizations.Probability.Signs.law N) = 0 := by
    simp only [h.stochasticOutput_response, hzero, map_zero, Finset.sum_const_zero, zero_add,
      norm_zero, zero_pow (by omega : 2 ≠ 0), integral_zero]
  rw [← hout]
  exact MseValue.model ℝ (Fin N → Bool) (InexactRealizations.Probability.Signs.law N)
    (InexactRealizations.Probability.Signs.past N 0) (InexactRealizations.Probability.Signs.stream N 0)
    (InexactRealizations.Probability.Signs.martingale N 0)
    (by
      intro s hs
      rw [InexactRealizations.Probability.Signs.conditional_variance N 0 s hs]
      exact Filter.Eventually.of_forall (fun _ => by simpa using sq_nonneg σ)) H
    (Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩) 0 (by simpa only [norm_zero] using hr)

/-- All actual martingale MSE values form a nonempty bounded set.
Use: validates the stochastic real supremum under the exact oracle assumptions. 
-/
theorem mseValues_nonempty_bddAbove (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (r σ : ℝ) (hr : 0 ≤ r) :
    (mseValues h I r σ).Nonempty ∧ BddAbove (mseValues h I r σ) := by
  obtain ⟨C, hC⟩ := mseBounds_nonempty h I he r σ hr
  exact ⟨⟨0, zero_mem_mseValues h I r σ hr⟩,
    ⟨C, by rw [mseValues_upperBounds]; exact hC⟩⟩

/-- The martingale MSE risk equals the literal supremum over all actual models.
Use: variance and causality quantifiers are preserved exactly. 
-/
theorem mseRisk_eq_sSup (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (r σ : ℝ) (hr : 0 ≤ r) :
    mseRisk h I r σ = sSup (mseValues h I r σ) := by
  obtain ⟨hne, hbd⟩ := mseValues_nonempty_bddAbove h I he r σ hr
  unfold mseRisk
  rw [← mseValues_upperBounds]
  exact csInf_upperBounds_eq_csSup hbd hne

end
end InexactRealizations.Risk
