import InexactRealizations.Risk.RelaxedFlat
import InexactRealizations.Risk.Suprema

/-! The two actual all-linear comparison classes in current Theorem3.2.
The first uses the existing physical risk; the second allows a square-
integrable initial error measurable at F0, with its original mean budget. 
-/
namespace InexactRealizations.Risk.AllLinear
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
variable {N : ℕ}

def RandomMseBound (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r σ C : ℝ) : Prop :=
  ∀ (E Ω : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ mΩ) (w : ℕ → Ω → E),
    InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ →
    (∀ s, s < N → μ[fun ξ ↦ ‖w s ξ‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ ↦ σ ^ 2) →
    ∀ (H : E →ₗ[ℝ] E), InexactRealizations.Analysis.Admissible I H →
    ∀ (V : Ω → E), StronglyMeasurable[𝓕 0] V → MemLp V 2 μ →
    (∫ ξ, ‖V ξ‖ ^ 2 ∂μ) ≤ r ^ 2 → (∫ ξ, ‖h.stochasticOutput H (V ξ) w ξ‖ ^ 2 ∂μ) ≤ C

def randomMseRisk (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r σ : ℝ) : ℝ :=
  sInf {C : ℝ | RandomMseBound h I r σ C}

theorem randomMseBounds_nonempty (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r σ : ℝ) :
    {C : ℝ | RandomMseBound h I r σ C}.Nonempty := by
  obtain ⟨B, hB, hp⟩ := InexactRealizations.Analysis.exists_polynomial_bound I h.terminal
  obtain ⟨P, hP⟩ := InexactRealizations.Risk.exists_responseBounds h I
  refine ⟨B ^ 2 * r ^ 2 + σ ^ 2 * ∑ s, P s ^ 2, ?_⟩
  intro E Ω _ _ _ _ _ μ _ 𝓕 w hw hσ H hH V hV hV₂ hr
  exact InexactRealizations.History.integral_randomInitial_stochasticOutput_le h I H hH V hV hV₂ hw
    r σ B hB hp P hP hr hσ

theorem deterministicBound_of_randomBound (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    {r σ C : ℝ} (hr : 0 ≤ r) (hb : RandomMseBound h I r σ C) : InexactRealizations.Risk.MseBound h I r σ C := by
  intro E Ω _ _ _ _ _ μ _ 𝓕 w hw hσ H hH initial hi
  apply hb E Ω μ 𝓕 w hw hσ H hH (fun _ ↦ initial) stronglyMeasurable_const (memLp_const initial)
  have hh := (sq_le_sq₀ (norm_nonneg initial) hr).mpr hi
  simpa only [integral_const, probReal_univ, one_smul] using hh

theorem allMseBounds_nonempty (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r σ : ℝ) (hr : 0 ≤ r) : {C : ℝ | InexactRealizations.Risk.MseBound h I r σ C}.Nonempty := by
  obtain ⟨C, hC⟩ := randomMseBounds_nonempty h I r σ
  exact ⟨C, deterministicBound_of_randomBound h I hr hC⟩

theorem mseBounds_nonneg (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    {r σ C : ℝ} (hr : 0 ≤ r) (hb : InexactRealizations.Risk.MseBound h I r σ C) : 0 ≤ C := by
  have he : C ∈ upperBounds (InexactRealizations.Risk.mseValues h I r σ) := by
    rw [InexactRealizations.Risk.mseValues_upperBounds]
    exact hb
  exact he (InexactRealizations.Risk.zero_mem_mseValues h I r σ hr)

theorem mseRisk_le_randomMseRisk (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r σ : ℝ) (hr : 0 ≤ r) : InexactRealizations.Risk.mseRisk h I r σ ≤ randomMseRisk h I r σ := by
  apply le_csInf (randomMseBounds_nonempty h I r σ)
  intro C hC
  exact csInf_le ⟨0, fun _ hb ↦ mseBounds_nonneg h I hr hb⟩
    (deterministicBound_of_randomBound h I hr hC)

theorem shrunkFlat_randomBound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (r σ : ℝ) :
    RandomMseBound (relaxedFlat I N hN (shrink (r ^ 2) (σ ^ 2 / (I.mu ^ 2 * N)) (I.epsilon N))) I r σ
      (value (r ^ 2) (σ ^ 2 / (I.mu ^ 2 * N)) (I.epsilon N)) := by
  intro E Ω _ _ _ _ _ μ _ 𝓕 w hw hσ H hH V hV hV₂ hr
  exact shrunkFlat_random_mse_upper I hN H hH V hV hV₂ hw r σ hr hσ

end
end InexactRealizations.Risk.AllLinear
