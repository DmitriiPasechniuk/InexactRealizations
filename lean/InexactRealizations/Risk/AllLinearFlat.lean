import InexactRealizations.Risk.AllLinearOptima

namespace InexactRealizations.Risk.AllLinear
noncomputable section
open Set MeasureTheory

theorem flat_random_objective (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r σ : ℝ) (hr : 0 ≤ r) :
    randomMseRisk (InexactRealizations.Flat.history I N hN) I r σ =
      objective (r ^ 2) (σ ^ 2 / (I.mu ^ 2 * N)) (I.epsilon N) := by
  have hb : RandomMseBound (InexactRealizations.Flat.history I N hN) I r σ
      (objective (r ^ 2) (σ ^ 2 / (I.mu ^ 2 * N)) (I.epsilon N)) := by
    intro E Ω _ _ _ _ _ μ _ 𝓕 w hw hσ H hH V hV hV₂ hVr
    have hh := relaxedFlat_random_mse_upper I hN H hH V hV hV₂ hw r σ hVr hσ
      (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
    simpa only [relaxedFlat, InexactRealizations.History.relax_one, relaxedTerminalBound,
      sub_self, zero_add, one_mul] using hh
  apply le_antisymm
  · exact csInf_le ⟨0, fun _ hC ↦ mseBounds_nonneg _ I hr (deterministicBound_of_randomBound _ I hr hC)⟩ hb
  · rw [← flat_objective I N hN r σ hr]
    exact mseRisk_le_randomMseRisk _ I r σ hr

theorem flat_all_linear_random_optimal_iff (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r σ : ℝ) (hr : 0 ≤ r) :
    randomMseRisk (InexactRealizations.Flat.history I N hN) I r σ = allLinearValue I N r σ ↔
      (σ ^ 2 / (I.mu ^ 2 * N)) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2 := by
  rw [flat_random_objective I N hN r σ hr]
  have he := epsilon_unit I (by omega : 0 < N)
  exact flat_attains_iff (sq_nonneg r) (by positivity) he.1 he.2

theorem flat_all_linear_random_factor (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r σ : ℝ) (hr : 0 < r) :
    randomMseRisk (InexactRealizations.Flat.history I N hN) I r σ ≤
      (1 + (σ ^ 2 / (I.mu ^ 2 * N)) / r ^ 2) * allLinearValue I N r σ := by
  rw [flat_random_objective I N hN r σ hr.le]
  have he := epsilon_unit I (by omega : 0 < N)
  exact flat_multiplicative_bound (sq_pos_of_pos hr) (by positivity) he.1 he.2

end
end InexactRealizations.Risk.AllLinear
