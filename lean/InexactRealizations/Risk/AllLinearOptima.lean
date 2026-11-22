import InexactRealizations.Risk.AllLinearClass
import InexactRealizations.Risk.AllLinearLower

/-! Current Theorem3.2: exact attained minima over all fixed-coefficient
causal linear histories, for deterministic and random initial error.
The separate arbitrary-adaptive-method clause requires its own proof. 
-/
namespace InexactRealizations.Risk.AllLinear
noncomputable section
open Set MeasureTheory
variable {N : ℕ}

def allLinearValue (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (r σ : ℝ) : ℝ :=
  value (r ^ 2) (σ ^ 2 / (I.mu ^ 2 * N)) (I.epsilon N)

def optimalShrink (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (r σ : ℝ) : ℝ :=
  shrink (r ^ 2) (σ ^ 2 / (I.mu ^ 2 * N)) (I.epsilon N)

def optimalHistory (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (r σ : ℝ) : InexactRealizations.History N :=
  relaxedFlat I N hN (optimalShrink I N r σ)

theorem all_mseRisk_lower (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (hN : 2 ≤ N) (r σ : ℝ) (hr : 0 ≤ r) : allLinearValue I N r σ ≤ InexactRealizations.Risk.mseRisk h I r σ :=
  le_csInf (allMseBounds_nonempty h I r σ hr) (fun _ hb ↦ allMseBound_lower h I hN hr hb)

theorem all_randomMseRisk_lower (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (hN : 2 ≤ N) (r σ : ℝ) (hr : 0 ≤ r) : allLinearValue I N r σ ≤ randomMseRisk h I r σ :=
  (all_mseRisk_lower h I hN r σ hr).trans (mseRisk_le_randomMseRisk h I r σ hr)

theorem optimalHistory_mseRisk (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r σ : ℝ) (hr : 0 ≤ r) :
    InexactRealizations.Risk.mseRisk (optimalHistory I N hN r σ) I r σ = allLinearValue I N r σ := by
  apply le_antisymm
  · exact csInf_le ⟨0, fun _ hb ↦ mseBounds_nonneg _ I hr hb⟩
      (deterministicBound_of_randomBound _ I hr (shrunkFlat_randomBound I N hN r σ))
  · exact all_mseRisk_lower _ I hN r σ hr

theorem optimalHistory_randomMseRisk (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r σ : ℝ) (hr : 0 ≤ r) :
    randomMseRisk (optimalHistory I N hN r σ) I r σ = allLinearValue I N r σ := by
  apply le_antisymm
  · exact csInf_le ⟨0, fun _ hb ↦ mseBounds_nonneg _ I hr
      (deterministicBound_of_randomBound _ I hr hb)⟩ (shrunkFlat_randomBound I N hN r σ)
  · exact all_randomMseRisk_lower _ I hN r σ hr

theorem all_linear_mse_minimum (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r σ : ℝ) (hr : 0 ≤ r) :
    IsLeast {v : ℝ | ∃ h : InexactRealizations.History N, v = InexactRealizations.Risk.mseRisk h I r σ}
      (allLinearValue I N r σ) := by
  refine ⟨⟨optimalHistory I N hN r σ, (optimalHistory_mseRisk I N hN r σ hr).symm⟩, ?_⟩
  rintro _ ⟨h, rfl⟩
  exact all_mseRisk_lower h I hN r σ hr

theorem all_linear_random_mse_minimum (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r σ : ℝ) (hr : 0 ≤ r) :
    IsLeast {v : ℝ | ∃ h : InexactRealizations.History N, v = randomMseRisk h I r σ}
      (allLinearValue I N r σ) := by
  refine ⟨⟨optimalHistory I N hN r σ, (optimalHistory_randomMseRisk I N hN r σ hr).symm⟩, ?_⟩
  rintro _ ⟨h, rfl⟩
  exact all_randomMseRisk_lower h I hN r σ hr

theorem flat_objective (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r σ : ℝ) (hr : 0 ≤ r) :
    InexactRealizations.Risk.mseRisk (InexactRealizations.Flat.history I N hN) I r σ =
      objective (r ^ 2) (σ ^ 2 / (I.mu ^ 2 * N)) (I.epsilon N) := by
  rw [InexactRealizations.Flat.mseRisk_eq I N hN r σ hr]
  unfold InexactRealizations.Risk.mseOptimum objective InexactRealizations.Lower.additiveScale
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp [I.mu_pos.ne', hn]

theorem flat_all_linear_optimal_iff (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r σ : ℝ) (hr : 0 ≤ r) :
    InexactRealizations.Risk.mseRisk (InexactRealizations.Flat.history I N hN) I r σ = allLinearValue I N r σ ↔
      (σ ^ 2 / (I.mu ^ 2 * N)) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2 := by
  rw [flat_objective I N hN r σ hr]
  have he := epsilon_unit I (by omega : 0 < N)
  exact flat_attains_iff (sq_nonneg r) (by positivity) he.1 he.2

theorem flat_all_linear_factor (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r σ : ℝ) (hr : 0 < r) :
    InexactRealizations.Risk.mseRisk (InexactRealizations.Flat.history I N hN) I r σ ≤
      (1 + (σ ^ 2 / (I.mu ^ 2 * N)) / r ^ 2) * allLinearValue I N r σ := by
  rw [flat_objective I N hN r σ hr.le]
  have he := epsilon_unit I (by omega : 0 < N)
  exact flat_multiplicative_bound (sq_pos_of_pos hr) (by positivity) he.1 he.2

theorem optimalShrink_zero_zero (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    optimalShrink I N 0 0 = 0 := by simp [optimalShrink, shrink]

end
end InexactRealizations.Risk.AllLinear
