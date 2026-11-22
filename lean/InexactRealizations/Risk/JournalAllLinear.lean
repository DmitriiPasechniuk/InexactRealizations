import InexactRealizations.Risk.AllLinearFlat
import InexactRealizations.Risk.RandomSupremum

/-! Current Theorem3.2, fixed-coefficient linear-history clauses only.
The arbitrary adaptive/nonlinear-method clause is a separate obligation. 
-/
namespace InexactRealizations.Risk.AllLinear
noncomputable section
open Set

theorem journal_all_linear_fixed_coefficients (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r σ : ℝ) (hr : 0 ≤ r) :
    IsLeast {v : ℝ | ∃ h : InexactRealizations.History N, v = InexactRealizations.Risk.mseRisk h I r σ} (allLinearValue I N r σ) ∧
    IsLeast {v : ℝ | ∃ h : InexactRealizations.History N, v = randomMseRisk h I r σ} (allLinearValue I N r σ) ∧
    IsLeast (objective (r ^ 2) (σ ^ 2 / (I.mu ^ 2 * N)) '' Icc (I.epsilon N) 1) (allLinearValue I N r σ) := by
  have he := epsilon_unit I (by omega : 0 < N)
  exact ⟨all_linear_mse_minimum I N hN r σ hr, all_linear_random_mse_minimum I N hN r σ hr,
    value_isLeast (sq_nonneg r) (by positivity) he.1 he.2⟩

theorem journal_all_linear_flat_iff (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r σ : ℝ) (hr : 0 ≤ r) :
    (InexactRealizations.Risk.mseRisk (InexactRealizations.Flat.history I N hN) I r σ = allLinearValue I N r σ ↔
      (σ ^ 2 / (I.mu ^ 2 * N)) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2) ∧
    (randomMseRisk (InexactRealizations.Flat.history I N hN) I r σ = allLinearValue I N r σ ↔
      (σ ^ 2 / (I.mu ^ 2 * N)) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2) :=
  ⟨flat_all_linear_optimal_iff I N hN r σ hr, flat_all_linear_random_optimal_iff I N hN r σ hr⟩

end
end InexactRealizations.Risk.AllLinear
