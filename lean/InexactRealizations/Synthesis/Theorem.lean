import InexactRealizations.Synthesis.Normalized
import InexactRealizations.History.Execution
import InexactRealizations.History.Continuity

namespace InexactRealizations
noncomputable section
open Polynomial
open scoped BigOperators

/-- The complete normalized algebraic identity for an actual history.
Use: a single entry point records both degree orders, normalization, the physical
Bezoutian, continuous diagonal extension and the normalized factorization. 
-/
theorem realization_identity {N : ℕ} (h : History N) (hN : 0 < N)
    (I : InexactRealizations.Operators.SpectralInterval) (he : h.ChebyshevExact I) :
    (∀ s, (h.query s).degree = (s.val : WithBot ℕ) ∧
      (h.response s).degree = ((N - 1 - s.val : ℕ) : WithBot ℕ)) ∧
    (∀ s, (h.chartQuery I s).degree = (s.val : WithBot ℕ) ∧
      (h.chartFactor I s).degree = ((N - 1 - s.val : ℕ) : WithBot ℕ) ∧
      (h.chartQuery I s).eval I.eta = 1) ∧
    (∀ x y : ℝ, (∑ s, (h.response s).eval x * (h.query s).eval y) =
      History.dividedDifference h.terminal x y) ∧
    Continuous (fun xy : ℝ × ℝ => History.dividedDifference h.terminal xy.1 xy.2) ∧
    (∀ x y : ℝ, (∑ s, (h.chartFactor I s).eval x * (h.chartQuery I s).eval y) =
      chebyshevBezout N x y) := by
  exact ⟨fun s => ⟨h.query_degree_eq hN (h.exact_terminal_natDegree I he) s,
      h.response_degree_eq hN (h.exact_terminal_natDegree I he) s⟩,
    fun s => ⟨h.chartQuery_degree I hN he s, h.chartFactor_degree I hN he s,
      h.chartQuery_eta I s⟩,
    h.physical_bezout_all, h.continuous_physical_bezout, h.chart_factorization I he⟩

namespace History
variable {N : ℕ}

/-- The normalized query evaluated in physical spectral coordinates is the actual query.
Use: the explicit change-of-coordinate dictionary. 
-/
theorem chartQuery_physical_eval (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (s : Fin N) (lam : ℝ) :
    (h.chartQuery I s).eval (I.z lam) = (h.query s).eval lam := by
  have hc := congrArg (fun p : ℝ[X] => p.eval lam) (GradedFamily.chart_comp_coordinate I)
  simp only [eval_comp, eval_sub, eval_C, eval_mul, eval_X] at hc
  rw [← I.z_eq] at hc
  simp only [chartQuery, eval_comp, hc]

/-- The normalized factor recovers the actual physical response with exact scale.
Use: transfers spectral energies of `f_s` back to physical oracle sensitivities. 
-/
theorem chartFactor_physical_eval (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (s : Fin N) (lam : ℝ) :
    (h.response s).eval lam =
      (-4 * I.epsilon N / I.delta) * (h.chartFactor I s).eval (I.z lam) := by
  have hd : I.delta ≠ 0 := ne_of_gt I.delta_pos
  have he : I.epsilon N ≠ 0 := one_div_ne_zero (I.den_ne N)
  have hc := congrArg (fun p : ℝ[X] => p.eval lam) (GradedFamily.chart_comp_coordinate I)
  simp only [eval_comp, eval_sub, eval_C, eval_mul, eval_X] at hc
  rw [← I.z_eq] at hc
  simp only [chartFactor, eval_mul, eval_C, eval_comp, hc]
  field_simp

end History

end
end InexactRealizations
