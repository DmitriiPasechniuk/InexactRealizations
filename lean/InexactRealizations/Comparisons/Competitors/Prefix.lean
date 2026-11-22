import InexactRealizations.Comparisons.Competitors.TwoTerm
import InexactRealizations.Comparisons.Classical.History
import InexactRealizations.Operators.Jacobi.Prefix

namespace InexactRealizations.Comparisons.Competitors.Prefix
noncomputable section
open InexactRealizations.Operators Polynomial

/-- Literal Prefix momentum coefficients through its normalized Jacobi method. -/
def config (I : SpectralInterval) : Momentum := TwoTerm.config (InexactRealizations.Operators.Prefix.jacobiData.method I)

/-- The actual N-call Prefix history. -/
def history (I : SpectralInterval) (N : ℕ) : InexactRealizations.History N := (config I).history N

/-- Fixed-point normalization holds at every noninitial Prefix call. -/
theorem fixed_point (I : SpectralInterval) (N s : ℕ) (hs : 0<s) (hsN : s<N) :
    (InexactRealizations.Operators.Prefix.jacobiData.method I).a s+(InexactRealizations.Operators.Prefix.jacobiData.method I).b s=1 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s≠0)
  exact InexactRealizations.Operators.Prefix.jacobiData.fixed_point I n
    (ne_of_gt (InexactRealizations.Operators.Prefix.jacobi_admissible I N (n+2) (by omega)))

/-- The separately prescribed initial step and zero initial momentum. -/
theorem initial_coefficients (I : SpectralInterval) :
    (config I).alpha 0=2/(I.L+I.mu) ∧ (config I).beta 0=0 := by
  simp [config,TwoTerm.config,InexactRealizations.Operators.Prefix.jacobi_gamma,InexactRealizations.Operators.Prefix.gamma]

/-- Every later used coefficient equals the printed classical Chebyshev formula. -/
theorem coefficients_succ (I : SpectralInterval) (s : ℕ) :
    (config I).alpha (s+1)=4*I.den (s+1)/(I.delta*I.den (s+2)) ∧
      (config I).beta (s+1)=I.den s/I.den (s+2) := by
  simp [config,TwoTerm.config,InexactRealizations.Operators.Prefix.jacobi_gamma,InexactRealizations.Operators.Prefix.gamma,
    InexactRealizations.Operators.Prefix.jacobi_b_succ]

/-- The actual terminal polynomial is the prescribed normalized Chebyshev terminal. -/
theorem terminal (I : SpectralInterval) (N : ℕ) : (history I N).terminal=I.residual N := by
  rw [history,config,TwoTerm.terminal _ N (fixed_point I N),
    ← JacobiData.realization,InexactRealizations.Operators.Prefix.jacobi_realization,
    InexactRealizations.Operators.Prefix.residualPolynomial_eq]

/-- Actual Prefix query polynomials are the complete normalized Chebyshev prefixes. -/
theorem query_polynomial (I : SpectralInterval) (N : ℕ) (s : Fin N) :
    (history I N).query s=I.residual s.val := by
  apply Polynomial.funext
  intro lam
  rw [history,config,TwoTerm.query_eval _ N (fixed_point I N),
    ← JacobiData.realization,InexactRealizations.Operators.Prefix.jacobi_realization,InexactRealizations.Operators.Prefix.scalar_exact]

/-- The literal Prefix oracle program realizes exactly the classical comparison history. -/
theorem history_eq_classical (I : SpectralInterval) (N : ℕ) :
    history I N=InexactRealizations.Classical.history I N := by
  apply (InexactRealizations.Classical.queryFamily I N).realize_unique I (InexactRealizations.Classical.queryFamily_eta I N)
  · exact terminal I N
  · intro s
    simp only [InexactRealizations.History.chartQuery,query_polynomial,InexactRealizations.Operators.SpectralInterval.residual,
      mul_comp,C_comp,comp_assoc,InexactRealizations.GradedFamily.coordinate_comp_chart,comp_X]
    simp only [InexactRealizations.Classical.queryFamily,one_div]

end
end InexactRealizations.Comparisons.Competitors.Prefix
