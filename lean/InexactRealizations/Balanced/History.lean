import InexactRealizations.Balanced.Basis

namespace InexactRealizations.Balanced
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- The eta-normalized graded query family prescribed by Balanced. -/
def queryFamily (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    GradedFamily N where
  poly s := C (1 / normalizer I N s) * psi N s
  degree_eq s := by
    rw [degree_C_mul (one_div_ne_zero (ne_of_gt (normalizer_pos I hN s.isLt)))]
    exact psi_degree hN s.isLt

/-- Every normalized query takes value one at the zero-Hessian coordinate eta. -/
theorem queryFamily_eta (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : ((queryFamily I N hN).poly s).eval I.eta = 1 := by
  simp only [queryFamily, eval_mul, eval_C, normalizer]
  exact one_div_mul_cancel (ne_of_gt (normalizer_pos I hN s.isLt))

/-- The actual causal Balanced history produced by exact finite synthesis. -/
def history (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) : InexactRealizations.History N :=
  (queryFamily I N hN).realize I (queryFamily_eta I N hN)

/-- Balanced belongs to the full Chebyshev-exact history comparison class. -/
theorem history_exact (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (history I N hN).ChebyshevExact I :=
  (queryFamily I N hN).realize_exact I (queryFamily_eta I N hN)

/-- The constructed physical history has exactly the prescribed stopped-parity queries. -/
theorem history_chartQuery (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : (history I N hN).chartQuery I s =
      C (1 / normalizer I N s) * psi N s :=
  (queryFamily I N hN).realize_chartQuery I (queryFamily_eta I N hN) s

end
end InexactRealizations.Balanced
