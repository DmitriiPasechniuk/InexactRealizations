import InexactRealizations.Comparisons.Competitors.Propagation
import InexactRealizations.Operators.Stepsize.Basic
import InexactRealizations.History.Realization

namespace InexactRealizations.Comparisons.Competitors.Stepsize
noncomputable section
open InexactRealizations.Operators Polynomial
open scoped BigOperators Matrix

/-- Literal gradient steps with the prescribed scalar schedule. -/
def config (gamma : ℕ → ℝ) : Momentum where
  alpha := gamma
  beta _ := 0
  extrapolated := false
  reset _ := false

/-- The actual N-call causal history of the scalar gradient-step schedule. -/
def history (N : ℕ) (gamma : ℕ → ℝ) : InexactRealizations.History N := (config gamma).history N

/-- The exact zero-momentum spectral matrix. -/
theorem matrix_eq (gamma : ℕ → ℝ) (s : ℕ) (lam : ℝ) :
    (config gamma).matrix s lam = !![1-gamma s*lam,0;1,0] := by
  simp [Momentum.matrix,Momentum.baseMatrix,config]

/-- Every finite ordered product has precisely the scalar residual in its first row. -/
theorem product_row (gamma : ℕ → ℝ) (start n : ℕ) (lam : ℝ) :
    (orderedProduct (fun i => (config gamma).matrix (start+i) lam) n) 0 =
      ![orderedProduct (fun i => 1-gamma (start+i)*lam) n,0] := by
  induction n with
  | zero => ext j; fin_cases j <;> simp
  | succ n ih =>
    have h0 := congrFun ih 0
    have h1 := congrFun ih 1
    ext j
    fin_cases j <;>
      simp [orderedProduct_succ, Matrix.mul_apply, Fin.sum_univ_two, matrix_eq gamma (start+n) lam, h0, h1]

/-- The scalar first row acts independently of the initial previous-state slot. -/
theorem product_action (gamma : ℕ → ℝ) (start n : ℕ) (lam x p : ℝ) :
    (orderedProduct (fun i => (config gamma).matrix (start+i) lam) n *ᵥ ![x,p]) 0 =
      orderedProduct (fun i => 1-gamma (start+i)*lam) n * x := by
  have h0 := congrFun (product_row gamma start n lam) 0
  have h1 := congrFun (product_row gamma start n lam) 1
  simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail, h0, h1]

/-- The actual terminal is exactly the existing scalar stepsize residual polynomial. -/
theorem terminal (N : ℕ) (gamma : ℕ → ℝ) :
    (history N gamma).terminal = InexactRealizations.Operators.Stepsize.polynomial gamma N := by
  apply Polynomial.funext
  intro lam
  rw [history, Momentum.terminal_eval]
  have hp := product_action gamma 0 N lam 1 1
  rw [InexactRealizations.Operators.Stepsize.polynomial_eval, InexactRealizations.Operators.Stepsize.scalarTransfer_eq]
  simpa only [Nat.zero_add,mul_one] using hp

end
end InexactRealizations.Comparisons.Competitors.Stepsize
