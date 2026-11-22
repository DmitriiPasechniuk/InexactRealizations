import InexactRealizations.Comparisons.Competitors.DFB
import InexactRealizations.Comparisons.Competitors.AveragedHistory
import InexactRealizations.Probability.Covariance

namespace InexactRealizations.Comparisons.Competitors.DFB
noncomputable section
open InexactRealizations.Operators Polynomial MeasureTheory
open scoped BigOperators

/-- The physical history of the literal DFB running-average implementation. -/
def history (L : ℝ) (N : ℕ) : InexactRealizations.History N := (config L).averagedHistory N

/-- DFB's actual averaged output agrees with its causal history for arbitrary oracles. -/
theorem output_eq_history {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : ℝ) (N : ℕ) (oracle : Fin N → E → E) (initial : E) :
    output L N oracle initial=(history L N).oracleOutput initial oracle :=
  Momentum.averagedOutput_eq_history _ _ _ _

/-- The actual averaged terminal evaluates to the printed d_j average. -/
theorem terminal_eval (L lam : ℝ) (N : ℕ) :
    (history L N).terminal.eval lam=terminalValue L lam N := by
  have h := output_eq_history L N (Momentum.scalarOracle N lam (fun _ => 0)) (1:ℝ)
  rw [terminalValue_actual] at h
  change terminalValue L lam N=(history L N).oracleOutput 1
    (fun _ x => InexactRealizations.History.scalarOperator lam x+(0:ℝ)) at h
  rw [InexactRealizations.History.oracleOutput_linear,InexactRealizations.History.nominal_output,
    InexactRealizations.History.scalarOperator_polynomial_action,mul_one] at h
  exact h.symm

/-- The averaged history response is its actual one-physical-call impulse. -/
theorem response_eval_actual (L lam : ℝ) (N : ℕ) (s : Fin N) :
    ((history L N).response s).eval lam=responseValue L lam N s := by
  unfold responseValue
  rw [output_eq_history]
  change _=(history L N).oracleOutput 0
    (fun j x => InexactRealizations.History.scalarOperator lam x+(if j=s then 1 else 0))
  rw [InexactRealizations.History.oracleOutput_linear,InexactRealizations.Risk.scalar_output]
  simp only [mul_zero,zero_add,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- The literal DFB average has exactly the stated finite physical error response. -/
theorem response_eval (L lam : ℝ) (hL : L≠0) (hlam : lam≠0) (N : ℕ) (s : Fin N) :
    ((history L N).response s).eval lam=-(1-d L lam (N-s.val))/(lam*((N:ℝ)+1)) := by
  rw [response_eval_actual,responseValue_eq L lam hL hlam]

end
end InexactRealizations.Comparisons.Competitors.DFB
