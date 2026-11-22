import InexactRealizations.Algorithms.AveragedBalancedData
import InexactRealizations.Comparisons.Classical.History
import InexactRealizations.Comparisons.Competitors.Propagation

/-! The literal Prefix recurrence used inside current is the
classical history, including startup and arbitrary oracle errors. 
-/
namespace InexactRealizations.Roundoff
noncomputable section
open Polynomial
open InexactRealizations.Algorithms InexactRealizations.Algorithms.AveragedBalanced
open InexactRealizations.Comparisons.Competitors

def prefixMomentum (I : InexactRealizations.Operators.SpectralInterval) : Momentum where
  alpha := alpha I
  beta := beta I
  extrapolated := false
  reset _ := false

theorem prefix_nominal_state (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (lam : ℝ)
    (k : ℕ) (hk : k ≤ N) :
    (prefixMomentum I).scalarState N lam 1 (fun _ ↦ 0) k =
      ![(I.residual k).eval lam, (I.residual (k - 1)).eval lam] := by
  induction k with
  | zero =>
    ext i
    fin_cases i <;> simp [Momentum.scalarState, Momentum.program, RegisterProgram.runPrefix,
      RegisterProgram.initialState]
  | succ k ih =>
    rw [Momentum.scalarState_succ _ _ _ _ _ _ (by omega), ih (by omega), Momentum.matrix_mulVec]
    ext i
    fin_cases i
    · simpa [Momentum.scalarForcing, show k < N by omega, prefixMomentum,
        Momentum.previous, Momentum.query] using (prefix_eval_step I k lam).symm
    · simp [Momentum.scalarForcing, show k < N by omega]

theorem prefix_query_eval (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (s : Fin N) (lam : ℝ) :
    (((prefixMomentum I).history N).query s).eval lam = (I.residual s.val).eval lam := by
  rw [Momentum.query_eval_actual, Momentum.queryAt_eq]
  change ((prefixMomentum I).scalarState N lam 1 (fun _ ↦ 0) s.val) 0 = _
  rw [prefix_nominal_state I N lam s.val s.isLt.le]
  rfl

theorem prefix_terminal_eval (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (lam : ℝ) :
    ((prefixMomentum I).history N).terminal.eval lam = (I.residual N).eval lam := by
  have hp := (prefixMomentum I).output_eq_history N (Momentum.scalarOracle N lam (fun _ ↦ 0)) (1 : ℝ)
  have ho : Momentum.scalarOracle N lam (fun _ ↦ 0) =
      fun _ y ↦ InexactRealizations.History.scalarOperator lam y + (0 : ℝ) := rfl
  rw [ho, InexactRealizations.History.oracleOutput_linear, InexactRealizations.History.noiseless_scalar_output, mul_one] at hp
  rw [← hp, ← ho, Momentum.scalar_output, prefix_nominal_state I N lam N le_rfl]
  rfl

theorem prefix_history_eq_classical (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    (prefixMomentum I).history N = InexactRealizations.Classical.history I N := by
  have he : ((prefixMomentum I).history N).ChebyshevExact I := by
    apply Polynomial.funext
    exact prefix_terminal_eval I N
  have hq (s : Fin N) : ((prefixMomentum I).history N).query s = (InexactRealizations.Classical.history I N).query s := by
    apply Polynomial.funext
    intro lam
    rw [prefix_query_eval, InexactRealizations.Classical.query_eval, I.residual_eval]
  apply (InexactRealizations.Classical.queryFamily I N).realize_unique I (InexactRealizations.Classical.queryFamily_eta I N)
    ((prefixMomentum I).history N) he
  intro s
  change (((prefixMomentum I).history N).query s).comp (InexactRealizations.GradedFamily.chart I) = _
  rw [hq]
  exact InexactRealizations.Classical.history_chartQuery I N s

end
end InexactRealizations.Roundoff
