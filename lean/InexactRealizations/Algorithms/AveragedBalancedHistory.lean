import InexactRealizations.Algorithms.AveragedBalancedNominal
import InexactRealizations.Balanced.History
import InexactRealizations.Synthesis.Exactness

/-! The literal current nine-vector program realizes the original Balanced
history for every oracle, by its proved nominal queries and terminal and
the unrestricted uniqueness theorem. 
-/
namespace InexactRealizations.Algorithms.AveragedBalanced
noncomputable section
open Polynomial
open InexactRealizations.Balanced

def journalProgram (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : RegisterProgram 9 N :=
  (parameters I N).program

theorem translationNormalized (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    (journalProgram I N).TranslationNormalized where
  query s := by
    rw [RegisterProgram.queryCoefficient_initial_value]
    change (parameters I N).program.queryAt (fun _ (_ : ℝ) ↦ 0) 1 s = 1
    have hh := nominal_query I hN 0 s
    have hz : I.z 0 = I.eta := by simp [InexactRealizations.Operators.SpectralInterval.z, InexactRealizations.Operators.SpectralInterval.eta]
    rw [hz] at hh
    have he : (psi N s.val).eval I.eta / normalizer I N s.val = 1 :=
      div_self (normalizer_pos I hN s.isLt).ne'
    rw [he] at hh
    simpa only [zero_mul] using hh
  output := by
    change (journalProgram I N).coefficientState N 0 none = 1
    rw [RegisterProgram.coefficientState_initial_value]
    change (parameters I N).program.output (fun _ (_ : ℝ) ↦ 0) 1 = 1
    have hh := nominal_output I hN 0
    have he : (I.residual N).eval 0 = 1 := by
      rw [I.residual_eval]
      simp only [InexactRealizations.Operators.SpectralInterval.z, mul_zero, sub_zero]
      exact div_self (I.den_ne N)
    rw [he] at hh
    simpa only [zero_mul] using hh

def actualHistory (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) : InexactRealizations.History N :=
  (journalProgram I N).history (translationNormalized I hN)

theorem actualHistory_query_eval (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) (lam : ℝ) :
    ((actualHistory I N hN).query s).eval lam =
      (psi N s.val).eval (I.z lam) / normalizer I N s.val := by
  have hp := (journalProgram I N).query_eq_history (translationNormalized I hN) (1 : ℝ)
    (fun _ y ↦ InexactRealizations.History.scalarOperator lam y + (0 : ℝ)) s
  have hh := (actualHistory I N hN).nominal_query (InexactRealizations.History.scalarOperator lam) (1 : ℝ)
    ((actualHistory I N hN).oracleExecution (InexactRealizations.History.scalarOperator lam) 1 (fun _ ↦ 0)) s
  simp only [InexactRealizations.History.oracleExecution, InexactRealizations.History.scalarOperator_polynomial_action, mul_one] at hh
  have he := hp.trans hh
  have hn := nominal_query I hN lam s
  simp only [InexactRealizations.History.scalarOperator_apply, add_zero] at he
  exact he.symm.trans hn

theorem actualHistory_exact (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (actualHistory I N hN).ChebyshevExact I := by
  apply Polynomial.funext
  intro lam
  have hp := (journalProgram I N).output_eq_history (translationNormalized I hN) (1 : ℝ)
    (fun _ y ↦ InexactRealizations.History.scalarOperator lam y + (0 : ℝ))
  rw [InexactRealizations.History.oracleOutput_linear, InexactRealizations.History.noiseless_scalar_output, mul_one] at hp
  simp only [InexactRealizations.History.scalarOperator_apply, add_zero] at hp
  exact hp.symm.trans (nominal_output I hN lam)

theorem actualHistory_eq_balanced (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    actualHistory I N hN = InexactRealizations.Balanced.history I N hN := by
  have hq (s : Fin N) : (actualHistory I N hN).query s = (InexactRealizations.Balanced.history I N hN).query s := by
    apply Polynomial.funext
    intro lam
    rw [actualHistory_query_eval, ← InexactRealizations.History.chartQuery_physical_eval,
      InexactRealizations.Balanced.history_chartQuery]
    simp only [eval_mul, eval_C, one_div_mul_eq_div]
  apply (InexactRealizations.Balanced.queryFamily I N hN).realize_unique I
    (InexactRealizations.Balanced.queryFamily_eta I N hN) (actualHistory I N hN) (actualHistory_exact I N hN)
  intro s
  change ((actualHistory I N hN).query s).comp (InexactRealizations.GradedFamily.chart I) = _
  rw [hq]
  exact InexactRealizations.Balanced.history_chartQuery I N hN s

theorem query_eq_history {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) (s : Fin N) :
    (journalProgram I N).queryAt oracle initial s =
      (InexactRealizations.Balanced.history I N hN).oracleQuery initial oracle s := by
  have hh := (journalProgram I N).query_eq_history (translationNormalized I hN) initial oracle s
  change _ = (actualHistory I N hN).oracleQuery initial oracle s at hh
  rw [actualHistory_eq_balanced] at hh
  exact hh

theorem output_eq_history {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) :
    (journalProgram I N).output oracle initial =
      (InexactRealizations.Balanced.history I N hN).oracleOutput initial oracle := by
  have hh := (journalProgram I N).output_eq_history (translationNormalized I hN) initial oracle
  change _ = (actualHistory I N hN).oracleOutput initial oracle at hh
  rw [actualHistory_eq_balanced] at hh
  exact hh

end
end InexactRealizations.Algorithms.AveragedBalanced
