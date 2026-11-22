import InexactRealizations.Algorithms.AveragedBalancedHistory
import InexactRealizations.Algorithms.AveragedBalancedBounds

/-! Current: exact ratio preparation and the
nine-register compensated averaged-Prefix program, for all oracle errors. 
-/
namespace InexactRealizations.Algorithms.AveragedBalanced
noncomputable section
open scoped BigOperators

theorem journal_balanced_queries {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) (s : Fin N) :
    (journalProgram I N).queryAt oracle initial s =
      (InexactRealizations.Balanced.history I N hN).oracleQuery initial oracle s :=
  query_eq_history I N hN oracle initial s

theorem journal_balanced_output {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) :
    (journalProgram I N).output oracle initial =
      (InexactRealizations.Balanced.history I N hN).oracleOutput initial oracle :=
  output_eq_history I N hN oracle initial

theorem journal_balanced_physical_response {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (initial : E) (noise : Fin N → E) :
    (journalProgram I N).output (fun s y ↦ H y + noise s) initial =
      (Polynomial.aeval H (I.residual N)) initial +
        ∑ s, (Polynomial.aeval H ((InexactRealizations.Balanced.history I N hN).response s)) (noise s) := by
  have he := InexactRealizations.Balanced.history_exact I N hN
  change (InexactRealizations.Balanced.history I N hN).terminal = I.residual N at he
  rw [output_eq_history, InexactRealizations.History.oracleOutput_linear, InexactRealizations.History.physical_response, he]

theorem journal_balanced_oracle_calls {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (oracle : Fin N → E → E) (initial : E) :
    ((journalProgram I N).run oracle initial).calls = N := RegisterProgram.run_calls _ _ _

theorem journal_balanced_vector_slots : Fintype.card (Fin 9) = 9 := Fintype.card_fin 9

end
end InexactRealizations.Algorithms.AveragedBalanced
