import InexactRealizations.Roundoff.VectorRegisters
import InexactRealizations.Roundoff.PrefixExecution

/-! The oracle-error part of the discrepancy filter is the actual Balanced
response. This is proved from the printed nine-register execution, rather
than assuming its response coefficient in the roundoff identity. 
-/
namespace InexactRealizations.Roundoff
noncomputable section
open scoped BigOperators
open InexactRealizations.Algorithms InexactRealizations.Algorithms.AveragedBalanced AveragedParameters
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

structure ProgramErrorInvariant (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (H : E →ₗ[ℝ] E) (initial : E) (w : ℕ → E) (n : ℕ) (u : Fin 9 → E) : Prop where
  current : u 0 = (prefixPair I H initial (recoveredError I N w 0) n).1
  previous : u 1 = (prefixPair I H initial (recoveredError I N w 0) n).2
  correction0 : u 4 = 0
  correction1 : u 5 = 0
  discrepancy : ∀ j, n ≤ j → j ≤ n + 1 → 2 ≤ j → j < N →
    u (gradientSlot j) - H (u (averageSlot j)) = averageError I N w 0 (j - 2)

theorem programError_initial (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (H : E →ₗ[ℝ] E) (initial : E) (w : ℕ → E) :
    ProgramErrorInvariant I N H initial w 0 ((journalProgram I N).initialState initial).vectors := by
  constructor
  · simp [journalProgram, parameters, AveragedParameters.program, RegisterProgram.initialState, prefixPair]
  · simp [journalProgram, parameters, AveragedParameters.program, RegisterProgram.initialState, prefixPair]
  · simp [journalProgram, parameters, AveragedParameters.program, RegisterProgram.initialState]
  · simp [journalProgram, parameters, AveragedParameters.program, RegisterProgram.initialState]
  · intro j _ hj hj₂ _
    omega

theorem programError_step (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (initial : E) (w : ℕ → E) (s : Fin N) (u : Fin 9 → E)
    (hi : ProgramErrorInvariant I N H initial w s.val u) :
    ProgramErrorInvariant I N H initial w (s.val + 1)
      ((parameters I N).nextState s u (H ((parameters I N).queryValue s u) + w s.val)) := by
  have hrec := recovered_with_filter I hN s H w u hi.correction0 hi.correction1
    (fun hs ↦ hi.discrepancy s.val le_rfl (by omega) hs s.isLt)
  have hc := vector_correction_value s.val u hi.correction0 hi.correction1
  have hcorr := vector_next_corrections (parameters I N) s u
    (H ((parameters I N).queryValue s u) + w s.val) hi.correction0 hi.correction1
  constructor
  · change (1 + beta I s.val) • u 0 - beta I s.val • u 1 -
      alpha I s.val • (parameters I N).recoveredValue s u (H ((parameters I N).queryValue s u) + w s.val) = _
    rw [hrec, hi.current, hi.previous]
    rfl
  · change u 0 = _
    rw [hi.current]
    rfl
  · exact hcorr.1
  · exact hcorr.2
  · intro j hj hj' hj₂ hjN
    rcases (show j = s.val + 1 ∨ j = s.val + 2 by omega) with rfl | rfl
    · rw [vector_next_other_gradient, vector_next_other_average]
      exact hi.discrepancy (s.val + 1) (by omega) le_rfl hj₂ hjN
    · rw [gradientSlot_add_two, averageSlot_add_two, vector_next_current_gradient _ _ _ _ hjN,
        vector_next_current_average _ _ _ _ hjN]
      by_cases hs : s.val < 2
      · rw [ite_eq_left hs, ite_eq_left hs]
        simp only [queryValue, hs, ite_true]
        have he : averageError I N w (0 : ℕ → E) s.val = w s.val := by
          rcases (show s.val = 0 ∨ s.val = 1 by omega) with h0 | h1
          · simp [h0, averageError]
          · simp [h1, averageError]
        rw [Nat.add_sub_cancel, he]
        abel
      · rw [ite_eq_right hs, ite_eq_right hs]
        simp only [parameters, hc, smul_zero, add_zero]
        rw [affine_average_error]
        have hg := hi.discrepancy s.val le_rfl (by omega) (by omega) s.isLt
        rw [hg]
        have hh : (parameters I N).recoveredValue s u (H ((parameters I N).queryValue s u) + w s.val) - H (u 0) =
            recoveredError I N w 0 s.val := by rw [hrec]; abel
        dsimp only [parameters] at hh
        rw [hh, Nat.add_sub_cancel]
        have he := canonical_averaging I hN hjN w (0 : ℕ → E)
        simpa only [priorError, hs, ite_false, Pi.zero_apply, add_zero] using he.symm

theorem programError_run (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (initial : E) (w : ℕ → E) (n : ℕ) (hn : n ≤ N) :
    ProgramErrorInvariant I N H initial w n
      (((journalProgram I N).runPrefix (fun s y ↦ H y + w s.val) initial n).vectors) := by
  induction n with
  | zero => exact programError_initial I N H initial w
  | succ n ih =>
    have hlt : n < N := by omega
    have hi := ih (by omega)
    rw [RegisterProgram.runPrefix, dite_eq_left hlt]
    change ProgramErrorInvariant I N H initial w (n + 1)
      (((parameters I N).program.stage (fun s y ↦ H y + w s.val) ⟨n, hlt⟩
        ⟨((journalProgram I N).runPrefix (fun s y ↦ H y + w s.val) initial n).vectors,
          ((journalProgram I N).runPrefix (fun s y ↦ H y + w s.val) initial n).calls⟩).vectors)
    rw [stage_vectors]
    exact programError_step I hN H initial w ⟨n, hlt⟩ _ hi

theorem oracle_filter_response (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (w : ℕ → E) :
    (∑ s : Fin N, (Polynomial.aeval H ((InexactRealizations.Classical.history I N).response s)) (recoveredError I N w 0 s.val)) =
      ∑ s : Fin N, (Polynomial.aeval H ((InexactRealizations.Balanced.history I N hN).response s)) (w s.val) := by
  have he := (programError_run I hN H (0 : E) w N le_rfl).current
  change (journalProgram I N).output (fun s y ↦ H y + w s.val) 0 = (prefixPair I H 0 (recoveredError I N w 0) N).1 at he
  rw [journal_balanced_physical_response I N hN, prefixPair_response] at he
  simpa only [map_zero, zero_add] using he.symm

end
end InexactRealizations.Roundoff
