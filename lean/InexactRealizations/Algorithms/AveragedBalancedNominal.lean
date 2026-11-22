import InexactRealizations.Algorithms.AveragedBalancedData
import InexactRealizations.Algorithms.AveragedBalancedSelectors

/-! Nominal invariant of the actual nine-vector. The average
is kept in weighted form so the zero initial mass at even horizons is
handled directly, without division by an unused zero weight. 
-/
namespace InexactRealizations.Algorithms.AveragedBalanced
noncomputable section
open Polynomial Polynomial.Chebyshev
open InexactRealizations.Balanced AveragedParameters

structure NominalInvariant (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (lam : ℝ)
    (n : ℕ) (u : Fin 9 → ℝ) : Prop where
  current : u 0 = (I.residual n).eval lam
  previous : u 1 = (I.residual (n - 1)).eval lam
  correction0 : u 4 = 0
  correction1 : u 5 = 0
  average : ∀ j, n ≤ j → j ≤ n + 1 → j < N →
    mass I N j * u (averageSlot j) = (remainder N j).eval (I.z lam)
  gradient : ∀ j, n ≤ j → j ≤ n + 1 → 2 ≤ j → j < N → u (gradientSlot j) = lam * u (averageSlot j)

theorem nominal_initial (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (lam : ℝ) :
    NominalInvariant I N lam 0 ((parameters I N).program.initialState (1 : ℝ)).vectors := by
  constructor
  · simp [parameters, AveragedParameters.program, RegisterProgram.initialState]
  · simp [parameters, AveragedParameters.program, RegisterProgram.initialState]
  · simp [parameters, AveragedParameters.program, RegisterProgram.initialState]
  · simp [parameters, AveragedParameters.program, RegisterProgram.initialState]
  · intro j _ hj _
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp [remainder]
  · intro j _ hj hj₂ _
    omega

theorem nominal_query_value (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (s : Fin N) (lam : ℝ) (u : Fin 9 → ℝ) (hi : NominalInvariant I N lam s.val u) :
    (parameters I N).queryValue s u = (psi N s.val).eval (I.z lam) / normalizer I N s.val := by
  have ha := hi.average s.val le_rfl (by omega) s.isLt
  have hq := weighted_query I hN s.isLt lam (u (averageSlot s.val)) ha
  have hc := correction_value s.val u hi.correction0 hi.correction1
  unfold queryValue
  split_ifs with hsmall
  · simp only [theta, hsmall, ite_true, one_mul, sub_self, zero_mul, add_zero] at hq
    rw [hi.current]
    exact hq
  · simp only [parameters, smul_eq_mul, hc, add_zero, hi.current]
    exact hq

theorem nominal_recovered_value (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (s : Fin N) (lam : ℝ) (u : Fin 9 → ℝ) (hi : NominalInvariant I N lam s.val u) :
    (parameters I N).recoveredValue s u (lam * (parameters I N).queryValue s u) = lam * u 0 := by
  have hc := correction_value s.val u hi.correction0 hi.correction1
  by_cases hs : s.val < 2
  · simp only [recoveredValue, queryValue, hs, ite_true]
  · have hg := hi.gradient s.val le_rfl (by omega) (by omega) s.isLt
    have ht := (theta_unit I hN s.isLt).1.ne'
    simp only [recoveredValue, queryValue, hs, ite_false, parameters, smul_eq_mul, hc, add_zero, hg]
    field_simp [ht]
    ring

theorem nominal_step (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (s : Fin N) (lam : ℝ) (u : Fin 9 → ℝ) (hi : NominalInvariant I N lam s.val u) :
    NominalInvariant I N lam (s.val + 1)
      ((parameters I N).nextState s u (lam * (parameters I N).queryValue s u)) := by
  have hr := nominal_recovered_value I hN s lam u hi
  have hc := correction_value s.val u hi.correction0 hi.correction1
  have hcorr := nextState_corrections (parameters I N) s u
    (lam * (parameters I N).queryValue s u) hi.correction0 hi.correction1
  constructor
  · rw [nextState_x, hr, hi.current, hi.previous]
    simpa only [parameters, mul_assoc] using (prefix_eval_step I s.val lam).symm
  · simpa only [nextState_previous, Nat.add_sub_cancel] using hi.current
  · exact hcorr.1
  · exact hcorr.2
  · intro j hj hj' hjN
    rcases (show j = s.val + 1 ∨ j = s.val + 2 by omega) with rfl | rfl
    · rw [nextState_other_average]
      exact hi.average (s.val + 1) (by omega) le_rfl hjN
    · rw [averageSlot_add_two, nextState_current_average _ _ _ _ hjN]
      by_cases hs : s.val < 2
      · rw [ite_eq_left hs, hi.current]
        exact weighted_startup_step I N s.val hs lam
      · rw [ite_eq_right hs]
        simp only [parameters, hc, mul_zero, add_zero, hi.current]
        exact weighted_average_step I hN (by omega) hjN lam (u (averageSlot s.val))
          (hi.average s.val le_rfl (by omega) s.isLt)
  · intro j hj hj' hj₂ hjN
    rcases (show j = s.val + 1 ∨ j = s.val + 2 by omega) with rfl | rfl
    · rw [nextState_other_gradient, nextState_other_average]
      exact hi.gradient (s.val + 1) (by omega) le_rfl hj₂ hjN
    · rw [gradientSlot_add_two, averageSlot_add_two,
        nextState_current_gradient _ _ _ _ hjN, nextState_current_average _ _ _ _ hjN]
      by_cases hs : s.val < 2
      · simp only [hs, ite_true, queryValue]
      · rw [ite_eq_right hs, ite_eq_right hs, hr]
        have hg := hi.gradient s.val le_rfl (by omega) (by omega) s.isLt
        simp only [parameters, hc, mul_zero, add_zero, hg]
        ring

theorem nominal_run (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (lam : ℝ) (n : ℕ) (hn : n ≤ N) :
    NominalInvariant I N lam n
      (((parameters I N).program.runPrefix (fun _ (y : ℝ) ↦ lam * y) 1 n).vectors) := by
  induction n with
  | zero => exact nominal_initial I N lam
  | succ n ih =>
    have hlt : n < N := by omega
    have hi := ih (by omega)
    rw [RegisterProgram.runPrefix, dite_eq_left hlt]
    change NominalInvariant I N lam (n + 1)
      (((parameters I N).program.stage (fun _ (y : ℝ) ↦ lam * y) ⟨n, hlt⟩
        ⟨((parameters I N).program.runPrefix (fun _ (y : ℝ) ↦ lam * y) 1 n).vectors,
          ((parameters I N).program.runPrefix (fun _ (y : ℝ) ↦ lam * y) 1 n).calls⟩).vectors)
    rw [stage_vectors]
    exact nominal_step I hN ⟨n, hlt⟩ lam _ hi

theorem nominal_query (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (lam : ℝ) (s : Fin N) :
    (parameters I N).program.queryAt (fun _ (y : ℝ) ↦ lam * y) 1 s =
      (psi N s.val).eval (I.z lam) / normalizer I N s.val := by
  change executeLinear ((parameters I N).queryInstructions s) _ 8 = _
  rw [query_instructions_value]
  exact nominal_query_value I hN s lam _ (nominal_run I hN lam s.val s.isLt.le)

theorem nominal_output (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) (lam : ℝ) :
    (parameters I N).program.output (fun _ (y : ℝ) ↦ lam * y) 1 = (I.residual N).eval lam :=
  (nominal_run I hN lam N le_rfl).current

end
end InexactRealizations.Algorithms.AveragedBalanced
