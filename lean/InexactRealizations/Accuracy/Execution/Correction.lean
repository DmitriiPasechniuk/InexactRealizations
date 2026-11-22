import InexactRealizations.Accuracy.Execution.Uniform

/-! The actual stored correction is O(u), even in the presence of oracle
errors. This is derived from the printed correction operations, not a
hypothesis on the execution. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Run
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO M : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

theorem older_correction_bound (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (s : ℕ) (hs : s < N) :
    ‖v.states s 5‖ ≤ u * (600 * stateEnvelope I.kappa N * M) := by
  have he := stateEnvelope_one I N
  have hS : 0 ≤ stateEnvelope I.kappa N * M := by positivity
  have hu1 : u ≤ 1 := by linarith
  cases s with
  | zero => rw [v.initial_eq]; simp [initialState]; positivity
  | succ s => cases s with
    | zero =>
      rw [v.step_eq ⟨0, by omega⟩]
      change ‖v.states 0 4‖ ≤ _
      rw [v.initial_eq]
      simp [initialState]
      positivity
    | succ s =>
      let a := v.stages ⟨s, by omega⟩
      have hv := v.global_state_bound hN hu hu2 huO huO1 hM hinitial htarget hH s (by omega)
      have hc := (a.averages_size_error hN hu hu1 hS hv).2.1
      have hvalid : s + 2 < N := hs
      have hc' : ‖a.nextCorrection‖ ≤ 600 * u * (stateEnvelope I.kappa N * M) := by
        simpa [exactStep, hvalid] using hc
      have hid : v.states (s + 2) 5 = a.nextCorrection := by
        rw [v.step_eq ⟨s + 1, by omega⟩]
        change v.states (s + 1) 4 = a.nextCorrection
        rw [v.step_eq ⟨s, by omega⟩]
        rfl
      rw [hid]
      nlinarith

end Run
end
end InexactRealizations.Accuracy.Execution
