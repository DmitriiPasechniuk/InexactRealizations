import InexactRealizations.Accuracy.Execution.Run

/-! Pointwise access to the actual stage outputs. -/
namespace InexactRealizations.Accuracy.Execution.Run
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

theorem answer_at (v : Run p H initial target uO) (s : Fin N) : v.answer s.val = (v.stages s).answer := by
  simp only [answer, s.isLt, dite_true]

theorem recovered_at (v : Run p H initial target uO) (s : Fin N) : v.recovered s.val = (v.stages s).recovered := by
  simp only [recovered, s.isLt, dite_true]

theorem state_at (v : Run p H initial target uO) (s : Fin N) :
    v.x (s.val + 1) = (v.stages s).prefixOperations.result := by
  unfold x
  rw [v.step_eq s]
  rfl

theorem average_at (v : Run p H initial target uO) (s : Fin N) :
    v.average s.val = (v.stages s).nextAverage + (v.stages s).nextCorrection := by
  unfold average
  rw [v.step_eq s]
  rfl

theorem gradient_at (v : Run p H initial target uO) (s : Fin N) :
    v.gradient s.val = (v.stages s).nextGradient := by
  unfold gradient
  rw [v.step_eq s]
  rfl

end
end InexactRealizations.Accuracy.Execution.Run
