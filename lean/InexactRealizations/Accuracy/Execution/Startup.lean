import InexactRealizations.Accuracy.Execution.Correction

/-! The first two calls copy the query, recovered gradient and stored
averages, exactly. No fictitious rounding operation is
introduced at startup. 
-/
namespace InexactRealizations.Accuracy.Execution.Run
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Roundoff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

theorem startup_query (v : Run p H initial target uO) (s : ℕ) (hs : s < N) (hs2 : s < 2) :
    v.query s = v.x s := by
  simp only [query, hs, dite_true, Stage.query, observedQuery, hs2, x]

theorem startup_recovered (v : Run p H initial target uO) (s : ℕ) (hs : s < N) (hs2 : s < 2) :
    v.recovered s = v.answer s := by
  simp only [recovered, answer, hs, dite_true, Stage.recovered, observedRecovered, hs2]

theorem startup_query_error (v : Run p H initial target uO) (s : ℕ) (hs : s < N) (hs2 : s < 2) :
    v.localErrors.query s = 0 := by
  simp only [localErrors, startup_query v s hs hs2, earlierAverage, theta, hs2, ite_true,
    sub_zero, one_smul, zero_add, sub_self]

theorem startup_recovery_error (v : Run p H initial target uO) (s : ℕ) (hs : s < N) (hs2 : s < 2) :
    v.localErrors.recovery s = 0 := by
  simp only [localErrors, startup_recovered v s hs hs2, earlierAverage, theta, hs2, ite_true,
    sub_zero, inv_one, one_smul, zero_add, sub_self]

theorem startup_average (v : Run p H initial target uO) (s : ℕ) (hs : s + 2 < N) (hs2 : s < 2) :
    v.average s = v.x s := by
  unfold average
  rw [v.step_eq ⟨s, by omega⟩]
  simp [Stage.output, Stage.nextAverage, Stage.nextCorrection, hs, hs2, x]

theorem startup_gradient (v : Run p H initial target uO) (s : ℕ) (hs : s + 2 < N) (hs2 : s < 2) :
    v.gradient s = v.recovered s := by
  unfold gradient
  rw [v.step_eq ⟨s, by omega⟩]
  simp [Stage.output, Stage.nextGradient, hs, hs2, recovered, show s < N by omega,
    Stage.recovered, observedRecovered]

theorem startup_average_error (v : Run p H initial target uO) (s : ℕ) (hs : s + 2 < N) (hs2 : s < 2) :
    v.localErrors.average s = 0 := by
  simp only [localErrors, startup_average v s hs hs2, earlierAverage, phi, hs2, ite_true,
    sub_zero, one_smul, zero_add, sub_self]

theorem startup_gradient_error (v : Run p H initial target uO) (s : ℕ) (hs : s + 2 < N) (hs2 : s < 2) :
    v.localErrors.gradient s = 0 := by
  simp only [localErrors, startup_gradient v s hs hs2, earlierAverage, phi, hs2, ite_true,
    sub_zero, one_smul, zero_add, sub_self]

end
end InexactRealizations.Accuracy.Execution.Run
