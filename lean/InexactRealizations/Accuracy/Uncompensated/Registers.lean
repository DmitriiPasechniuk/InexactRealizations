import InexactRealizations.Accuracy.Uncompensated.Componentwise

/-! Selecting the uncorrected instruction makes both correction registers
identically zero, as required by the printed variant. 
-/
namespace InexactRealizations.Accuracy.Execution.Run
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem uncompensated_corrections_zero {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ} {p : Prepared I N u}
    {H : E →ₗ[ℝ] E} {initial target : E} (v : Run p H initial target uO)
    (hc : v.Uncompensated) (n : ℕ) (hn : n ≤ N) : v.states n 4 = 0 ∧ v.states n 5 = 0 := by
  induction n with
  | zero => rw [v.initial_eq]; constructor <;> rfl
  | succ n ih =>
    have hprev := ih (by omega : n ≤ N)
    have hs : n < N := by omega
    let a := v.stages ⟨n, hs⟩
    have hnext : a.nextCorrection = 0 := by
      unfold Stage.nextCorrection
      split_ifs with hv hsmall
      · rfl
      · dsimp only [a] at hsmall hv ⊢
        rcases hc ⟨n, hs⟩ (show 2 ≤ n by omega) hv with ⟨op, hop⟩
        rw [hop]
      · exact hprev.2
    rw [v.step_eq ⟨n, hs⟩]
    change a.nextCorrection = 0 ∧ v.states n 4 = 0
    exact ⟨hnext, hprev.1⟩

end
end InexactRealizations.Accuracy.Execution.Run
