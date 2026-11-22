import InexactRealizations.Prose.TailFactors

/-! The tail readout is the arithmetic mean of the actual iterates from
ceil(N/2) through N on one oracle trajectory. 
-/
namespace InexactRealizations.Prose.Tail
noncomputable section
open scoped BigOperators
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem readout_output (h : InexactRealizations.History N) (j : Fin (N + 1))
    (initial : E) (oracle : Fin N → E → E) :
    (readout h j).oracleOutput initial oracle =
      if hj : j.val < N then h.oracleQuery initial oracle ⟨j.val, hj⟩
      else h.oracleOutput initial oracle := by
  unfold InexactRealizations.History.oracleOutput
  rw [same_answers h (readout h j) rfl]
  by_cases hj : j.val < N
  · simp only [hj, dite_true, readout, InexactRealizations.History.oracleQuery]
  · simp only [hj, dite_false, readout]

theorem actual_tail_mean (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (initial : E) (oracle : Fin N → E → E) :
    (history I N).oracleOutput initial oracle =
      ((indices N).card : ℝ)⁻¹ • ∑ j ∈ indices N,
        if hj : j.val < N then (InexactRealizations.Classical.history I N).oracleQuery initial oracle ⟨j.val, hj⟩
        else (InexactRealizations.Classical.history I N).oracleOutput initial oracle := by
  rw [history, average_output _ _ (weights_sum N)]
  simp_rw [readout_output]
  simp only [weights, ite_smul, zero_smul, ← Finset.sum_filter, Finset.smul_sum]
  congr 1
  ext j
  simp

end
end InexactRealizations.Prose.Tail
