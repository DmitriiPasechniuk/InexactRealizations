import InexactRealizations.Comparisons.Classical.Bounds
import InexactRealizations.Risk.EndpointAttainment

namespace InexactRealizations.Classical
noncomputable section
open scoped BigOperators

/-- The true temporal energy of the classical physical impulse responses. -/
def variance (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : ℝ :=
  ∑ s : Fin N, responseBound I N s ^ 2

/-- The manuscript's exact finite variance formula. -/
theorem variance_exact (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0<N) :
    variance I N = (16*I.epsilon N^2/I.delta^2) *
      ((N:ℝ)^2/4+∑ s ∈ Finset.Ico 1 N, ((N:ℝ)-s)^2*I.den s^2) := by
  let f : ℕ → ℝ := fun s => (initialWeight s*I.den s*((N:ℝ)-s))^2
  have he : variance I N = (16*I.epsilon N^2/I.delta^2)*∑ s ∈ Finset.range N, f s := by
    unfold variance
    change (∑ s : Fin N, (fun s : ℕ => responseBound I N s^2) s.val)=_
    rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => responseBound I N s^2) N, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    dsimp [responseBound, f]
    ring
  rw [he]
  congr 1
  have hsplit := Finset.sum_range_add_sum_Ico f (show 1≤N by omega)
  rw [Finset.sum_range_one] at hsplit
  rw [← hsplit]
  congr 1
  · simp [f, initialWeight, InexactRealizations.Operators.SpectralInterval.den]
    ring
  · apply Finset.sum_congr rfl
    intro s hs
    have hs0 : s≠0 := by have := (Finset.mem_Ico.mp hs).1; omega
    simp only [f, initialWeight, hs0, ite_false, one_mul]
    ring

/-- The exact worst-case MSE of the actual classical recurrence. -/
theorem mseRisk_eq (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0<N)
    (r σ : ℝ) (hr : 0≤r) : Risk.mseRisk (history I N) I r σ =
      I.epsilon N^2*r^2+σ^2*variance I N := by
  apply Risk.mseRisk_eq_of_endpoint_bounds _ I (history_exact I N) hN _
    (responseBounds I N hN)
  intro s
  rw [response_endpoint I N hN, abs_neg, abs_of_pos (responseBound_pos I s)]
  exact hr

end
end InexactRealizations.Classical
