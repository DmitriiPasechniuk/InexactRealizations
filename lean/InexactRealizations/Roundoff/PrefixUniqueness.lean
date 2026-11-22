import InexactRealizations.Roundoff.PrefixExecution

/-! Uniqueness of the actual forced Prefix recurrence, including startup. -/
namespace InexactRealizations.Roundoff
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem prefixPair_unique (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E)
    (initial : E) (e x : ℕ → E) (h0 : x 0 = initial)
    (hstep : ∀ s : Fin N, x (s.val + 1) = (1 + beta I s.val) • x s.val -
      beta I s.val • x (s.val - 1) - alpha I s.val • (H (x s.val) + e s.val))
    (n : ℕ) (hn : n ≤ N) :
    (prefixPair I H initial e n).1 = x n ∧ (prefixPair I H initial e n).2 = x (n - 1) := by
  induction n with
  | zero => simpa only [prefixPair, Nat.zero_sub] using And.intro h0.symm h0.symm
  | succ n ih =>
    have hi := ih (by omega)
    simp only [prefixPair, hi.1, hi.2]
    exact ⟨(hstep ⟨n, by omega⟩).symm, by rw [Nat.add_sub_cancel]⟩

end
end InexactRealizations.Roundoff
