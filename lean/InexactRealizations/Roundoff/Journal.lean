import InexactRealizations.Roundoff.Identity

/-! Current journal: `exact_local_error_identity` is the
terminal formula for the printed local execution equations; the theorem
below collects all of its spectral peak and normalization clauses.
The paper's M_s is `Algorithms.AveragedBalanced.mass I N (s + 2)`.
No norm or spectral assumption is needed for the algebraic terminal identity. 
-/
namespace InexactRealizations.Roundoff
noncomputable section
open scoped BigOperators
open InexactRealizations.Algorithms.AveragedBalanced

theorem journal_response_peaks (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    (∀ (s : Fin N) (lam : ℝ), lam ∈ Set.Icc I.mu I.L →
      |((InexactRealizations.Balanced.history I N hN).response s).eval lam| ≤
        |((InexactRealizations.Balanced.history I N hN).response s).eval I.mu|) ∧
    (∀ (s : Fin N) (lam : ℝ), lam ∈ Set.Icc I.mu I.L →
      |((InexactRealizations.Classical.history I N).response s).eval lam| ≤
        |((InexactRealizations.Classical.history I N).response s).eval I.mu|) ∧
    (∀ (s : Fin (N - 2)) (lam : ℝ), lam ∈ Set.Icc I.mu I.L →
      |(averageResponse I N s.val).eval lam| ≤ (averageResponse I N s.val).eval I.mu) ∧
    (∑ s : Fin N, |((InexactRealizations.Balanced.history I N hN).response s).eval I.mu|) =
      InexactRealizations.Lower.additiveScale I N ∧
    (∀ s : Fin N, |(alpha I s.val)⁻¹ * ((InexactRealizations.Classical.history I N).response s).eval I.mu| =
      ((N : ℝ) - s.val) * I.den (s.val + 1) / I.den N) ∧
    (∀ s : Fin (N - 2), (averageResponse I N s.val).eval I.mu =
      4 * mass I N (s.val + 2) * (((N - 1 - s.val) ^ 2 / 4 : ℕ) : ℝ) /
        (I.delta * InexactRealizations.Balanced.omega N (s.val + 2) * I.den N)) := by
  refine ⟨?_, ?_, ?_, balanced_response_abs_sum I N hN, ?_, ?_⟩
  · intro s lam hlam
    rw [InexactRealizations.Balanced.response_endpoint, abs_neg,
      abs_of_pos (InexactRealizations.Balanced.responseBound_pos I hN s.isLt)]
    exact InexactRealizations.Balanced.response_bound I N hN s hlam
  · intro s lam hlam
    rw [InexactRealizations.Classical.response_endpoint I N (by omega), abs_neg,
      abs_of_pos (InexactRealizations.Classical.responseBound_pos I s)]
    exact InexactRealizations.Classical.response_bound I N (by omega) s hlam
  · intro s lam hlam
    exact averageResponse_peak I hN (by have := s.isLt; omega) hlam
  · exact prefix_state_response_endpoint I N (by omega)
  · intro s
    rw [averageResponse_endpoint, averageScale]
    ring

end
end InexactRealizations.Roundoff
