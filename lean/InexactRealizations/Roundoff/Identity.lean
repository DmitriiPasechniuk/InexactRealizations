import InexactRealizations.Roundoff.Execution
import InexactRealizations.Roundoff.ProgramError
import InexactRealizations.Roundoff.AverageResponse
import InexactRealizations.Roundoff.PrefixUniqueness

/-! The complete terminal identity in current, derived from
the printed local execution equations with arbitrary oracle/local errors. 
-/
namespace InexactRealizations.Roundoff
noncomputable section
open Polynomial
open scoped BigOperators
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem combined_filter_response (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (w iota : ℕ → E) :
    (∑ s : Fin N, (aeval H ((InexactRealizations.Classical.history I N).response s)) (recoveredError I N w iota s.val)) =
      (∑ s : Fin N, (aeval H ((InexactRealizations.Balanced.history I N hN).response s)) (w s.val)) +
        ∑ s : Fin (N - 2), (aeval H (averageResponse I N s.val)) (iota s.val) := by
  calc
    _ = ∑ s : Fin N, (aeval H ((InexactRealizations.Classical.history I N).response s))
        (recoveredError I N w 0 s.val + recoveredError I N 0 iota s.val) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [recoveredError_split]
    _ = _ := by
      simp only [map_add, Finset.sum_add_distrib]
      rw [oracle_filter_response I hN, average_filter_response I hN]

theorem LocalExecution.centered_step {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ}
    {H : E →ₗ[ℝ] E} {initial target : E} {ell : LocalErrorStreams E}
    (u : LocalExecution I N H initial target ell) (hN : 2 ≤ N) (s : Fin N) :
    u.x (s.val + 1) - target =
      (1 + beta I s.val) • (u.x s.val - target) - beta I s.val • (u.x (s.val - 1) - target) -
        alpha I s.val • (H (u.x s.val - target) +
          (recoveredError I N (hatNoise I N H ell) (averageNoise H ell) s.val -
            (alpha I s.val)⁻¹ • ell.state (s.val + 1))) := by
  have hr : u.recovered s.val = H (u.x s.val - target) +
      recoveredError I N (hatNoise I N H ell) (averageNoise H ell) s.val := by
    have hh := u.recovered_error hN s.val s.isLt
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  calc
    _ = (1 + beta I s.val) • (u.x s.val - target) - beta I s.val • (u.x (s.val - 1) - target) -
        alpha I s.val • (H (u.x s.val - target) +
          recoveredError I N (hatNoise I N H ell) (averageNoise H ell) s.val) + ell.state (s.val + 1) := by
      rw [u.state_eq s.val s.isLt, hr]
      module
    _ = _ := by
      rw [state_error_as_oracle_error _ _ (alpha_bounds I s.val).1.ne']
      congr 1
      congr 1
      abel

theorem exact_local_error_identity (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (initial target : E) (ell : LocalErrorStreams E)
    (u : LocalExecution I N H initial target ell) :
    u.x N - target = (aeval H (I.residual N)) (initial - target) +
      (∑ s : Fin N, (aeval H ((InexactRealizations.Balanced.history I N hN).response s)) (hatNoise I N H ell s.val)) +
      (∑ s : Fin (N - 2), (aeval H (averageResponse I N s.val)) (averageNoise H ell s.val)) -
      ∑ s : Fin N, (alpha I s.val)⁻¹ •
        (aeval H ((InexactRealizations.Classical.history I N).response s)) (ell.state (s.val + 1)) := by
  let e : ℕ → E := fun s ↦ recoveredError I N (hatNoise I N H ell) (averageNoise H ell) s -
    (alpha I s)⁻¹ • ell.state (s + 1)
  have h0 : u.x 0 - target = initial - target := by rw [u.initial_eq]
  have he := (prefixPair_unique I N H (initial - target) e (fun s ↦ u.x s - target) h0
    (u.centered_step hN) N le_rfl).1
  rw [← he, prefixPair_response]
  simp only [e, map_sub, map_smul]
  rw [Finset.sum_sub_distrib, combined_filter_response I hN]
  abel

end
end InexactRealizations.Roundoff
