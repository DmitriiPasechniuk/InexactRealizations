import InexactRealizations.Accuracy.Execution.Nominal

/-! Exact affine-gradient identities for the nominal execution. -/
namespace InexactRealizations.Accuracy.Execution.Nominal
noncomputable section
open InexactRealizations.Roundoff InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E) (initial target : E)

theorem recovered_gradient (hN : 2 ≤ N) (s : ℕ) (hs : s < N) :
    recovered I N H initial target s = H (x I N H initial target s - target) := by
  let v := execution I N H initial target
  have hw : hatNoise I N H (zeroErrors E) = 0 := by funext j; simp [hatNoise, combinedOracleError, zeroErrors]
  have hi : averageNoise H (zeroErrors E) = 0 := by funext j; simp [averageNoise, combinedAverageError, zeroErrors]
  have hh := v.recovered_error hN s hs
  rw [hw, hi, recoveredError_zero] at hh
  exact sub_eq_zero.mp hh

theorem gradient_identity (hN : 2 ≤ N) (s : ℕ) (hs : s + 2 < N) :
    gradient I N H initial target s = H (average I N H initial target s - target) := by
  let v := execution I N H initial target
  have hw : hatNoise I N H (zeroErrors E) = 0 := by funext j; simp [hatNoise, combinedOracleError, zeroErrors]
  have hi : averageNoise H (zeroErrors E) = 0 := by funext j; simp [averageNoise, combinedAverageError, zeroErrors]
  have hh := (errorSystem_unique I hN _ _ v.hat v.bar (v.error_system hN) s (by omega)).2 hs
  rw [hw, hi, averageError_zero] at hh
  exact sub_eq_zero.mp hh

theorem prior_gradient (hN : 2 ≤ N) (s : ℕ) (hs : 2 ≤ s) (hsN : s < N) :
    nominalStates I N H initial target s 7 =
      H (representedAverage (nominalStates I N H initial target s) - target) := by
  have hg := earlier_gradient I N H initial target s hs
  have ha := earlier_average I N H initial target s hs
  simp only [earlierAverage, show ¬s < 2 by omega, ite_false] at hg ha
  rw [← hg, gradient_identity I N H initial target hN (s - 2) (by omega), ha]

theorem oracle_gradient_difference (hN : 2 ≤ N) (s : ℕ) (hs : 2 ≤ s) (hsN : s < N) :
    answer I N H initial target s - nominalStates I N H initial target s 7 =
      theta I N s • H (x I N H initial target s - representedAverage (nominalStates I N H initial target s)) := by
  rw [prior_gradient I N H initial target hN s hs hsN]
  simp only [answer, exactAnswer, exactQuery, show ¬s < 2 by omega, ite_false, x,
    map_add, map_sub, map_smul]
  module

theorem recovered_prior_difference (hN : 2 ≤ N) (s : ℕ) (hs : 2 ≤ s) (hsN : s < N) :
    recovered I N H initial target s - nominalStates I N H initial target s 7 =
      H (x I N H initial target s - representedAverage (nominalStates I N H initial target s)) := by
  rw [recovered_gradient I N H initial target hN s hsN, prior_gradient I N H initial target hN s hs hsN]
  simp only [map_sub]
  abel

theorem gradient_update_identity (hN : 2 ≤ N) (s : ℕ) (hs : 2 ≤ s) (hsN : s + 2 < N) :
    nominalStates I N H initial target s 7 + phi I N s •
      (recovered I N H initial target s - nominalStates I N H initial target s 7) =
        H (average I N H initial target s - target) := by
  have hh := (execution I N H initial target).gradient_eq s hsN
  change gradient I N H initial target s = updatedAverage (phi I N s)
    (earlierAverage (gradient I N H initial target) s) (recovered I N H initial target s) 0 at hh
  rw [earlier_gradient I N H initial target s hs] at hh
  simp only [updatedAverage, add_zero] at hh
  rw [← hh, gradient_identity I N H initial target hN s hsN]

theorem prefix_update (s : ℕ) :
    (1 + beta I s) • x I N H initial target s - beta I s • nominalStates I N H initial target s 1 -
      alpha I s • recovered I N H initial target s = x I N H initial target (s + 1) := rfl

end
end InexactRealizations.Accuracy.Execution.Nominal
