import InexactRealizations.Roundoff.Journal

/-! Linear transport of the printed local equations and their zero-error
fixed point. Used to take constant coefficients of polynomial executions. 
-/
namespace InexactRealizations.Roundoff
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
variable {E V : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]

def LocalErrorStreams.map (ell : LocalErrorStreams E) (F : E →ₗ[ℝ] V) : LocalErrorStreams V where
  oracle s := F (ell.oracle s)
  query s := F (ell.query s)
  recovery s := F (ell.recovery s)
  average s := F (ell.average s)
  gradient s := F (ell.gradient s)
  state s := F (ell.state s)

theorem map_earlierAverage (F : E →ₗ[ℝ] V) (f : ℕ → E) (s : ℕ) :
    F (earlierAverage f s) = earlierAverage (fun j ↦ F (f j)) s := by
  by_cases hs : s < 2 <;> simp only [earlierAverage, hs, ite_true, ite_false, map_zero]

def LocalExecution.map {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ}
    {H : E →ₗ[ℝ] E} {initial target : E} {ell : LocalErrorStreams E}
    (u : LocalExecution I N H initial target ell) (F : E →ₗ[ℝ] V) (K : V →ₗ[ℝ] V)
    (hcommute : ∀ v, F (H v) = K (F v)) :
    LocalExecution I N K (F initial) (F target) (ell.map F) where
  x s := F (u.x s)
  y s := F (u.y s)
  g s := F (u.g s)
  recovered s := F (u.recovered s)
  average s := F (u.average s)
  gradient s := F (u.gradient s)
  initial_eq := congrArg F u.initial_eq
  query_eq s hs := by
    have hh := congrArg F (u.query_eq s hs)
    simpa only [computedQuery, map_add, map_sub, map_smul, map_earlierAverage, LocalErrorStreams.map] using hh
  answer_eq s hs := by
    have hh := congrArg F (u.answer_eq s hs)
    simpa only [computedAnswer, map_add, map_sub, hcommute, LocalErrorStreams.map] using hh
  recovered_eq s hs := by
    have hh := congrArg F (u.recovered_eq s hs)
    simpa only [recoveredGradient, map_add, map_sub, map_smul, map_earlierAverage, LocalErrorStreams.map] using hh
  average_eq s hs := by
    have hh := congrArg F (u.average_eq s hs)
    simpa only [updatedAverage, map_add, map_sub, map_smul, map_earlierAverage, LocalErrorStreams.map] using hh
  gradient_eq s hs := by
    have hh := congrArg F (u.gradient_eq s hs)
    simpa only [updatedAverage, map_add, map_sub, map_smul, map_earlierAverage, LocalErrorStreams.map] using hh
  state_eq s hs := by
    have hh := congrArg F (u.state_eq s hs)
    simpa only [map_add, map_sub, map_smul, LocalErrorStreams.map] using hh

def zeroErrors (E : Type*) [Zero E] : LocalErrorStreams E where
  oracle _ := 0
  query _ := 0
  recovery _ := 0
  average _ := 0
  gradient _ := 0
  state _ := 0

theorem recoveredError_zero (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    recoveredError I N (0 : ℕ → E) 0 s = 0 := by
  simp only [recoveredError, Pi.zero_apply, averageError_zero, smul_zero, sub_zero, ite_self]

namespace LocalExecution
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {H : E →ₗ[ℝ] E} {target : E}

theorem zero_error_state (u : LocalExecution I N H target target (zeroErrors E))
    (hN : 2 ≤ N) (s : ℕ) (hs : s ≤ N) : u.x s = target := by
  have hr (j : ℕ) (hj : j < N) : u.recovered j = H (u.x j - target) := by
    have hh := u.recovered_error hN j hj
    have hw : hatNoise I N H (zeroErrors E) = 0 := by
      funext i
      simp [hatNoise, combinedOracleError, zeroErrors]
    have hi : averageNoise H (zeroErrors E) = 0 := by
      funext i
      simp [averageNoise, combinedAverageError, zeroErrors]
    rw [hw, hi, recoveredError_zero] at hh
    exact sub_eq_zero.mp hh
  induction s using Nat.strong_induction_on with
  | h s ih =>
    cases s with
    | zero => exact u.initial_eq
    | succ s =>
      rw [u.state_eq s (by omega), hr s (by omega), ih s (by omega) (by omega),
        ih (s - 1) (by omega) (by omega)]
      simp only [sub_self, map_zero, smul_zero, zeroErrors, add_zero, sub_zero]
      module

theorem zero_error_average (u : LocalExecution I N H target target (zeroErrors E))
    (hN : 2 ≤ N) (s : ℕ) (hs : s + 2 < N) : u.average s = target := by
  induction s using Nat.twoStepInduction with
  | zero =>
    rw [u.average_eq 0 hs, zero_error_state u hN 0 (by omega)]
    simp [updatedAverage, earlierAverage, phi, zeroErrors]
  | one =>
    rw [u.average_eq 1 hs, zero_error_state u hN 1 (by omega)]
    simp [updatedAverage, earlierAverage, phi, zeroErrors]
  | more s ih _ =>
    rw [u.average_eq (s + 2) hs, zero_error_state u hN (s + 2) (by omega)]
    simp only [updatedAverage, earlierAverage, show ¬s + 2 < 2 by omega, ite_false, Nat.add_sub_cancel,
      ih (by omega), sub_self, smul_zero, zeroErrors, add_zero]

theorem zero_error_average_of_eq {ell : LocalErrorStreams E}
    (u : LocalExecution I N H target target ell) (hell : ell = zeroErrors E)
    (hN : 2 ≤ N) (s : ℕ) (hs : s + 2 < N) : u.average s = target := by
  subst ell
  exact u.zero_error_average hN s hs

theorem zero_error_state_of_eq {ell : LocalErrorStreams E}
    (u : LocalExecution I N H target target ell) (hell : ell = zeroErrors E)
    (hN : 2 ≤ N) (s : ℕ) (hs : s ≤ N) : u.x s = target := by
  subst ell
  exact u.zero_error_state hN s hs

end LocalExecution
end
end InexactRealizations.Roundoff
