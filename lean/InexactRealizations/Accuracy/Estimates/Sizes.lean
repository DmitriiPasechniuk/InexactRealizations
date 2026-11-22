import InexactRealizations.Accuracy.Estimates.Omega
import InexactRealizations.Accuracy.Estimates.Nominal
import InexactRealizations.Analysis.Spectral

/-! The dimension-independent noiseless sizes in the proof. -/
namespace InexactRealizations.Accuracy
noncomputable section
open Polynomial
open InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Roundoff

theorem mass_lower (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : 1 ≤ s) (hsN : s + 2 < N) :
    2 / ((N : ℝ) + 1) * I.den s ≤ mass I N (s + 2) := by
  have hm := mass_nonneg I hN (by omega : s < N)
  have hd := mul_le_mul_of_nonneg_right (omega_drop_bounds hN hs).1 (I.den_pos s).le
  rw [mass_step]
  linarith

theorem physicalRemainder_eval (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (lam : ℝ) :
    (physicalRemainder I N s).eval lam = (InexactRealizations.Balanced.remainder N s).eval (I.z lam) := by
  have hz : I.eta - 2 / I.delta * lam = I.z lam := by
    unfold InexactRealizations.Operators.SpectralInterval.eta InexactRealizations.Operators.SpectralInterval.z
    ring
  simp only [physicalRemainder, eval_comp, eval_sub, eval_mul, eval_C, eval_X, hz]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {H : E →ₗ[ℝ] E} {initial target : E}

theorem nominal_state_bound (u : LocalExecution I N H initial target (zeroErrors E))
    (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H) (s : ℕ) (hs : s ≤ N) :
    ‖u.x s - target‖ ≤ ‖initial - target‖ / I.den s := by
  rw [nominal_state u hN s hs]
  simpa only [InexactRealizations.Operators.SpectralInterval.epsilon, one_div_mul_eq_div] using
    InexactRealizations.Analysis.residual_action_bound I H hH s (initial - target)

theorem nominal_average_bound_of_pos (u : LocalExecution I N H initial target (zeroErrors E))
    (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H) (s : ℕ) (hsN : s + 2 < N)
    (hm : 0 < mass I N (s + 2)) :
    ‖u.average s - target‖ ≤ ‖initial - target‖ / mass I N (s + 2) := by
  have he : u.average s - target = (mass I N (s + 2))⁻¹ •
      (aeval H (physicalRemainder I N (s + 2))) (initial - target) := by
    rw [← nominal_average_weighted u hN s hsN, smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hm]
  have hp (lam : ℝ) (hlam : lam ∈ Set.Icc I.mu I.L) :
      |(physicalRemainder I N (s + 2)).eval lam| ≤ 1 := by
    rw [physicalRemainder_eval]
    exact (InexactRealizations.Balanced.abs_remainder_eval_le hN hsN (abs_le.mpr (I.z_mem hlam))).trans
      (by linarith [(InexactRealizations.Balanced.omega_pos hN hsN).le])
  have hb := InexactRealizations.Analysis.polynomial_action_bound I H hH (physicalRemainder I N (s + 2)) 1
    zero_le_one hp (initial - target)
  simpa only [one_mul, inv_mul_eq_div] using
    mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hm.le)

theorem nominal_average_bound (u : LocalExecution I N H initial target (zeroErrors E))
    (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H) (s : ℕ) (hs : 1 ≤ s) (hsN : s + 2 < N) :
    ‖u.average s - target‖ ≤ ‖initial - target‖ / mass I N (s + 2) := by
  have hn : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hm : 0 < mass I N (s + 2) :=
    lt_of_lt_of_le (mul_pos (div_pos (by norm_num) hn) (I.den_pos s)) (mass_lower I hN hs hsN)
  exact nominal_average_bound_of_pos u hN hH s hsN hm

omit [FiniteDimensional ℝ E] in
theorem nominal_average_start (u : LocalExecution I N H initial target (zeroErrors E))
    (s : ℕ) (hs : s < 2) (hsN : s + 2 < N) : u.average s = u.x s := by
  rw [u.average_eq s hsN]
  simp only [updatedAverage, phi, hs, ite_true, one_smul, zeroErrors, add_zero]
  abel

theorem nominal_distance_bound (u : LocalExecution I N H initial target (zeroErrors E))
    (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H) (s : ℕ) (hs : 2 ≤ s) (hsN : s < N) :
    ‖u.x s - u.average (s - 2)‖ ≤
      ((N : ℝ) + 3) * ‖initial - target‖ / (2 * I.den (s - 2)) := by
  have hx := nominal_state_bound u hN hH s hsN.le
  have ht : ‖u.x s - u.average (s - 2)‖ ≤ ‖u.x s - target‖ + ‖u.average (s - 2) - target‖ := by
    simpa only [sub_add_sub_cancel, norm_sub_rev target (u.average (s - 2))] using
      norm_add_le (u.x s - target) (target - u.average (s - 2))
  have hc : I.den (s - 2) ≤ I.den s := (den_strictMono I).monotone (by omega)
  have hx' : ‖u.x s - target‖ ≤ ‖initial - target‖ / I.den (s - 2) :=
    hx.trans (div_le_div_of_nonneg_left (norm_nonneg _) (I.den_pos (s - 2)) hc)
  by_cases hs2 : s = 2
  · subst s
    have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast (show 3 ≤ N by omega)
    have ha : u.average 0 = initial := (nominal_average_start u 0 (by omega) (by omega)).trans u.initial_eq
    have ht2 : ‖u.x 2 - u.average 0‖ ≤ ‖u.x 2 - target‖ + ‖initial - target‖ := by
      simpa only [ha] using ht
    simpa only [Nat.sub_self, I.den_zero, mul_one] using
      (show ‖u.x 2 - u.average 0‖ ≤ ((N : ℝ) + 3) * ‖initial - target‖ / 2 by
        have hx0 : ‖u.x 2 - target‖ ≤ ‖initial - target‖ := by simpa using hx'
        nlinarith [norm_nonneg (initial - target)])
  · have hs1 : 1 ≤ s - 2 := by omega
    have hsback : s - 2 + 2 < N := by omega
    have ha := nominal_average_bound u hN hH (s - 2) hs1 hsback
    have hm := mass_lower I hN hs1 hsback
    have hden := I.den_pos (s - 2)
    have hp : 0 < 2 / ((N : ℝ) + 1) * I.den (s - 2) := by positivity
    have havg : ‖u.average (s - 2) - target‖ ≤
        ((N : ℝ) + 1) * ‖initial - target‖ / (2 * I.den (s - 2)) := by
      have hb := ha.trans (div_le_div_of_nonneg_left (norm_nonneg _) hp hm)
      convert hb using 1
      field_simp [I.den_ne (s - 2), (show (0 : ℝ) < (N : ℝ) + 1 by positivity).ne']
    have he : ‖initial - target‖ / I.den (s - 2) +
        ((N : ℝ) + 1) * ‖initial - target‖ / (2 * I.den (s - 2)) =
        ((N : ℝ) + 3) * ‖initial - target‖ / (2 * I.den (s - 2)) := by ring
    rw [← he]
    exact ht.trans (add_le_add hx' havg)

end
end InexactRealizations.Accuracy
