import InexactRealizations.Accuracy.Errors.Oracle
import InexactRealizations.Accuracy.Estimates.PrefixLeading

/-! Local bounds in the variables. Startup uses copies;
all remainders are derived from the rounded execution. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Roundoff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def activeDistance (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E)
    (initial target : E) (s : ℕ) : ℝ :=
  if s < 2 then 0 else nominalDistance I N H initial target s

omit [FiniteDimensional ℝ E] in
theorem activeDistance_nonneg (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E)
    (initial target : E) (s : ℕ) : 0 ≤ activeDistance I N H initial target s := by
  unfold activeDistance nominalDistance
  split_ifs <;> positivity

namespace Run
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO M : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

set_option maxHeartbeats 1000000 in
theorem query_error_first_order (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : InexactRealizations.Analysis.Admissible I H) (s : ℕ) (hs : s < N) :
    ‖v.localErrors.query s‖ ≤ u * (2 * ‖target‖ +
      2 * (‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s) +
      3 * theta I N s * activeDistance I N H initial target s) +
      (u + uO) ^ 2 * queryRemainder I.kappa N * M := by
  have hz := (InexactRealizations.Balanced.normalizer_pos I hN hs).le
  have ht := (theta_unit I hN hs).1.le
  have hd := activeDistance_nonneg I N H initial target s
  have hR := (remainders_nonneg I N).1
  by_cases hsmall : s < 2
  · rw [v.startup_query_error s hs hsmall, norm_zero]
    positivity
  · have hraw := v.query_error_reference hN hu hu2 huO huO1 hM hinitial htarget
      (InexactRealizations.Analysis.hessian_action_bound I H hH) s hs (by omega)
    have hlead := query_leading_bound (initial := initial) (target := target) hN hH s (by omega) hs
    have hbound : nominalQueryLeading I N H initial target s ≤
        2 * ‖target‖ + 2 * (‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s) +
          3 * theta I N s * activeDistance I N H initial target s := by
      simp only [activeDistance, hsmall, ite_false, mul_div_assoc] at *
      nlinarith [mul_nonneg ht (norm_nonneg target)]
    exact hraw.trans (add_le_add (mul_le_mul_of_nonneg_left hbound hu) le_rfl)

set_option maxHeartbeats 1000000 in
theorem recovery_error_first_order (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : InexactRealizations.Analysis.Admissible I H) (s : ℕ) (hs : s < N) :
    theta I N s * ‖v.localErrors.recovery s‖ ≤ u * I.L *
      (3 * theta I N s * activeDistance I N H initial target s +
        ‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s) +
      (u + uO) ^ 2 * I.L * recoveryRemainder I.kappa N * M := by
  have hz := InexactRealizations.Balanced.normalizer_pos I hN hs
  have ht := theta_unit I hN hs
  have ht0 := ht.1.le
  have hden := (I.den_pos s).le
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hd := activeDistance_nonneg I N H initial target s
  have hR := (remainders_nonneg I N).2.1
  by_cases hsmall : s < 2
  · rw [v.startup_recovery_error s hs hsmall, norm_zero, mul_zero]
    positivity
  · have hraw := v.recovery_error_reference hN hu hu2 huO huO1 hM hinitial htarget
      (InexactRealizations.Analysis.hessian_action_bound I H hH) s hs (by omega)
    have hlead := recovery_leading_bound (initial := initial) (target := target) hN hH s (by omega) hs
    have hc : ‖initial - target‖ / I.den s ≤ ‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s :=
      div_le_div_of_nonneg_left (norm_nonneg _) hz (normalizer_le_den I hN hs)
    have htheta : theta I N s * (‖initial - target‖ / I.den s) ≤
        ‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s := by
      have hh := mul_le_mul_of_nonneg_right ht.2 (show 0 ≤ ‖initial - target‖ / I.den s by positivity)
      nlinarith
    have hbound : nominalRecoveryLeading I N H initial target s ≤ I.L *
        (3 * theta I N s * activeDistance I N H initial target s +
          ‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s) := by
      simp only [activeDistance, hsmall, ite_false]
      nlinarith [mul_le_mul_of_nonneg_left htheta hL]
    have hh := hraw.trans (add_le_add (mul_le_mul_of_nonneg_left hbound hu) le_rfl)
    convert hh using 1
    ring

set_option maxHeartbeats 1000000 in
theorem hat_error_first_order (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : InexactRealizations.Analysis.Admissible I H) (s : ℕ) (hs : s < N) :
    ‖hatNoise I N H v.localErrors s‖ ≤ (u + uO) * I.L *
      (2 * ‖target‖ + 3 * (‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s) +
        6 * theta I N s * activeDistance I N H initial target s) +
      (u + uO) ^ 2 * I.L *
        (queryEnvelope I.kappa N + queryRemainder I.kappa N + recoveryRemainder I.kappa N) * M := by
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have ht := (theta_unit I hN hs).1.le
  have hz := (InexactRealizations.Balanced.normalizer_pos I hN hs).le
  have hd := activeDistance_nonneg I N H initial target s
  have hw := v.oracle_error_reference hN hu hu2 huO huO1 hM hinitial htarget hH s hs
  have hq := mul_le_mul_of_nonneg_left
    (v.query_error_first_order hN hu hu2 huO huO1 hM hinitial htarget hH s hs) hL
  have hg := v.recovery_error_first_order hN hu hu2 huO huO1 hM hinitial htarget hH s hs
  have hHq := InexactRealizations.Analysis.hessian_action_bound I H hH (v.localErrors.query s)
  have hn : ‖hatNoise I N H v.localErrors s‖ ≤
      ‖v.localErrors.oracle s‖ + I.L * ‖v.localErrors.query s‖ + theta I N s * ‖v.localErrors.recovery s‖ := by
    unfold hatNoise combinedOracleError
    have hh := norm_add_le (v.localErrors.oracle s + H (v.localErrors.query s))
      (theta I N s • v.localErrors.recovery s)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hh
    linarith [norm_add_le (v.localErrors.oracle s) (H (v.localErrors.query s))]
  nlinarith [mul_nonneg huO (show 0 ≤ I.L * (‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s) by positivity),
    mul_nonneg huO (show 0 ≤ I.L * theta I N s * activeDistance I N H initial target s by positivity)]

end Run
end
end InexactRealizations.Accuracy.Execution
