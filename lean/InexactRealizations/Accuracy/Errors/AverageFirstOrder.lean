import InexactRealizations.Accuracy.Errors.FirstOrder

/-! The two average-error channels combined in the exact identity. -/
namespace InexactRealizations.Accuracy.Execution.Run
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Roundoff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO M : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

set_option maxHeartbeats 1000000 in
theorem average_noise_first_order (v : Run p H initial target uO) (hc : v.Compensated) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : InexactRealizations.Analysis.Admissible I H) (s : ℕ) (hs2 : 2 ≤ s) (hs : s + 2 < N) :
    ‖averageNoise H v.localErrors s‖ ≤ u * I.L *
      (9 * phi I N s * nominalDistance I N H initial target s + ‖initial - target‖ / mass I N (s + 2)) +
      (u + uO) ^ 2 * I.L * (gradientRemainder I.kappa N + averageRemainder I.kappa N) * M := by
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hHnorm := InexactRealizations.Analysis.hessian_action_bound I H hH
  have ha := v.average_error_reference hc hN hu hu2 huO huO1 hM hinitial htarget hHnorm s hs2 hs
  have hg := v.gradient_error_reference hN hu hu2 huO huO1 hM hinitial htarget hHnorm s hs2 hs
  have hl := gradient_leading_bound (initial := initial) (target := target) hN hH s hs2 hs
  have hg' := hg.trans (add_le_add (mul_le_mul_of_nonneg_left hl hu) le_rfl)
  have hn : ‖averageNoise H v.localErrors s‖ ≤ ‖v.localErrors.gradient s‖ + I.L * ‖v.localErrors.average s‖ := by
    unfold averageNoise combinedAverageError
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (hHnorm _))
  nlinarith [mul_le_mul_of_nonneg_left ha hL]

set_option maxHeartbeats 1000000 in
theorem uncompensated_noise_first_order (v : Run p H initial target uO) (hc : v.Uncompensated) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : InexactRealizations.Analysis.Admissible I H) (s : ℕ) (hs2 : 2 ≤ s) (hs : s + 2 < N) :
    ‖averageNoise H v.localErrors s‖ ≤ u * I.L * ‖target‖ + u * I.L *
      (6 * phi I N s * nominalDistance I N H initial target s + 2 * (‖initial - target‖ / mass I N (s + 2))) +
      (u + uO) ^ 2 * I.L * (gradientRemainder I.kappa N + uncompensatedRemainder I.kappa N) * M := by
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hHnorm := InexactRealizations.Analysis.hessian_action_bound I H hH
  have ha := v.uncompensated_error_reference hc hN hu hu2 huO huO1 hM hinitial htarget hHnorm s hs2 hs
  have hg := v.gradient_error_reference hN hu hu2 huO huO1 hM hinitial htarget hHnorm s hs2 hs
  have hla := average_leading_bound (initial := initial) (target := target) hN hH s hs2 hs
  have hlg := gradient_leading_bound (initial := initial) (target := target) hN hH s hs2 hs
  have ha' := ha.trans (add_le_add (mul_le_mul_of_nonneg_left hla hu) le_rfl)
  have hg' := hg.trans (add_le_add (mul_le_mul_of_nonneg_left hlg hu) le_rfl)
  have hn : ‖averageNoise H v.localErrors s‖ ≤ ‖v.localErrors.gradient s‖ + I.L * ‖v.localErrors.average s‖ := by
    unfold averageNoise combinedAverageError
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (hHnorm _))
  nlinarith [mul_le_mul_of_nonneg_left ha' hL]

omit [FiniteDimensional ℝ E] in
theorem startup_average_noise (v : Run p H initial target uO) (s : ℕ) (hs2 : s < 2) (hs : s + 2 < N) :
    averageNoise H v.localErrors s = 0 := by
  simp only [averageNoise, combinedAverageError, v.startup_gradient_error s hs hs2,
    v.startup_average_error s hs hs2, map_zero, sub_zero]

set_option maxHeartbeats 1000000 in
theorem prefix_error_first_order (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : InexactRealizations.Analysis.Admissible I H) (s : ℕ) (hs : s < N) :
    ‖v.localErrors.state (s + 1)‖ ≤ 8 * u * ‖target‖ +
      u * ‖initial - target‖ * prefixInitialCoefficient I s +
      (u + uO) ^ 2 * prefixRemainder I.kappa N * M := by
  have hh := v.prefix_error_reference hN hu hu2 huO huO1 hM hinitial htarget
    (InexactRealizations.Analysis.hessian_action_bound I H hH) s hs
  have hb := prefix_leading_bound (initial := initial) (target := target) hN hH s hs
  have h := hh.trans (add_le_add (mul_le_mul_of_nonneg_left hb hu) le_rfl)
  convert h using 1
  ring

end
end InexactRealizations.Accuracy.Execution.Run
