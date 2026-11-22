import InexactRealizations.Accuracy.Estimates.Leading

/-! The actual-query oracle assumption gives its nominal first-order
bound, with an explicit uniform quadratic remainder. 
-/
namespace InexactRealizations.Accuracy.Execution.Run
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO M : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

set_option maxHeartbeats 1000000 in
theorem oracle_error_reference (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : InexactRealizations.Analysis.Admissible I H) (s : ℕ) (hs : s < N) :
    ‖v.localErrors.oracle s‖ ≤
      uO * I.L * (2 * ‖target‖ + ‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s) +
      (u + uO) ^ 2 * I.L * queryEnvelope I.kappa N * M := by
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hQ := (envelopes_nonneg I N).1
  have hdelta : 0 ≤ u + uO := add_nonneg hu huO
  have hclose := v.global_query_close hN hu hu2 huO huO1 hM hinitial htarget
    (InexactRealizations.Analysis.hessian_action_bound I H hH) s hs
  have hq := norm_from_distance hclose
  have hnom := nominal_query_size (initial := initial) (target := target) hN hH s hs
  have ht := InexactRealizations.Analysis.hessian_action_bound I H hH target
  have hn := (v.stages ⟨s, hs⟩).noise_bound
  have hn' : ‖v.localErrors.oracle s‖ ≤ uO * (I.L * ‖v.query s‖ + ‖H target‖) := by
    simpa only [localErrors, noise, query, hs, dite_true, Stage.query] using hn
  have hsq : uO * (u + uO) ≤ (u + uO) ^ 2 := by nlinarith [mul_nonneg hu hdelta]
  have hq' : I.L * ‖v.query s‖ + ‖H target‖ ≤
      I.L * (2 * ‖target‖ + ‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s) +
        (u + uO) * I.L * queryEnvelope I.kappa N * M := by
    nlinarith [mul_le_mul_of_nonneg_left (hq.trans (add_le_add hnom le_rfl)) hL]
  have hb := hn'.trans (mul_le_mul_of_nonneg_left hq' huO)
  nlinarith [mul_le_mul_of_nonneg_right hsq (show 0 ≤ I.L * queryEnvelope I.kappa N * M by positivity)]

end
end InexactRealizations.Accuracy.Execution.Run
