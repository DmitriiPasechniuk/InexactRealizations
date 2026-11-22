import InexactRealizations.Accuracy.Bounds.StageRecovery

/-! The actual left-to-right Prefix step versus its exact stage value. -/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO S : ℝ} {p : Prepared I N u}
  {s : Fin N} {v : State E} {H : E →ₗ[ℝ] E} {target : E}

set_option maxHeartbeats 1000000 in
theorem Stage.prefix_size_error (a : Stage p s v H target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hS : 0 ≤ S) (hv : Bounded v I.L S) (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (htarget : ‖target‖ ≤ S) :
    ‖a.prefixOperations.result - exactStep I N s.val v H target 0‖ ≤
      40000000000 * (parameterBound I.kappa N) ^ 2 * (u + uO) * S ∧
    ‖a.prefixOperations.result‖ ≤ 50000000000 * (parameterBound I.kappa N) ^ 2 * S := by
  let A := parameterBound I.kappa N
  have hA : 1 ≤ A := parameterBound_one I N
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hu1 : u ≤ 1 := by linarith
  have hdelta : 0 ≤ (u + uO) * S := by positivity
  have hAu : 0 ≤ u * A ^ 2 * S := by positivity
  have hAO : 0 ≤ uO * A ^ 2 * S := by positivity
  have hx := hv.scalar 0 (by decide)
  have hb := hv.scalar 1 (by decide)
  have halpha := (alpha_bounds I s.val).1.le
  have hbeta := beta_bounds I s.val
  have halphaL : alpha I s.val * I.L ≤ A := alpha_scaled_bound I N s.val
  have hr := a.recovered_size_error hN hu hu2 huO huO1 hS hv hH htarget
  have hr1 : ‖a.recovered - exactRecovered I N s.val v H target‖ ≤ 20000000 * A * (u + uO) * I.L * S := hr.1
  have hr2 : ‖a.recovered‖ ≤ 20000000 * A * I.L * S := hr.2
  have hg : alpha I s.val * ‖a.recovered‖ ≤ 20000000 * A ^ 2 * S := by
    have hh := mul_le_mul_of_nonneg_left hr2 halpha
    have hc := mul_le_mul_of_nonneg_left halphaL (by positivity : 0 ≤ 20000000 * A * S)
    nlinarith
  have hop := a.prefixOperations.coarse hu hu1 halpha hbeta.1 hbeta.2.le
    (p.alpha_error s) (p.beta_error s) hS (by positivity : 0 ≤ 20000000 * A ^ 2 * S) hx hb hg
  let q := (1 + beta I s.val) • v 0 - beta I s.val • v 1 - alpha I s.val • a.recovered
  have hq : ‖q - exactStep I N s.val v H target 0‖ ≤ 20000000 * A ^ 2 * (u + uO) * S := by
    have he : q - exactStep I N s.val v H target 0 =
        -(alpha I s.val) • (a.recovered - exactRecovered I N s.val v H target) := by
      change q - ((1 + beta I s.val) • v 0 - beta I s.val • v 1 -
        alpha I s.val • exactRecovered I N s.val v H target) = _
      dsimp [q]
      module
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg halpha]
    have hh := mul_le_mul_of_nonneg_left hr1 halpha
    have hc := mul_le_mul_of_nonneg_left halphaL (by positivity : 0 ≤ 20000000 * A * (u + uO) * S)
    nlinarith
  have hop1 : ‖a.prefixOperations.result - q‖ ≤ 1000 * u * (S + 20000000 * A ^ 2 * S) := hop.1
  have hop2 := hop.2
  change ‖a.prefixOperations.result - exactStep I N s.val v H target 0‖ ≤
    40000000000 * A ^ 2 * (u + uO) * S ∧ ‖a.prefixOperations.result‖ ≤ 50000000000 * A ^ 2 * S
  refine ⟨?_, ?_⟩
  · have ht : ‖a.prefixOperations.result - exactStep I N s.val v H target 0‖ ≤
        ‖a.prefixOperations.result - q‖ + ‖q - exactStep I N s.val v H target 0‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (a.prefixOperations.result - q)
        (q - exactStep I N s.val v H target 0)
    nlinarith [mul_le_mul_of_nonneg_right hA2 (mul_nonneg hu hS)]
  · nlinarith [mul_le_mul_of_nonneg_right hA2 hS]

end
end InexactRealizations.Accuracy.Execution
