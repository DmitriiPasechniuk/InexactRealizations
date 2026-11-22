import InexactRealizations.Accuracy.Bounds.StageQuery

/-! Uniform one-stage bounds on the recovered gradient, with its natural
factor L. No differentiability of a rounding selection is required. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO S : ℝ} {p : Prepared I N u}
  {s : Fin N} {v : State E} {H : E →ₗ[ℝ] E} {target : E}

theorem exact_recovered_size (hN : 2 ≤ N) (hS : 0 ≤ S) (hv : Bounded v I.L S)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (htarget : ‖target‖ ≤ S) :
    ‖exactRecovered I N s.val v H target‖ ≤ 5 * parameterBound I.kappa N * I.L * S := by
  let A := parameterBound I.kappa N
  change ‖exactRecovered I N s.val v H target‖ ≤ 5 * A * I.L * S
  have hA : 1 ≤ A := parameterBound_one I N
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hq := exact_query_size hN hS hv (s := s)
  have hg : ‖exactAnswer I N s.val v H target‖ ≤ 3 * I.L * S := by
    have hh := mul_le_mul_of_nonneg_left (norm_sub_le (exactQuery I N s.val v) target) hL
    exact (hH _).trans (by nlinarith)
  unfold exactRecovered
  split_ifs
  · nlinarith [mul_le_mul_of_nonneg_right hA (mul_nonneg hL hS)]
  · have ht := (theta_unit I hN s.isLt).1
    have hi := theta_parameter_bound I hN s.isLt
    have hb := hv.gradient 7 (by decide)
    have hd : ‖exactAnswer I N s.val v H target - v 7‖ ≤ 4 * I.L * S :=
      (norm_sub_le _ _).trans (by linarith)
    have hh := norm_add_le (v 7) ((theta I N s.val)⁻¹ • (exactAnswer I N s.val v H target - v 7))
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht] at hh
    have hmul := mul_le_mul hi hd (norm_nonneg _) (show 0 ≤ A by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hA (mul_nonneg hL hS)]

set_option maxHeartbeats 1000000 in
theorem Stage.recovered_size_error (a : Stage p s v H target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hS : 0 ≤ S) (hv : Bounded v I.L S) (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (htarget : ‖target‖ ≤ S) :
    ‖a.recovered - exactRecovered I N s.val v H target‖ ≤
      20000000 * parameterBound I.kappa N * (u + uO) * I.L * S ∧
    ‖a.recovered‖ ≤ 20000000 * parameterBound I.kappa N * I.L * S := by
  let A := parameterBound I.kappa N
  change ‖a.recovered - exactRecovered I N s.val v H target‖ ≤ 20000000 * A * (u + uO) * I.L * S ∧
    ‖a.recovered‖ ≤ 20000000 * A * I.L * S
  have hA : 1 ≤ A := parameterBound_one I N
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hu1 : u ≤ 1 := by linarith
  have hdelta : 0 ≤ (u + uO) * I.L * S := by positivity
  have hAu : 0 ≤ u * A * I.L * S := by positivity
  have hAO : 0 ≤ uO * A * I.L * S := by positivity
  have hg := a.answer_size_error hN hu hu1 huO huO1 hS hv hH htarget
  have hg1 := hg.1
  have hg2 := hg.2
  by_cases hs : s.val < 2
  · simp only [Stage.recovered, observedRecovered, hs, dite_true, exactRecovered, ite_true]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hA (show 0 ≤ (u + uO) * I.L * S by positivity)]
    · nlinarith [mul_le_mul_of_nonneg_right hA (mul_nonneg hL hS)]
  · have ht := theta_unit I hN s.isLt
    have hi : (theta I N s.val)⁻¹ ≤ A := theta_parameter_bound I hN s.isLt
    have hb : ‖v 7‖ ≤ 10000 * I.L * S := by nlinarith [hv.gradient 7 (by decide)]
    have hop := (a.recoveryOperations (by omega)).coarse hu hu2 ht.1 ht.2 (p.theta_error s)
      (by positivity : 0 ≤ 10000 * I.L * S) hA hi hg.2 hb
    let q := v 7 + (theta I N s.val)⁻¹ • (a.answer - v 7)
    have hq : ‖q - exactRecovered I N s.val v H target‖ ≤ 5000 * A * (u + uO) * I.L * S := by
      have he : q - exactRecovered I N s.val v H target =
          (theta I N s.val)⁻¹ • (a.answer - exactAnswer I N s.val v H target) := by
        simp only [q, exactRecovered, hs, ite_false]
        module
      rw [he, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht.1]
      have hh := mul_le_mul hi hg.1 (norm_nonneg _) (show 0 ≤ A by linarith)
      nlinarith
    have hact : a.recovered = (a.recoveryOperations (by omega)).result := by
      simp only [Stage.recovered, observedRecovered, hs, dite_false]
    have hop1 : ‖a.recovered - q‖ ≤ 1000 * u * A * (10000 * I.L * S) := by
      rw [hact]
      exact hop.1
    refine ⟨?_, ?_⟩
    · have ht' : ‖a.recovered - exactRecovered I N s.val v H target‖ ≤
          ‖a.recovered - q‖ + ‖q - exactRecovered I N s.val v H target‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (a.recovered - q)
          (q - exactRecovered I N s.val v H target)
      change ‖a.recovered - exactRecovered I N s.val v H target‖ ≤ _
      nlinarith [mul_nonneg huO (show 0 ≤ A * I.L * S by positivity)]
    · rw [hact]
      nlinarith [hop.2]

end
end InexactRealizations.Accuracy.Execution
