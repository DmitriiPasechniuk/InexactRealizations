import InexactRealizations.Accuracy.Bounds.StageRecovery

/-! Actual stored averages/corrections/gradients versus one exact stage. -/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO S : ℝ} {p : Prepared I N u}
  {s : Fin N} {v : State E} {H : E →ₗ[ℝ] E} {target : E}

set_option maxHeartbeats 1000000 in
theorem Stage.averages_size_error (a : Stage p s v H target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hS : 0 ≤ S) (hv : Bounded v I.L S) :
    ‖a.nextAverage - exactStep I N s.val v H target 2‖ ≤ 6000 * u * S ∧
    ‖a.nextCorrection - exactStep I N s.val v H target 4‖ ≤ 600 * u * S ∧
    ‖a.nextAverage‖ ≤ 10000 * S ∧ ‖a.nextCorrection‖ ≤ 1000 * S := by
  have hx := hv.scalar 0 (by decide)
  have hb := hv.scalar 3 (by decide)
  have hc := hv.scalar 5 (by decide)
  change ‖a.nextAverage - (if s.val + 2 < N then if s.val < 2 then v 0 else
    representedAverage v + phi I N s.val • (v 0 - representedAverage v) else v 3)‖ ≤ _ ∧
    ‖a.nextCorrection - (if s.val + 2 < N then 0 else v 5)‖ ≤ _ ∧ _
  by_cases hvalid : s.val + 2 < N
  · by_cases hs : s.val < 2
    · simp only [Stage.nextAverage, Stage.nextCorrection, hvalid, dite_true, ite_true, hs, sub_self, norm_zero]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
    · have hp := phi_unit I hN (by omega : 2 ≤ s.val) hvalid
      cases hchoice : a.averageOperations (by omega) hvalid with
      | inl op =>
        have herr : ‖op.c - (representedAverage v + phi I N s.val • (v 0 - representedAverage v))‖ ≤
            2000 * u * (‖v 0‖ + ‖v 3‖ + ‖v 5‖) :=
          op.raw_error_coarse hu hu1 hp.1.le hp.2 (p.phi_error s hvalid)
        have hcorr := op.correction_bound hu hu1 hp.1.le hp.2 (p.phi_error s hvalid)
        have hq : ‖representedAverage v + phi I N s.val • (v 0 - representedAverage v)‖ ≤ 2 * S := by
          exact affine_size _ hp.1.le hp.2 _ _ _ (by linarith)
            ((norm_add_le _ _).trans (by linarith))
        have he : ‖op.c - (representedAverage v + phi I N s.val • (v 0 - representedAverage v))‖ ≤ 6000 * u * S := by
          nlinarith [mul_le_mul_of_nonneg_left (show ‖v 0‖ + ‖v 3‖ + ‖v 5‖ ≤ 3 * S by linarith)
            (by positivity : 0 ≤ 2000 * u)]
        have hce : ‖op.nextCorrection‖ ≤ 600 * u * S := by
          nlinarith [mul_le_mul_of_nonneg_left (show ‖v 0‖ + ‖v 3‖ + ‖v 5‖ ≤ 3 * S by linarith)
            (by positivity : 0 ≤ 200 * u)]
        have hsize : ‖op.c‖ ≤ 10000 * S := by
          have ht : ‖op.c‖ ≤ ‖op.c - (representedAverage v + phi I N s.val • (v 0 - representedAverage v))‖ +
              ‖representedAverage v + phi I N s.val • (v 0 - representedAverage v)‖ := by
            simpa only [sub_add_cancel] using norm_add_le
              (op.c - (representedAverage v + phi I N s.val • (v 0 - representedAverage v)))
              (representedAverage v + phi I N s.val • (v 0 - representedAverage v))
          nlinarith [mul_le_mul_of_nonneg_right hu1 hS]
        simp only [Stage.nextAverage, Stage.nextCorrection, hvalid, dite_true, ite_true, hs, dite_false, ite_false, hchoice, sub_zero]
        exact ⟨he, hce, hsize, by nlinarith [mul_le_mul_of_nonneg_right hu1 hS]⟩
      | inr op =>
        have hbbar : ‖representedAverage v‖ ≤ 2 * S := (norm_add_le _ _).trans (by linarith)
        have hop := op.coarse hu hu1 hp.1.le hp.2 (p.phi_error s hvalid)
          (by positivity : 0 ≤ 2 * S) (by linarith : ‖v 0‖ ≤ 2 * S) hbbar
        simp only [Stage.nextAverage, Stage.nextCorrection, hvalid, dite_true, ite_true, hs,
          dite_false, ite_false, hchoice, sub_zero, norm_zero]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hop.1, hop.2]

  · simp only [Stage.nextAverage, Stage.nextCorrection, hvalid, dite_false, ite_false, sub_self, norm_zero]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

set_option maxHeartbeats 1000000 in
theorem Stage.gradient_size_error (a : Stage p s v H target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hS : 0 ≤ S) (hv : Bounded v I.L S) (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (htarget : ‖target‖ ≤ S) :
    ‖a.nextGradient - exactStep I N s.val v H target 6‖ ≤
      3000000000 * parameterBound I.kappa N * (u + uO) * I.L * S ∧
    ‖a.nextGradient‖ ≤ 4000000000 * parameterBound I.kappa N * I.L * S := by
  let A := parameterBound I.kappa N
  have hA : 1 ≤ A := parameterBound_one I N
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hu1 : u ≤ 1 := by linarith
  have hdelta : 0 ≤ (u + uO) * I.L * S := by positivity
  have hAu : 0 ≤ u * A * I.L * S := by positivity
  have hAO : 0 ≤ uO * A * I.L * S := by positivity
  have hb := hv.gradient 7 (by decide)
  change ‖a.nextGradient - (if s.val + 2 < N then if s.val < 2 then exactAnswer I N s.val v H target else
    v 7 + phi I N s.val • (exactRecovered I N s.val v H target - v 7) else v 7)‖ ≤
    3000000000 * A * (u + uO) * I.L * S ∧ ‖a.nextGradient‖ ≤ 4000000000 * A * I.L * S
  by_cases hvalid : s.val + 2 < N
  · by_cases hs : s.val < 2
    · have hg := a.answer_size_error hN hu hu1 huO huO1 hS hv hH htarget
      simp only [Stage.nextGradient, hvalid, dite_true, ite_true, hs]
      constructor <;> nlinarith [hg.1, hg.2, mul_le_mul_of_nonneg_right hA (mul_nonneg hL hS),
        mul_le_mul_of_nonneg_right hA (show 0 ≤ (u + uO) * I.L * S by positivity)]
    · have hp := phi_unit I hN (by omega : 2 ≤ s.val) hvalid
      have hr := a.recovered_size_error hN hu hu2 huO huO1 hS hv hH htarget
      have hr1 : ‖a.recovered - exactRecovered I N s.val v H target‖ ≤ 20000000 * A * (u + uO) * I.L * S := hr.1
      have hr2 : ‖a.recovered‖ ≤ 20000000 * A * I.L * S := hr.2
      let q := v 7 + phi I N s.val • (a.recovered - v 7)
      let q0 := v 7 + phi I N s.val • (exactRecovered I N s.val v H target - v 7)
      let op := a.gradientOperations (by omega) hvalid
      have hb' : ‖v 7‖ ≤ 20000000 * A * I.L * S := by
        nlinarith [mul_le_mul_of_nonneg_right hA (mul_nonneg hL hS)]
      have hop := op.coarse hu hu1 hp.1.le hp.2 (p.phi_error s hvalid)
        (by positivity : 0 ≤ 20000000 * A * I.L * S) hr2 hb'
      have hq : ‖q - q0‖ ≤ 20000000 * A * (u + uO) * I.L * S := by
        have he : q - q0 = phi I N s.val • (a.recovered - exactRecovered I N s.val v H target) := by
          dsimp [q, q0]
          module
        rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hp.1]
        exact (mul_le_mul_of_nonneg_right hp.2 (norm_nonneg _)).trans (by simpa only [one_mul] using hr1)
      have he : ‖op.result - q0‖ ≤ 3000000000 * A * (u + uO) * I.L * S := by
        have ht : ‖op.result - q0‖ ≤ ‖op.result - q‖ + ‖q - q0‖ := by
          simpa only [sub_add_sub_cancel] using norm_add_le (op.result - q) (q - q0)
        have hop1 : ‖op.result - q‖ ≤ 100 * u * (20000000 * A * I.L * S) := hop.1
        nlinarith [mul_nonneg huO (show 0 ≤ A * I.L * S by positivity)]
      simp only [Stage.nextGradient, hvalid, dite_true, ite_true, hs, dite_false, ite_false]
      exact ⟨he, by nlinarith [hop.2]⟩
  · simp only [Stage.nextGradient, hvalid, dite_false, ite_false, sub_self, norm_zero]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_right hA (mul_nonneg hL hS)]

end
end InexactRealizations.Accuracy.Execution
