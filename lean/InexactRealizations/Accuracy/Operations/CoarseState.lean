import InexactRealizations.Accuracy.Operations.Coarse

/-! Coarse bounds for the state operations, including arbitrary input
corrections. These bounds support the finite-horizon perturbation induction. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem PrefixStep.coarse {x previous gradient : E} {alphaHat betaHat u alpha beta S T : ℝ}
    (v : PrefixStep x previous gradient alphaHat betaHat u)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (ha : |alphaHat - alpha| ≤ u * alpha) (hb : |betaHat - beta| ≤ u * beta)
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hx : ‖x‖ ≤ S) (hp : ‖previous‖ ≤ S)
    (hg : alpha * ‖gradient‖ ≤ T) :
    ‖v.result - ((1 + beta) • x - beta • previous - alpha • gradient)‖ ≤ 1000 * u * (S + T) ∧
      ‖v.result‖ ≤ 2000 * (S + T) := by
  have hd : ‖x - previous‖ ≤ 2 * S := (norm_sub_le _ _).trans (by linarith)
  have hZ : ‖(1 + beta) • x - beta • previous‖ ≤ 3 * S := by
    have hh := norm_sub_le ((1 + beta) • x) (beta • previous)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hbeta, abs_of_nonneg (by positivity : 0 ≤ 1 + beta)] at hh
    nlinarith [mul_le_mul (show 1 + beta ≤ 2 by linarith) hx (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      mul_le_mul hbeta1 hp (norm_nonneg _) zero_le_one]
  have hq : ‖(1 + beta) • x - beta • previous - alpha • gradient‖ ≤ 3 * S + T := by
    have hh := norm_sub_le ((1 + beta) • x - beta • previous) (alpha • gradient)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg halpha] at hh
    linarith
  have hh := v.local_error hu hu1 halpha hbeta hbeta1 ha hb
  have hlead : beta * ‖x - previous‖ + 2 * (1 + beta) * ‖x‖ + beta * ‖previous‖ +
      ‖(1 + beta) • x - beta • previous‖ + 2 * alpha * ‖gradient‖ +
      ‖(1 + beta) • x - beta • previous - alpha • gradient‖ ≤ 13 * S + 3 * T := by
    nlinarith [mul_le_mul hbeta1 hd (norm_nonneg _) zero_le_one,
      mul_le_mul (show 1 + beta ≤ 2 by linarith) hx (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      mul_le_mul hbeta1 hp (norm_nonneg _) zero_le_one]
  have htail : ‖x‖ + ‖previous‖ + alpha * ‖gradient‖ ≤ 2 * S + T := by linarith
  have huq : u ^ 2 ≤ u := by nlinarith
  have he : ‖v.result - ((1 + beta) • x - beta • previous - alpha • gradient)‖ ≤ 1000 * u * (S + T) := by
    nlinarith [mul_le_mul_of_nonneg_left hlead hu,
      mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ 100 * u ^ 2),
      mul_le_mul_of_nonneg_right huq (show 0 ≤ 2 * S + T by positivity)]
  refine ⟨he, ?_⟩
  have hn : ‖v.result‖ ≤ ‖v.result - ((1 + beta) • x - beta • previous - alpha • gradient)‖ +
      ‖(1 + beta) • x - beta • previous - alpha • gradient‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (v.result - ((1 + beta) • x - beta • previous - alpha • gradient))
      ((1 + beta) • x - beta • previous - alpha • gradient)
  nlinarith [mul_le_mul_of_nonneg_right hu1 (show 0 ≤ S + T by positivity)]

omit [NormedSpace ℝ E] in
theorem rounded_zero_eq (out exact : E) (herr : ‖out - exact‖ ≤ (0 : ℝ) * ‖exact‖) : out = exact := by
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa only [zero_mul] using herr) (norm_nonneg _)))

theorem CompensatedStep.zero_total {x average correction : E} {prepared phi : ℝ}
    (v : CompensatedStep x average correction phi prepared 0)
    (hp : |prepared - phi| ≤ (0 : ℝ) * phi) :
    v.total = (average + correction) + phi • (x - (average + correction)) := by
  have hp' : prepared = phi := sub_eq_zero.mp (abs_eq_zero.mp
    (le_antisymm (by simpa only [zero_mul] using hp) (abs_nonneg _)))
  have h1 := rounded_zero_eq _ _ v.difference_error
  have h2 := rounded_zero_eq _ _ v.corrected_error
  have h3 := rounded_zero_eq _ _ v.product_error
  have h4 := rounded_zero_eq _ _ v.a_error
  have h5 := rounded_zero_eq _ _ v.c_error
  have h6 := rounded_zero_eq _ _ v.d_error
  have h7 := rounded_zero_eq _ _ v.correction_error
  have hc : v.c = average + (correction + phi • ((x - average) - correction)) := by
    rw [h5, h4, h3, h2, h1, hp']
  have hr : v.nextCorrection = 0 := by rw [h7, h6, h5]; abel
  rw [total, hc, hr, add_zero]
  module

set_option maxHeartbeats 1000000 in
theorem CompensatedStep.total_error_coarse {x average correction : E} {phi prepared u : ℝ}
    (v : CompensatedStep x average correction phi prepared u)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hphi : 0 ≤ phi) (hphi1 : phi ≤ 1)
    (hp : |prepared - phi| ≤ u * phi) :
    ‖v.total - ((average + correction) + phi • (x - (average + correction)))‖ ≤
      1000 * u * (‖x‖ + ‖average‖ + ‖correction‖) := by
  by_cases hz : u = 0
  · subst u
    rw [v.zero_total hp]
    simp
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    let K := ‖correction‖ / u
    have hK : 0 ≤ K := div_nonneg (norm_nonneg _) hu
    have hk : ‖correction‖ ≤ u * K := by
      dsimp [K]
      field_simp [hz]
      exact le_rfl
    have hh := v.average_error hu hu1 hphi hphi1 hp hK hk
    have hD : ‖x - (average + correction)‖ ≤ ‖x‖ + ‖average‖ + ‖correction‖ :=
      (norm_sub_le _ _).trans (by linarith [norm_add_le average correction])
    have huq : u ^ 2 ≤ u := by nlinarith
    have hcancel : u ^ 2 * K = u * ‖correction‖ := by dsimp [K]; field_simp [hz]
    have hb := mul_le_mul_of_nonneg_left hD hphi
    have ht := mul_le_mul_of_nonneg_right hphi1 (norm_nonneg (x - (average + correction)))
    have hlead := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 6 * u)
    have hnorms : 0 ≤ ‖x‖ + ‖average‖ + ‖correction‖ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 6 * u + 200 * u ^ 2),
      mul_le_mul_of_nonneg_right huq hnorms,
      mul_le_mul_of_nonneg_right huq (norm_nonneg average), norm_nonneg x, norm_nonneg average,
      norm_nonneg correction]

theorem CompensatedStep.raw_error_coarse {x average correction : E} {phi prepared u : ℝ}
    (v : CompensatedStep x average correction phi prepared u)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hphi : 0 ≤ phi) (hphi1 : phi ≤ 1)
    (hp : |prepared - phi| ≤ u * phi) :
    ‖v.c - ((average + correction) + phi • (x - (average + correction)))‖ ≤
      2000 * u * (‖x‖ + ‖average‖ + ‖correction‖) := by
  have hh := v.total_error_coarse hu hu1 hphi hphi1 hp
  have hc := v.correction_bound hu hu1 hphi hphi1 hp
  have he : v.c - ((average + correction) + phi • (x - (average + correction))) =
      (v.total - ((average + correction) + phi • (x - (average + correction)))) - v.nextCorrection := by
    dsimp [CompensatedStep.total]
    abel
  rw [he]
  nlinarith [norm_sub_le (v.total - ((average + correction) + phi • (x - (average + correction)))) v.nextCorrection,
    mul_nonneg hu (show 0 ≤ ‖x‖ + ‖average‖ + ‖correction‖ by positivity)]

end
end InexactRealizations.Accuracy
