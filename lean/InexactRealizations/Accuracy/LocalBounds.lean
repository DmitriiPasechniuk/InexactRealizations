import InexactRealizations.Accuracy.Compensated

/-! Dimension-independent bounds for the actual compensation register,
and cancellation of the first-order constant-vector error. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem rounded_size {u : ℝ} (hu1 : u ≤ 1) (out exact : E)
    (herr : ‖out - exact‖ ≤ u * ‖exact‖) : ‖out‖ ≤ 2 * ‖exact‖ := by
  have ht : ‖out‖ ≤ ‖out - exact‖ + ‖exact‖ := by
    simpa only [sub_add_cancel] using norm_add_le (out - exact) exact
  nlinarith [mul_le_mul_of_nonneg_right hu1 (norm_nonneg exact)]

namespace CompensatedStep
variable {x average correction : E} {phi prepared u : ℝ}

set_option maxHeartbeats 1000000 in
theorem correction_bound (v : CompensatedStep x average correction phi prepared u)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hphi : 0 ≤ phi) (hphi1 : phi ≤ 1)
    (hprepared : |prepared - phi| ≤ u * phi) :
    ‖v.nextCorrection‖ ≤ 200 * u * (‖x‖ + ‖average‖ + ‖correction‖) := by
  have hp : |prepared| ≤ 2 := by
    have ht : |prepared| ≤ |prepared - phi| + |phi| := by
      simpa only [sub_add_cancel] using abs_add_le (prepared - phi) phi
    rw [abs_of_nonneg hphi] at ht
    nlinarith [mul_le_mul_of_nonneg_left hphi1 hu]
  have h1 : ‖v.difference‖ ≤ 2 * (‖x‖ + ‖average‖) :=
    (rounded_size hu1 _ _ v.difference_error).trans (by linarith [norm_sub_le x average])
  have h2 : ‖v.corrected‖ ≤ 2 * (‖v.difference‖ + ‖correction‖) :=
    (rounded_size hu1 _ _ v.corrected_error).trans (by linarith [norm_sub_le v.difference correction])
  have h3 : ‖v.product‖ ≤ 4 * ‖v.corrected‖ := by
    have hh := rounded_size hu1 _ _ v.product_error
    rw [norm_smul, Real.norm_eq_abs] at hh
    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg v.corrected)]
  have h4 : ‖v.a‖ ≤ 32 * ‖x‖ + 32 * ‖average‖ + 18 * ‖correction‖ := by
    have hh := rounded_size hu1 _ _ v.a_error
    nlinarith [norm_add_le correction v.product]
  let ec := v.c - (average + v.a)
  let ed := v.d - (v.c - average)
  have hc : ‖ec‖ ≤ u * (‖average‖ + ‖v.a‖) :=
    v.c_error.trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) hu)
  have he : v.c - average = v.a + ec := by dsimp [ec]; abel
  have hd : ‖ed‖ ≤ u * (‖average‖ + 2 * ‖v.a‖) := by
    have ht : ‖v.c - average‖ ≤ ‖v.a‖ + ‖ec‖ := by rw [he]; exact norm_add_le _ _
    have hcc := mul_le_mul_of_nonneg_right hu1 (show 0 ≤ ‖average‖ + ‖v.a‖ by positivity)
    exact v.d_error.trans (by nlinarith [mul_le_mul_of_nonneg_left ht hu])
  have hid : v.a - v.d = -(ec + ed) := by dsimp [ec, ed]; abel
  have hf := rounded_size hu1 _ _ v.correction_error
  rw [hid, norm_neg] at hf
  have hs : ‖v.nextCorrection‖ ≤ u * (4 * ‖average‖ + 6 * ‖v.a‖) := by
    nlinarith [norm_add_le ec ed]
  have hb := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 6 * u)
  nlinarith [mul_nonneg hu (norm_nonneg x), mul_nonneg hu (norm_nonneg average),
    mul_nonneg hu (norm_nonneg correction)]

end CompensatedStep
end
end InexactRealizations.Accuracy
