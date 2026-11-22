import InexactRealizations.Accuracy.Operations.Prepared

/-! The literal subtraction/division/addition recovering the gradient at X.
Multiplication by the exact theta retains the sharp nominal error scale. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure RecoveryStep (g previous : E) (prepared u : ℝ) where
  difference : E
  quotient : E
  result : E
  difference_error : ‖difference - (g - previous)‖ ≤ u * ‖g - previous‖
  quotient_error : ‖quotient - prepared⁻¹ • difference‖ ≤ u * ‖prepared⁻¹ • difference‖
  result_error : ‖result - (previous + quotient)‖ ≤ u * ‖previous + quotient‖

namespace RecoveryStep
variable {g previous : E} {prepared u : ℝ}

set_option maxHeartbeats 1000000 in
theorem local_error (v : RecoveryStep g previous prepared u) {theta : ℝ}
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (htheta : 0 < theta)
    (hprepared : |prepared - theta| ≤ u * theta) :
    theta * ‖v.result - (previous + theta⁻¹ • (g - previous))‖ ≤
      u * (3 * ‖g - previous‖ + theta * ‖previous + theta⁻¹ • (g - previous)‖) +
        100 * u ^ 2 * ‖g - previous‖ := by
  let D := g - previous
  let q := previous + theta⁻¹ • D
  let r := theta / prepared
  let e0 := v.difference - D
  let e1 := v.quotient - prepared⁻¹ • v.difference
  let e2 := v.result - (previous + v.quotient)
  have hD : 0 ≤ ‖D‖ := norm_nonneg _
  have hu1 : u ≤ 1 := by linarith
  have huq : u ^ 2 ≤ u := by nlinarith
  have hp := prepared_inverse htheta hu hu2 hprepared
  have hr : 0 < r := div_pos htheta hp.1
  have hr2 : r ≤ 2 := (le_abs_self r).trans hp.2.2
  have hre : |r - 1| ≤ u + 2 * u ^ 2 := hp.2.1
  have hr3 : r ≤ 1 + 3 * u := by nlinarith [(le_abs_self (r - 1)).trans hre]
  have h0 : ‖e0‖ ≤ u * ‖D‖ := v.difference_error
  have hds : ‖v.difference‖ ≤ (1 + u) * ‖D‖ := by
    have hh : ‖v.difference‖ ≤ ‖D‖ + ‖v.difference - D‖ := by
      simpa only [add_sub_cancel] using norm_add_le D (v.difference - D)
    nlinarith
  have h1 : theta * ‖e1‖ ≤ u * r * ‖v.difference‖ := by
    have hh := mul_le_mul_of_nonneg_left v.quotient_error htheta.le
    simpa only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp.1, r, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm] using hh
  have h1' : theta * ‖e1‖ ≤ u * ‖D‖ + 5 * u ^ 2 * ‖D‖ := by
    have hrr : r * (1 + u) ≤ 1 + 5 * u := by
      nlinarith [mul_le_mul_of_nonneg_right hr2 hu]
    have hh := mul_le_mul_of_nonneg_left hds (mul_nonneg hu hr.le)
    have hb := mul_le_mul_of_nonneg_left hrr (mul_nonneg hu hD)
    nlinarith
  have hquot : theta * ‖v.quotient - theta⁻¹ • D‖ ≤ 3 * u * ‖D‖ + 10 * u ^ 2 * ‖D‖ := by
    have he : theta • (v.quotient - theta⁻¹ • D) =
        theta • e1 + (r - 1) • D + r • e0 := by
      have hc : theta * theta⁻¹ = 1 := mul_inv_cancel₀ htheta.ne'
      dsimp [e1, e0, r]
      simp only [smul_sub, smul_smul, hc, one_smul, div_eq_mul_inv, sub_smul]
      abel
    have ht : theta * ‖v.quotient - theta⁻¹ • D‖ ≤
        theta * ‖e1‖ + |r - 1| * ‖D‖ + r * ‖e0‖ := by
      calc
        _ = ‖theta • (v.quotient - theta⁻¹ • D)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos htheta]
        _ = ‖theta • e1 + (r - 1) • D + r • e0‖ := congrArg norm he
        _ ≤ _ := by
          simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos htheta, abs_of_pos hr] using
            (norm_add_le (theta • e1 + (r - 1) • D) (r • e0)).trans
              (add_le_add (norm_add_le (theta • e1) ((r - 1) • D)) le_rfl)
    have hb := mul_le_mul hr3 h0 (norm_nonneg _) (by positivity : 0 ≤ 1 + 3 * u)
    nlinarith [mul_le_mul_of_nonneg_right hre hD]
  have hpre : theta * ‖previous + v.quotient‖ ≤ theta * ‖q‖ +
      3 * u * ‖D‖ + 10 * u ^ 2 * ‖D‖ := by
    have he : previous + v.quotient = q + (v.quotient - theta⁻¹ • D) := by dsimp [q]; abel
    have ht : ‖previous + v.quotient‖ ≤ ‖q‖ + ‖v.quotient - theta⁻¹ • D‖ := by rw [he]; exact norm_add_le _ _
    nlinarith [mul_le_mul_of_nonneg_left ht htheta.le]
  have h2 : theta * ‖e2‖ ≤ u * theta * ‖q‖ + 13 * u ^ 2 * ‖D‖ := by
    have hh := mul_le_mul_of_nonneg_left v.result_error htheta.le
    have hb := mul_le_mul_of_nonneg_left hpre hu
    have hc := mul_le_mul_of_nonneg_right huq (mul_nonneg hu hD)
    nlinarith
  have ht : ‖v.result - q‖ ≤ ‖e2‖ + ‖v.quotient - theta⁻¹ • D‖ := by
    have he : v.result - q = e2 + (v.quotient - theta⁻¹ • D) := by dsimp [q, e2]; abel
    rw [he]
    exact norm_add_le _ _
  change theta * ‖v.result - q‖ ≤ _
  nlinarith [mul_le_mul_of_nonneg_left ht htheta.le, mul_nonneg (sq_nonneg u) hD]

end RecoveryStep
end
end InexactRealizations.Accuracy
