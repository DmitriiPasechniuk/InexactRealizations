import InexactRealizations.Accuracy.Compensated

/-! The four rounded vector operations forming the current
query. The initial average is rounded before it appears again inside the
difference; collecting that shared error preserves its factor 1-theta. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure QueryStep (x average : E) (prepared u : ℝ) where
  start : E
  difference : E
  product : E
  result : E
  start_error : ‖start - average‖ ≤ u * ‖average‖
  difference_error : ‖difference - (x - start)‖ ≤ u * ‖x - start‖
  product_error : ‖product - prepared • difference‖ ≤ u * ‖prepared • difference‖
  result_error : ‖result - (start + product)‖ ≤ u * ‖start + product‖

namespace QueryStep
variable {x average : E} {prepared u : ℝ}

set_option maxHeartbeats 2000000 in
theorem local_error (v : QueryStep x average prepared u) {theta : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hprepared : |prepared - theta| ≤ u * theta) :
    ‖v.result - (average + theta • (x - average))‖ ≤
      u * ((1 - theta) * ‖average‖ + 3 * theta * ‖x - average‖ +
        ‖average + theta • (x - average)‖) + 100 * u ^ 2 * (‖average‖ + ‖x - average‖) := by
  let D := x - average
  let q := average + theta • D
  let e0 := v.start - average
  let e1 := v.difference - (x - v.start)
  let e2 := v.product - prepared • v.difference
  let e3 := v.result - (v.start + v.product)
  have hB : 0 ≤ ‖average‖ := norm_nonneg _
  have hD : 0 ≤ ‖D‖ := norm_nonneg _
  have hu2 : u ^ 2 ≤ u := by nlinarith
  have hp : |prepared| ≤ (1 + u) * theta := by
    have ht : |prepared| ≤ |prepared - theta| + |theta| := by
      simpa only [sub_add_cancel] using abs_add_le (prepared - theta) theta
    rw [abs_of_nonneg htheta] at ht
    linarith
  have h0 : ‖e0‖ ≤ u * ‖average‖ := v.start_error
  have hid : x - v.start = D - e0 := by dsimp [D, e0]; abel
  have h1 : ‖e1‖ ≤ u * ‖D‖ + u ^ 2 * ‖average‖ := by
    have hb : ‖x - v.start‖ ≤ ‖D‖ + u * ‖average‖ := by
      rw [hid]
      exact (norm_sub_le _ _).trans (add_le_add le_rfl h0)
    exact v.difference_error.trans (by nlinarith [mul_le_mul_of_nonneg_left hb hu])
  have hd : ‖v.difference - D‖ ≤ u * (‖D‖ + 2 * ‖average‖) := by
    have he : v.difference - D = -e0 + e1 := by dsimp [D, e0, e1]; abel
    rw [he]
    have hh := norm_add_le (-e0) e1
    rw [norm_neg] at hh
    nlinarith [mul_le_mul_of_nonneg_right hu2 hB]
  have hds : ‖v.difference‖ ≤ ‖D‖ + u * (‖D‖ + 2 * ‖average‖) := by
    have ht : ‖v.difference‖ ≤ ‖D‖ + ‖v.difference - D‖ := by
      simpa only [add_sub_cancel] using norm_add_le D (v.difference - D)
    exact ht.trans (add_le_add le_rfl hd)
  have h2 : ‖e2‖ ≤ u * theta * ‖D‖ + u ^ 2 * theta * (3 * ‖D‖ + 4 * ‖average‖) := by
    have hh := v.product_error
    rw [norm_smul, Real.norm_eq_abs] at hh
    have hmul := mul_le_mul hp hds (norm_nonneg _) (by positivity : 0 ≤ (1 + u) * theta)
    have htail : u ^ 3 * theta * (‖D‖ + 2 * ‖average‖) ≤
        u ^ 2 * theta * (‖D‖ + 2 * ‖average‖) := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ u ^ 2 * theta * (‖D‖ + 2 * ‖average‖))
        (sub_nonneg.mpr hu1)]
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hmul hu])
  have hproduct : ‖v.product - theta • D‖ ≤ u * (7 * ‖D‖ + 8 * ‖average‖) := by
    have he : v.product - theta • D = e2 + (prepared - theta) • D + prepared • (v.difference - D) := by
      dsimp [e2]
      module
    have ht : ‖v.product - theta • D‖ ≤ ‖e2‖ + |prepared - theta| * ‖D‖ + |prepared| * ‖v.difference - D‖ := by
      rw [he]
      simpa only [norm_smul, Real.norm_eq_abs] using
        (norm_add_le (e2 + (prepared - theta) • D) (prepared • (v.difference - D))).trans
          (add_le_add (norm_add_le e2 ((prepared - theta) • D)) le_rfl)
    have hh1 := mul_le_mul_of_nonneg_right hprepared hD
    have hh2 := mul_le_mul hp hd (norm_nonneg _) (by positivity : 0 ≤ (1 + u) * theta)
    have hh3 : u ^ 2 * theta * (3 * ‖D‖ + 4 * ‖average‖) ≤ u * (3 * ‖D‖ + 4 * ‖average‖) := by
      nlinarith [mul_le_mul_of_nonneg_right htheta1 (sq_nonneg u),
        mul_le_mul_of_nonneg_right hu2 (show 0 ≤ 3 * ‖D‖ + 4 * ‖average‖ by positivity)]
    have hh4 : (1 + u) * theta * (u * (‖D‖ + 2 * ‖average‖)) ≤
        2 * u * (‖D‖ + 2 * ‖average‖) := by
      have ha : (1 + u) * theta ≤ 2 := by nlinarith
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right ha
        (by positivity : 0 ≤ u * (‖D‖ + 2 * ‖average‖))
    nlinarith [mul_le_mul_of_nonneg_right htheta1 (mul_nonneg hu hD)]
  have hraw : ‖(v.start + v.product) - q‖ ≤ 10 * u * (‖average‖ + ‖D‖) := by
    have he : (v.start + v.product) - q = e0 + (v.product - theta • D) := by dsimp [q, e0]; abel
    rw [he]
    nlinarith [norm_add_le e0 (v.product - theta • D)]
  have h3 : ‖e3‖ ≤ u * ‖q‖ + 10 * u ^ 2 * (‖average‖ + ‖D‖) := by
    have ht : ‖v.start + v.product‖ ≤ ‖q‖ + ‖(v.start + v.product) - q‖ := by
      simpa only [add_sub_cancel] using norm_add_le q ((v.start + v.product) - q)
    exact v.result_error.trans (by nlinarith [mul_le_mul_of_nonneg_left ht hu])
  have he : v.result - q = (1 - theta) • e0 + theta • e1 + (prepared - theta) • D +
      (prepared - theta) • (-e0 + e1) + e2 + e3 := by
    dsimp [e0, e1, e2, e3, D, q]
    module
  have hcross : ‖(prepared - theta) • (-e0 + e1)‖ ≤
      u ^ 2 * theta * (‖D‖ + 2 * ‖average‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    have hb : ‖-e0 + e1‖ ≤ u * (‖D‖ + 2 * ‖average‖) := by
      have hh := norm_add_le (-e0) e1
      rw [norm_neg] at hh
      nlinarith [mul_le_mul_of_nonneg_right hu2 hB]
    have hh := mul_le_mul hprepared hb (norm_nonneg _) (mul_nonneg hu htheta)
    nlinarith
  have ht : ‖v.result - q‖ ≤ (1 - theta) * ‖e0‖ + theta * ‖e1‖ + |prepared - theta| * ‖D‖ +
      ‖(prepared - theta) • (-e0 + e1)‖ + ‖e2‖ + ‖e3‖ := by
    rw [he]
    calc
      _ ≤ ‖(1 - theta) • e0 + theta • e1 + (prepared - theta) • D +
          (prepared - theta) • (-e0 + e1) + e2‖ + ‖e3‖ := norm_add_le _ _
      _ ≤ (‖(1 - theta) • e0 + theta • e1 + (prepared - theta) • D +
          (prepared - theta) • (-e0 + e1)‖ + ‖e2‖) + ‖e3‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖(1 - theta) • e0 + theta • e1 + (prepared - theta) • D‖ +
          ‖(prepared - theta) • (-e0 + e1)‖) + ‖e2‖) + ‖e3‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (((‖(1 - theta) • e0 + theta • e1‖ + ‖(prepared - theta) • D‖) +
          ‖(prepared - theta) • (-e0 + e1)‖) + ‖e2‖) + ‖e3‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by
        have hh := norm_add_le ((1 - theta) • e0) (theta • e1)
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr htheta1), abs_of_nonneg htheta] at *
        linarith
  change ‖v.result - q‖ ≤ _
  have hb0 := mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr htheta1)
  have hb1 := mul_le_mul_of_nonneg_left h1 htheta
  have hb2 := mul_le_mul_of_nonneg_right hprepared hD
  have hb3 : theta * ‖average‖ + theta * (‖D‖ + 2 * ‖average‖) +
      theta * (3 * ‖D‖ + 4 * ‖average‖) + 10 * (‖average‖ + ‖D‖) ≤
        100 * (‖average‖ + ‖D‖) := by
    nlinarith [mul_le_mul_of_nonneg_right htheta1 hB,
      mul_le_mul_of_nonneg_right htheta1 hD]
  nlinarith [mul_le_mul_of_nonneg_left hb3 (sq_nonneg u)]

end QueryStep
end
end InexactRealizations.Accuracy
