import InexactRealizations.Accuracy.Compensated

/-! The three rounded operations in a gradient average, or an
uncompensated vector average: difference, prepared product, final sum. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure BlendStep (x previous : E) (prepared u : ℝ) where
  difference : E
  product : E
  result : E
  difference_error : ‖difference - (x - previous)‖ ≤ u * ‖x - previous‖
  product_error : ‖product - prepared • difference‖ ≤ u * ‖prepared • difference‖
  result_error : ‖result - (previous + product)‖ ≤ u * ‖previous + product‖

namespace BlendStep
variable {x previous : E} {prepared u : ℝ}

theorem local_error (v : BlendStep x previous prepared u) {phi : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hphi : 0 ≤ phi)
    (hprepared : |prepared - phi| ≤ u * phi) :
    ‖v.result - (previous + phi • (x - previous))‖ ≤
      u * (‖previous + phi • (x - previous)‖ + 3 * phi * ‖x - previous‖) +
        11 * u ^ 2 * phi * ‖x - previous‖ := by
  let D := x - previous
  have hs : ‖phi • v.difference - phi • D‖ ≤ u * (phi * ‖D‖) + u ^ 2 * 0 := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hphi]
    nlinarith [mul_le_mul_of_nonneg_left v.difference_error hphi]
  have hp : ‖prepared • v.difference - phi • v.difference‖ ≤ u * ‖phi • v.difference‖ := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs, abs_of_nonneg hphi]
    nlinarith [mul_le_mul_of_nonneg_right hprepared (norm_nonneg v.difference)]
  have hsize : ‖phi • D‖ ≤ phi * ‖D‖ + u * 0 := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hphi]
  have h1 := rounded_approx hu hu1 (by norm_num : (0 : ℝ) ≤ 0)
    (prepared • v.difference) (phi • v.difference) (phi • D) hp hs hsize
  have h1' : ‖prepared • v.difference - phi • D‖ ≤ u * (2 * phi * ‖D‖) + u ^ 2 * (phi * ‖D‖) := by
    convert h1 using 1
    ring
  have h2 := rounded_approx hu hu1 (mul_nonneg hphi (norm_nonneg D))
    v.product (prepared • v.difference) (phi • D) v.product_error h1' hsize
  have h2' : ‖(previous + v.product) - (previous + phi • D)‖ ≤
      u * (3 * phi * ‖D‖) + u ^ 2 * (4 * phi * ‖D‖) := by
    simp only [add_sub_add_left_eq_sub]
    convert h2 using 1
    ring
  have h3 := rounded_approx hu hu1 (by positivity : 0 ≤ 4 * phi * ‖D‖)
    v.result (previous + v.product) (previous + phi • D) v.result_error h2'
    (show ‖previous + phi • D‖ ≤ ‖previous + phi • D‖ + u * 0 by simp)
  convert h3 using 1
  ring

end BlendStep
end
end InexactRealizations.Accuracy
