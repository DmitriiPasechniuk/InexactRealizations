import InexactRealizations.Accuracy.Compensated
import Mathlib.Data.Fin.VecNotation

/-! The printed Prefix expression evaluated from left to right. One
prepared beta is shared by its two occurrences. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure PrefixStep (x previous gradient : E) (alphaHat betaHat u : ℝ) where
  onePlusBeta : ℝ
  currentProduct : E
  previousProduct : E
  difference : E
  gradientProduct : E
  result : E
  one_error : |onePlusBeta - (1 + betaHat)| ≤ u * |1 + betaHat|
  current_error : ‖currentProduct - onePlusBeta • x‖ ≤ u * ‖onePlusBeta • x‖
  previous_error : ‖previousProduct - betaHat • previous‖ ≤ u * ‖betaHat • previous‖
  difference_error : ‖difference - (currentProduct - previousProduct)‖ ≤ u * ‖currentProduct - previousProduct‖
  gradient_error : ‖gradientProduct - alphaHat • gradient‖ ≤ u * ‖alphaHat • gradient‖
  result_error : ‖result - (difference - gradientProduct)‖ ≤ u * ‖difference - gradientProduct‖

namespace PrefixStep
variable {x previous gradient : E} {alphaHat betaHat u : ℝ}

set_option maxHeartbeats 3000000 in
theorem local_error (v : PrefixStep x previous gradient alphaHat betaHat u) {alpha beta : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (ha : |alphaHat - alpha| ≤ u * alpha) (hb : |betaHat - beta| ≤ u * beta) :
    ‖v.result - ((1 + beta) • x - beta • previous - alpha • gradient)‖ ≤
      u * (beta * ‖x - previous‖ + 2 * (1 + beta) * ‖x‖ + beta * ‖previous‖ +
        ‖(1 + beta) • x - beta • previous‖ + 2 * alpha * ‖gradient‖ +
        ‖(1 + beta) • x - beta • previous - alpha • gradient‖) +
      100 * u ^ 2 * (‖x‖ + ‖previous‖ + alpha * ‖gradient‖) := by
  let Z := (1 + beta) • x - beta • previous
  let T := Z - alpha • gradient
  let e0 := v.onePlusBeta - (1 + betaHat)
  let e1 := v.currentProduct - v.onePlusBeta • x
  let e2 := v.previousProduct - betaHat • previous
  let e3 := v.difference - (v.currentProduct - v.previousProduct)
  let e4 := v.gradientProduct - alphaHat • gradient
  let e5 := v.result - (v.difference - v.gradientProduct)
  have huq : u ^ 2 ≤ u := by nlinarith
  have hX : 0 ≤ ‖x‖ := norm_nonneg _
  have hP : 0 ≤ ‖previous‖ := norm_nonneg _
  have hG : 0 ≤ ‖gradient‖ := norm_nonneg _
  have hbhat : |betaHat| ≤ (1 + u) * beta := by
    have hh : |betaHat| ≤ |betaHat - beta| + |beta| := by
      simpa only [sub_add_cancel] using abs_add_le (betaHat - beta) beta
    rw [abs_of_nonneg hbeta] at hh
    linarith
  have hahat : |alphaHat| ≤ (1 + u) * alpha := by
    have hh : |alphaHat| ≤ |alphaHat - alpha| + |alpha| := by
      simpa only [sub_add_cancel] using abs_add_le (alphaHat - alpha) alpha
    rw [abs_of_nonneg halpha] at hh
    linarith
  have hbase : |1 + betaHat| ≤ 1 + beta + u * beta := by
    have hh := abs_add_le (1 : ℝ) betaHat
    norm_num only [abs_one] at hh
    nlinarith
  have h0 : |e0| ≤ u * (1 + beta) + u ^ 2 * beta := by
    exact v.one_error.trans (by nlinarith [mul_le_mul_of_nonneg_left hbase hu])
  have h0' : |e0| ≤ 3 * u := by
    nlinarith [mul_le_mul_of_nonneg_left hbeta1 hu,
      mul_le_mul_of_nonneg_left hbeta1 (sq_nonneg u)]
  have hone : |v.onePlusBeta| ≤ 1 + beta + 4 * u := by
    have hh : |v.onePlusBeta| ≤ |e0| + |1 + betaHat| := by
      simpa only [e0, sub_add_cancel] using abs_add_le e0 (1 + betaHat)
    nlinarith [mul_le_mul_of_nonneg_left hbeta1 hu]
  have h1 : ‖e1‖ ≤ u * (1 + beta) * ‖x‖ + 4 * u ^ 2 * ‖x‖ := by
    have hh := v.current_error
    rw [norm_smul, Real.norm_eq_abs] at hh
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hone hX) hu]
  have h1' : ‖e1‖ ≤ 6 * u * ‖x‖ := by
    nlinarith [mul_le_mul_of_nonneg_right huq hX, mul_le_mul_of_nonneg_left hbeta1 (mul_nonneg hu hX)]
  have h2 : ‖e2‖ ≤ u * beta * ‖previous‖ + u ^ 2 * beta * ‖previous‖ := by
    have hh := v.previous_error
    rw [norm_smul, Real.norm_eq_abs] at hh
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbhat hP) hu]
  have h2' : ‖e2‖ ≤ 2 * u * ‖previous‖ := by
    have hh := mul_le_mul_of_nonneg_left hbeta1 (sq_nonneg u)
    have hc := mul_le_mul_of_nonneg_left hbeta1 hu
    nlinarith [mul_le_mul_of_nonneg_right hh hP, mul_le_mul_of_nonneg_right hc hP,
      mul_le_mul_of_nonneg_right huq hP]
  have hraw : ‖(v.currentProduct - v.previousProduct) - Z‖ ≤ u * (10 * ‖x‖ + 3 * ‖previous‖) := by
    have he : (v.currentProduct - v.previousProduct) - Z =
        (betaHat - beta) • (x - previous) + e0 • x + e1 - e2 := by
      dsimp [Z, e0, e1, e2]
      module
    have ht : ‖(v.currentProduct - v.previousProduct) - Z‖ ≤
        |betaHat - beta| * ‖x - previous‖ + |e0| * ‖x‖ + ‖e1‖ + ‖e2‖ := by
      rw [he]
      have hh := (norm_sub_le ((betaHat - beta) • (x - previous) + e0 • x + e1) e2).trans
        (add_le_add ((norm_add_le ((betaHat - beta) • (x - previous) + e0 • x) e1).trans
          (add_le_add (norm_add_le ((betaHat - beta) • (x - previous)) (e0 • x)) le_rfl)) le_rfl)
      simpa only [norm_smul, Real.norm_eq_abs] using hh
    have hh : |betaHat - beta| ≤ u := by nlinarith [mul_le_mul_of_nonneg_left hbeta1 hu]
    have hbnd := mul_le_mul hh (norm_sub_le x previous) (norm_nonneg _) hu
    nlinarith [mul_le_mul_of_nonneg_right h0' hX]
  have h3 : ‖e3‖ ≤ u * ‖Z‖ + u ^ 2 * (10 * ‖x‖ + 3 * ‖previous‖) := by
    have ht : ‖v.currentProduct - v.previousProduct‖ ≤ ‖Z‖ + ‖(v.currentProduct - v.previousProduct) - Z‖ := by
      simpa only [add_sub_cancel] using norm_add_le Z ((v.currentProduct - v.previousProduct) - Z)
    exact v.difference_error.trans (by nlinarith [mul_le_mul_of_nonneg_left ht hu])
  have hZ : ‖Z‖ ≤ 2 * ‖x‖ + ‖previous‖ := by
    have hh := norm_sub_le ((1 + beta) • x) (beta • previous)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hbeta, abs_of_nonneg (by positivity : 0 ≤ 1 + beta)] at hh
    nlinarith [mul_le_mul_of_nonneg_right hbeta1 hX, mul_le_mul_of_nonneg_right hbeta1 hP]
  have hdiff : ‖v.difference - Z‖ ≤ u * (22 * ‖x‖ + 7 * ‖previous‖) := by
    have he : v.difference - Z = e3 + ((v.currentProduct - v.previousProduct) - Z) := by dsimp [e3]; abel
    have ht : ‖v.difference - Z‖ ≤ ‖e3‖ + ‖(v.currentProduct - v.previousProduct) - Z‖ := by rw [he]; exact norm_add_le _ _
    nlinarith [mul_le_mul_of_nonneg_left hZ hu,
      mul_le_mul_of_nonneg_right huq (show 0 ≤ 10 * ‖x‖ + 3 * ‖previous‖ by positivity)]
  have h4 : ‖e4‖ ≤ u * alpha * ‖gradient‖ + u ^ 2 * alpha * ‖gradient‖ := by
    have hh := v.gradient_error
    rw [norm_smul, Real.norm_eq_abs] at hh
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hahat hG) hu]
  have hg : ‖v.gradientProduct - alpha • gradient‖ ≤ 3 * u * alpha * ‖gradient‖ := by
    have he : v.gradientProduct - alpha • gradient = e4 + (alphaHat - alpha) • gradient := by dsimp [e4]; module
    have ht : ‖v.gradientProduct - alpha • gradient‖ ≤ ‖e4‖ + |alphaHat - alpha| * ‖gradient‖ := by
      rw [he]
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le e4 ((alphaHat - alpha) • gradient)
    nlinarith [mul_le_mul_of_nonneg_right ha hG,
      mul_le_mul_of_nonneg_right huq (mul_nonneg halpha hG)]
  have h5 : ‖e5‖ ≤ u * ‖T‖ + u ^ 2 * (22 * ‖x‖ + 7 * ‖previous‖ + 3 * alpha * ‖gradient‖) := by
    have he : (v.difference - v.gradientProduct) - T = (v.difference - Z) - (v.gradientProduct - alpha • gradient) := by dsimp [T]; abel
    have ht : ‖v.difference - v.gradientProduct‖ ≤ ‖T‖ + ‖(v.difference - v.gradientProduct) - T‖ := by
      simpa only [add_sub_cancel] using norm_add_le T ((v.difference - v.gradientProduct) - T)
    have hh : ‖(v.difference - v.gradientProduct) - T‖ ≤ ‖v.difference - Z‖ + ‖v.gradientProduct - alpha • gradient‖ := by
      rw [he]
      exact norm_sub_le _ _
    exact v.result_error.trans (by nlinarith [mul_le_mul_of_nonneg_left ht hu])
  let terms : Fin 8 → E := ![(betaHat - beta) • (x - previous), e0 • x, e1, -e2, e3,
    -(alphaHat - alpha) • gradient, -e4, e5]
  have he : v.result - T = ∑ i : Fin 8, terms i := by
    simp only [terms, Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    dsimp [T, Z, e0, e1, e2, e3, e4, e5]
    module
  have ht : ‖v.result - T‖ ≤ |betaHat - beta| * ‖x - previous‖ + |e0| * ‖x‖ + ‖e1‖ + ‖e2‖ +
      ‖e3‖ + |alphaHat - alpha| * ‖gradient‖ + ‖e4‖ + ‖e5‖ := by
    rw [he]
    have hh := norm_sum_le (Finset.univ : Finset (Fin 8)) terms
    simpa only [terms, Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero, norm_neg, norm_smul, Real.norm_eq_abs, abs_neg, add_assoc] using hh
  have hbnd := mul_le_mul_of_nonneg_right hb (norm_nonneg (x - previous))
  have habnd := mul_le_mul_of_nonneg_right ha hG
  have h0b := mul_le_mul_of_nonneg_right h0 hX
  have htail : beta * ‖x‖ + 4 * ‖x‖ + beta * ‖previous‖ + (10 * ‖x‖ + 3 * ‖previous‖) +
      alpha * ‖gradient‖ + (22 * ‖x‖ + 7 * ‖previous‖ + 3 * alpha * ‖gradient‖) ≤
        100 * (‖x‖ + ‖previous‖ + alpha * ‖gradient‖) := by
    nlinarith [mul_le_mul_of_nonneg_right hbeta1 hX, mul_le_mul_of_nonneg_right hbeta1 hP,
      mul_nonneg halpha hG]
  change ‖v.result - T‖ ≤ _
  nlinarith [mul_le_mul_of_nonneg_left htail (sq_nonneg u)]

end PrefixStep
end
end InexactRealizations.Accuracy
