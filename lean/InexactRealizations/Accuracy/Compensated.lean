import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The literal compensated component update. The hypotheses
below bound only the rounding of individual printed operations. In
particular, no estimate on the final average is supplied as a hypothesis. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem componentwise_relative_norm {d : Type*} [Fintype d]
    (out exact : EuclideanSpace ℝ d) {u : ℝ} (hu : 0 ≤ u)
    (herr : ∀ i, |out i - exact i| ≤ u * |exact i|) :
    ‖out - exact‖ ≤ u * ‖exact‖ := by
  have hsq : ‖out - exact‖ ^ 2 ≤ (u * ‖exact‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := (sq_le_sq₀ (abs_nonneg (out i - exact i))
      (mul_nonneg hu (abs_nonneg (exact i)))).mpr (herr i)
    simpa only [PiLp.sub_apply, sq_abs, mul_pow] using hh
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hu (norm_nonneg _))).mp hsq

omit [NormedSpace ℝ E] in
theorem rounded_approx {u A B M₀ M₁ : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hB : 0 ≤ B)
    (out v z : E) (herr : ‖out - v‖ ≤ u * ‖v‖)
    (hv : ‖v - z‖ ≤ u * A + u ^ 2 * B) (hz : ‖z‖ ≤ M₀ + u * M₁) :
    ‖out - z‖ ≤ u * (M₀ + A) + u ^ 2 * (M₁ + A + 2 * B) := by
  have hsize : ‖v‖ ≤ M₀ + u * M₁ + (u * A + u ^ 2 * B) := by
    calc
      _ ≤ ‖z‖ + ‖v - z‖ := by simpa only [add_sub_cancel] using norm_add_le z (v - z)
      _ ≤ _ := add_le_add hz hv
  calc
    _ ≤ ‖out - v‖ + ‖v - z‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (out - v) (v - z)
    _ ≤ u * (M₀ + u * M₁ + (u * A + u ^ 2 * B)) + (u * A + u ^ 2 * B) :=
      add_le_add (herr.trans (mul_le_mul_of_nonneg_left hsize hu)) hv
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg u) (mul_nonneg hB (sub_nonneg.mpr hu1))]

structure CompensatedStep (x average correction : E) (phi prepared u : ℝ) where
  difference : E
  corrected : E
  product : E
  a : E
  c : E
  d : E
  nextCorrection : E
  difference_error : ‖difference - (x - average)‖ ≤ u * ‖x - average‖
  corrected_error : ‖corrected - (difference - correction)‖ ≤ u * ‖difference - correction‖
  product_error : ‖product - prepared • corrected‖ ≤ u * ‖prepared • corrected‖
  a_error : ‖a - (correction + product)‖ ≤ u * ‖correction + product‖
  c_error : ‖c - (average + a)‖ ≤ u * ‖average + a‖
  d_error : ‖d - (c - average)‖ ≤ u * ‖c - average‖
  correction_error : ‖nextCorrection - (a - d)‖ ≤ u * ‖a - d‖

namespace CompensatedStep
variable {x average correction : E} {phi prepared u : ℝ}

def total (v : CompensatedStep x average correction phi prepared u) : E := v.c + v.nextCorrection

set_option maxHeartbeats 2000000 in
theorem average_error (v : CompensatedStep x average correction phi prepared u)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hphi : 0 ≤ phi) (hphi1 : phi ≤ 1)
    (hprepared : |prepared - phi| ≤ u * phi) {K : ℝ} (hK : 0 ≤ K)
    (hcorr : ‖correction‖ ≤ u * K) :
    ‖v.total - ((average + correction) + phi • (x - (average + correction)))‖ ≤
      6 * u * phi * ‖x - (average + correction)‖ +
        200 * u ^ 2 * (‖x - (average + correction)‖ + K + ‖average‖) := by
  let D := x - (average + correction)
  let q := ‖D‖
  have hq : 0 ≤ q := norm_nonneg D
  have hphiD : phi * q ≤ q := by nlinarith
  have hu2 : u ^ 2 ≤ u := by nlinarith
  have hD : x - average = D + correction := by dsimp [D]; abel
  have h1 : ‖(v.difference - correction) - D‖ ≤ u * q + u ^ 2 * K := by
    have he : (v.difference - correction) - D = v.difference - (x - average) := by rw [hD]; abel
    rw [he]
    calc
      _ ≤ u * ‖x - average‖ := v.difference_error
      _ ≤ u * (q + u * K) := by
        apply mul_le_mul_of_nonneg_left _ hu
        rw [hD]
        exact (norm_add_le _ _).trans (add_le_add_right hcorr q)
      _ = _ := by ring
  have h2 := rounded_approx hu hu1 hK v.corrected (v.difference - correction) D
    v.corrected_error h1 (show ‖D‖ ≤ q + u * 0 by simp [q])
  have h2' : ‖v.corrected - D‖ ≤ u * (2 * q) + u ^ 2 * (q + 2 * K) := by
    convert h2 using 1
    ring
  have hs : ‖prepared • v.corrected - phi • v.corrected‖ ≤ u * ‖phi • v.corrected‖ := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs, abs_of_nonneg hphi]
    nlinarith [mul_le_mul_of_nonneg_right hprepared (norm_nonneg v.corrected)]
  have hscaled : ‖phi • v.corrected - phi • D‖ ≤
      u * (2 * phi * q) + u ^ 2 * (phi * (q + 2 * K)) := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hphi]
    nlinarith [mul_le_mul_of_nonneg_left h2' hphi]
  have h3 := rounded_approx hu hu1 (mul_nonneg hphi (by positivity : 0 ≤ q + 2 * K))
    (prepared • v.corrected) (phi • v.corrected) (phi • D) hs hscaled
    (show ‖phi • D‖ ≤ phi * q + u * 0 by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hphi, q])
  have h3' : ‖prepared • v.corrected - phi • D‖ ≤
      u * (3 * phi * q) + u ^ 2 * (phi * (4 * q + 4 * K)) := by
    convert h3 using 1
    ring
  have h4 := rounded_approx hu hu1 (mul_nonneg hphi (by positivity : 0 ≤ 4 * q + 4 * K))
    v.product (prepared • v.corrected) (phi • D) v.product_error h3'
    (show ‖phi • D‖ ≤ phi * q + u * 0 by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hphi, q])
  have h4' : ‖(correction + v.product) - (correction + phi • D)‖ ≤
      u * (4 * phi * q) + u ^ 2 * (phi * (11 * q + 8 * K)) := by
    simpa only [add_sub_add_left_eq_sub] using (show ‖v.product - phi • D‖ ≤
      u * (4 * phi * q) + u ^ 2 * (phi * (11 * q + 8 * K)) by
        convert h4 using 1
        ring)
  have hz : ‖correction + phi • D‖ ≤ phi * q + u * K := by
    calc
      _ ≤ ‖correction‖ + ‖phi • D‖ := norm_add_le _ _
      _ ≤ _ := by simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hphi, q, add_comm] using
        add_le_add_right hcorr ‖phi • D‖
  have h5 := rounded_approx hu hu1 (mul_nonneg hphi (by positivity : 0 ≤ 11 * q + 8 * K))
    v.a (correction + v.product) (correction + phi • D) v.a_error h4' hz
  have h5' : ‖v.a - (correction + phi • D)‖ ≤
      5 * u * phi * q + u ^ 2 * (26 * q + 17 * K) := by
    have hb : K + 4 * phi * q + 2 * (phi * (11 * q + 8 * K)) ≤ 26 * q + 17 * K := by
      nlinarith [mul_le_mul_of_nonneg_right hphi1 hK]
    nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg u)]
  have ha : ‖v.a‖ ≤ phi * q + u * (31 * q + 18 * K) := by
    have ht : ‖v.a‖ ≤ ‖v.a - (correction + phi • D)‖ + ‖correction + phi • D‖ := by
      simpa only [sub_add_cancel] using norm_add_le (v.a - (correction + phi • D)) (correction + phi • D)
    have hb := mul_le_mul_of_nonneg_right hu2 (show 0 ≤ 26 * q + 17 * K by positivity)
    nlinarith [hz, h5', mul_le_mul_of_nonneg_left hphiD hu]
  let ec := v.c - (average + v.a)
  let ed := v.d - (v.c - average)
  let ef := v.nextCorrection - (v.a - v.d)
  have hec : ‖ec‖ ≤ u * (‖average‖ + phi * q) + u ^ 2 * (31 * q + 18 * K) := by
    exact v.c_error.trans (by nlinarith [mul_le_mul_of_nonneg_left ((norm_add_le average v.a).trans
      (add_le_add_right ha ‖average‖)) hu])
  have hed : ‖ed‖ ≤ u * phi * q + u ^ 2 * (2 * (31 * q + 18 * K) + ‖average‖ + phi * q) := by
    have ht : ‖v.c - average‖ ≤ ‖v.a‖ + ‖ec‖ := by
      have he : v.c - average = v.a + ec := by dsimp [ec]; abel
      rw [he]
      exact norm_add_le _ _
    have hb := mul_le_mul_of_nonneg_right hu2 (show 0 ≤ 31 * q + 18 * K by positivity)
    exact v.d_error.trans (by nlinarith [mul_le_mul_of_nonneg_left ht hu])
  have hef : ‖ef‖ ≤ u ^ 2 * (2 * ‖average‖ + 3 * phi * q + 3 * (31 * q + 18 * K)) := by
    have ht : ‖v.a - v.d‖ ≤ ‖ec‖ + ‖ed‖ := by
      have he : v.a - v.d = -(ec + ed) := by dsimp [ec, ed]; abel
      rw [he, norm_neg]
      exact norm_add_le _ _
    have hb := mul_le_mul_of_nonneg_right hu2
      (show 0 ≤ 3 * (31 * q + 18 * K) + ‖average‖ + phi * q by positivity)
    exact v.correction_error.trans (by nlinarith [mul_le_mul_of_nonneg_left ht hu])
  have he : v.total - ((average + correction) + phi • D) =
      (v.a - (correction + phi • D)) - ed + ef := by dsimp [total, ed, ef]; abel
  change ‖v.total - ((average + correction) + phi • D)‖ ≤ _
  rw [he]
  have ht := (norm_add_le (v.a - (correction + phi • D) - ed) ef).trans
    (add_le_add_left (norm_sub_le _ _) ‖ef‖)
  have hb : 26 * q + 17 * K + (2 * (31 * q + 18 * K) + ‖average‖ + phi * q) +
      (2 * ‖average‖ + 3 * phi * q + 3 * (31 * q + 18 * K)) ≤ 200 * (q + K + ‖average‖) := by
    nlinarith [norm_nonneg average]
  nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg u)]

end CompensatedStep
end
end InexactRealizations.Accuracy
