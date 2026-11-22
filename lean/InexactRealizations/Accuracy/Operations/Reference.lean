import InexactRealizations.Accuracy.Operations.CoarseState
import InexactRealizations.Accuracy.Bounds.State

/-! Uniform replacement of actual operands by reference operands in the
first-order local bounds. All resulting second-order constants are explicit;
no smoothness assumption on the rounding selection is made. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem norm_from_distance {x y : E} {D : ℝ} (h : ‖x - y‖ ≤ D) : ‖x‖ ≤ ‖y‖ + D := by
  exact (show ‖x‖ ≤ ‖y‖ + ‖x - y‖ by simpa only [add_sub_cancel] using norm_add_le y (x - y)).trans
    (add_le_add le_rfl h)

omit [NormedSpace ℝ E] in
theorem distance_from_distances {x y x0 y0 : E} {D F : ℝ}
    (hx : ‖x - x0‖ ≤ D) (hy : ‖y - y0‖ ≤ F) : ‖x - y‖ ≤ ‖x0 - y0‖ + D + F := by
  have he : (x - y) - (x0 - y0) = (x - x0) - (y - y0) := by abel
  have hh : ‖(x - y) - (x0 - y0)‖ ≤ D + F := by
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hx hy)
  simpa only [add_assoc] using norm_from_distance hh

set_option maxHeartbeats 1000000 in
theorem QueryStep.reference_error {x b x0 b0 : E} {prepared u theta eps K S : ℝ}
    (v : QueryStep x b prepared u) (hu : 0 ≤ u) (hu1 : u ≤ 1) (hue : u ≤ eps)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1) (hp : |prepared - theta| ≤ u * theta)
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hx : ‖x - x0‖ ≤ eps * K) (hb : ‖b - b0‖ ≤ eps * K)
    (hxs : ‖x‖ ≤ S) (hbs : ‖b‖ ≤ S) :
    ‖v.result - (b + theta • (x - b))‖ ≤
      u * ((1 - theta) * ‖b0‖ + 3 * theta * ‖x0 - b0‖ + ‖b0 + theta • (x0 - b0)‖) +
        eps ^ 2 * (7 * K + 300 * S) := by
  have heps : 0 ≤ eps := hu.trans hue
  have hB := norm_from_distance hb
  have hD := distance_from_distances hx hb
  have hQ := norm_from_distance (Execution.affine_close theta htheta htheta1 x b x0 b0 (eps * K) hx hb)
  have hlead : (1 - theta) * ‖b‖ + 3 * theta * ‖x - b‖ + ‖b + theta • (x - b)‖ ≤
      (1 - theta) * ‖b0‖ + 3 * theta * ‖x0 - b0‖ + ‖b0 + theta • (x0 - b0)‖ + 7 * eps * K := by
    nlinarith [mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr htheta1),
      mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 3 * theta),
      mul_le_mul_of_nonneg_right htheta1 (mul_nonneg heps hK)]
  have hsize : ‖b‖ + ‖x - b‖ ≤ 3 * S := by nlinarith [norm_sub_le x b]
  have hh := v.local_error hu hu1 htheta htheta1 hp
  have hsq : u ^ 2 ≤ eps ^ 2 := (sq_le_sq₀ hu heps).mpr hue
  have hmul : u * eps ≤ eps ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hue) heps]
  nlinarith [mul_le_mul_of_nonneg_left hlead hu,
    mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ 100 * u ^ 2),
    mul_le_mul_of_nonneg_right hsq hS, mul_le_mul_of_nonneg_right hmul hK]

set_option maxHeartbeats 1000000 in
theorem BlendStep.reference_error {x b x0 b0 : E} {prepared u phi eps K S : ℝ}
    (v : BlendStep x b prepared u) (hu : 0 ≤ u) (hu1 : u ≤ 1) (hue : u ≤ eps)
    (hphi : 0 ≤ phi) (hphi1 : phi ≤ 1) (hp : |prepared - phi| ≤ u * phi)
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hx : ‖x - x0‖ ≤ eps * K) (hb : ‖b - b0‖ ≤ eps * K)
    (hxs : ‖x‖ ≤ S) (hbs : ‖b‖ ≤ S) :
    ‖v.result - (b + phi • (x - b))‖ ≤
      u * (‖b0 + phi • (x0 - b0)‖ + 3 * phi * ‖x0 - b0‖) + eps ^ 2 * (7 * K + 22 * S) := by
  have heps : 0 ≤ eps := hu.trans hue
  have hD := distance_from_distances hx hb
  have hQ := norm_from_distance (Execution.affine_close phi hphi hphi1 x b x0 b0 (eps * K) hx hb)
  have hlead : ‖b + phi • (x - b)‖ + 3 * phi * ‖x - b‖ ≤
      ‖b0 + phi • (x0 - b0)‖ + 3 * phi * ‖x0 - b0‖ + 7 * eps * K := by
    nlinarith [mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 3 * phi),
      mul_le_mul_of_nonneg_right hphi1 (mul_nonneg heps hK)]
  have hdsize : ‖x - b‖ ≤ 2 * S := (norm_sub_le x b).trans (by linarith)
  have hsize : phi * ‖x - b‖ ≤ 2 * S := by
    have hh := mul_le_mul_of_nonneg_right hphi1 (norm_nonneg (x - b))
    nlinarith
  have hh := v.local_error hu hu1 hphi hp
  have hsq : u ^ 2 ≤ eps ^ 2 := (sq_le_sq₀ hu heps).mpr hue
  have hmul : u * eps ≤ eps ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hue) heps]
  nlinarith [mul_le_mul_of_nonneg_left hlead hu,
    mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ 11 * u ^ 2),
    mul_le_mul_of_nonneg_right hsq hS, mul_le_mul_of_nonneg_right hmul hK]

set_option maxHeartbeats 1000000 in
theorem RecoveryStep.reference_error {g b g0 b0 : E} {prepared u theta eps K S : ℝ}
    (v : RecoveryStep g b prepared u) (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (hue : u ≤ eps)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) (hp : |prepared - theta| ≤ u * theta)
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hg : ‖g - g0‖ ≤ eps * K) (hb : ‖b - b0‖ ≤ eps * K)
    (hgs : ‖g‖ ≤ S) (hbs : ‖b‖ ≤ S) :
    theta * ‖v.result - (b + theta⁻¹ • (g - b))‖ ≤
      u * (3 * ‖g0 - b0‖ + theta * ‖b0 + theta⁻¹ • (g0 - b0)‖) +
        eps ^ 2 * (9 * K + 200 * S) := by
  have heps : 0 ≤ eps := hu.trans hue
  have hD := distance_from_distances hg hb
  have hQ : theta * ‖b + theta⁻¹ • (g - b)‖ ≤
      theta * ‖b0 + theta⁻¹ • (g0 - b0)‖ + 3 * eps * K := by
    have he : (b + theta⁻¹ • (g - b)) - (b0 + theta⁻¹ • (g0 - b0)) =
        (b - b0) + theta⁻¹ • ((g - g0) - (b - b0)) := by module
    have ht := norm_add_le (b - b0) (theta⁻¹ • ((g - g0) - (b - b0)))
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htheta] at ht
    have hd : ‖(g - g0) - (b - b0)‖ ≤ 2 * eps * K := (norm_sub_le _ _).trans (by linarith)
    have hb' := mul_le_mul_of_nonneg_left ht htheta.le
    have hc : theta * (theta⁻¹ * ‖(g - g0) - (b - b0)‖) = ‖(g - g0) - (b - b0)‖ := by
      rw [← mul_assoc, mul_inv_cancel₀ htheta.ne', one_mul]
    have hdiff : theta * ‖(b + theta⁻¹ • (g - b)) - (b0 + theta⁻¹ • (g0 - b0))‖ ≤ 3 * eps * K := by
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_left hb htheta.le,
        mul_le_mul_of_nonneg_right htheta1 (mul_nonneg heps hK)]
    have hn := norm_from_distance (show
      ‖(b + theta⁻¹ • (g - b)) - (b0 + theta⁻¹ • (g0 - b0))‖ ≤
        ‖(b + theta⁻¹ • (g - b)) - (b0 + theta⁻¹ • (g0 - b0))‖ from le_rfl)
    nlinarith [mul_le_mul_of_nonneg_left hn htheta.le]
  have hlead : 3 * ‖g - b‖ + theta * ‖b + theta⁻¹ • (g - b)‖ ≤
      3 * ‖g0 - b0‖ + theta * ‖b0 + theta⁻¹ • (g0 - b0)‖ + 9 * eps * K := by linarith
  have hsize : ‖g - b‖ ≤ 2 * S := (norm_sub_le _ _).trans (by linarith)
  have hh := v.local_error hu hu2 htheta hp
  have hsq : u ^ 2 ≤ eps ^ 2 := (sq_le_sq₀ hu heps).mpr hue
  have hmul : u * eps ≤ eps ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hue) heps]
  nlinarith [mul_le_mul_of_nonneg_left hlead hu,
    mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ 100 * u ^ 2),
    mul_le_mul_of_nonneg_right hsq hS, mul_le_mul_of_nonneg_right hmul hK]

end
end InexactRealizations.Accuracy
