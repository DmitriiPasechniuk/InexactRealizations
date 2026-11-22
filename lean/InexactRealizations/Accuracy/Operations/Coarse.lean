import InexactRealizations.Accuracy.Operations.Query
import InexactRealizations.Accuracy.Operations.Recovery
import InexactRealizations.Accuracy.Operations.Blend
import InexactRealizations.Accuracy.Operations.Prefix
import InexactRealizations.Accuracy.LocalBounds

/-! Dimension-independent coarse bounds for the finite operation graph.
They are used only for uniform perturbation/remainder control; sharp
first-order coefficients come from the operation lemmas themselves. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem QueryStep.coarse {x b : E} {prepared u theta S : ℝ}
    (v : QueryStep x b prepared u) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1) (hp : |prepared - theta| ≤ u * theta)
    (hS : 0 ≤ S) (hx : ‖x‖ ≤ S) (hb : ‖b‖ ≤ S) :
    ‖v.result - (b + theta • (x - b))‖ ≤ 1000 * u * S ∧ ‖v.result‖ ≤ 2000 * S := by
  have hd : ‖x - b‖ ≤ 2 * S := (norm_sub_le _ _).trans (by linarith)
  have hq : ‖b + theta • (x - b)‖ ≤ S := by
    have he : b + theta • (x - b) = theta • x + (1 - theta) • b := by module
    rw [he]
    have hh := norm_add_le (theta • x) ((1 - theta) • b)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg htheta, abs_of_nonneg (sub_nonneg.mpr htheta1)] at hh
    nlinarith [mul_le_mul_of_nonneg_left hx htheta, mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr htheta1)]
  have hh := v.local_error hu hu1 htheta htheta1 hp
  have ht : (1 - theta) * ‖b‖ + 3 * theta * ‖x - b‖ + ‖b + theta • (x - b)‖ ≤ 8 * S := by
    nlinarith [mul_le_mul (show 1 - theta ≤ 1 by linarith) hb (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1),
      mul_le_mul htheta1 hd (norm_nonneg _) zero_le_one]
  have hsum : ‖b‖ + ‖x - b‖ ≤ 3 * S := by linarith
  have huq : u ^ 2 ≤ u := by nlinarith
  have he : ‖v.result - (b + theta • (x - b))‖ ≤ 1000 * u * S := by
    nlinarith [mul_le_mul_of_nonneg_left ht hu, mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 100 * u ^ 2),
      mul_le_mul_of_nonneg_right huq hS]
  refine ⟨he, ?_⟩
  have hn : ‖v.result‖ ≤ ‖v.result - (b + theta • (x - b))‖ + ‖b + theta • (x - b)‖ := by
    simpa only [sub_add_cancel] using norm_add_le (v.result - (b + theta • (x - b))) (b + theta • (x - b))
  nlinarith [mul_le_mul_of_nonneg_right hu1 hS]

theorem RecoveryStep.coarse {g previous : E} {prepared u theta S A : ℝ}
    (v : RecoveryStep g previous prepared u) (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) (hp : |prepared - theta| ≤ u * theta)
    (hS : 0 ≤ S) (hA : 1 ≤ A) (hi : theta⁻¹ ≤ A) (hg : ‖g‖ ≤ S) (hb : ‖previous‖ ≤ S) :
    ‖v.result - (previous + theta⁻¹ • (g - previous))‖ ≤ 1000 * u * A * S ∧
      ‖v.result‖ ≤ 2000 * A * S := by
  have hd : ‖g - previous‖ ≤ 2 * S := (norm_sub_le _ _).trans (by linarith)
  have hq : theta * ‖previous + theta⁻¹ • (g - previous)‖ ≤ 3 * S := by
    have hh := norm_add_le previous (theta⁻¹ • (g - previous))
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htheta] at hh
    have hc := mul_le_mul_of_nonneg_left hh htheta.le
    have hid : theta * theta⁻¹ = 1 := mul_inv_cancel₀ htheta.ne'
    have hb' := mul_le_mul_of_nonneg_left hb htheta.le
    have hb'' := mul_le_mul_of_nonneg_right htheta1 hS
    nlinarith
  have hh := v.local_error hu hu2 htheta hp
  have hu1 : u ≤ 1 := by linarith
  have huq : u ^ 2 ≤ u := by nlinarith
  have hscaled : theta * ‖v.result - (previous + theta⁻¹ • (g - previous))‖ ≤ 1000 * u * S := by
    nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 3 * u + 100 * u ^ 2),
      mul_le_mul_of_nonneg_left hq hu, mul_le_mul_of_nonneg_right huq hS]
  have he : ‖v.result - (previous + theta⁻¹ • (g - previous))‖ ≤ 1000 * u * A * S := by
    have hb' := mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr htheta.le)
    have hc := mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ 1000 * u * S)
    rw [← mul_assoc, inv_mul_cancel₀ htheta.ne', one_mul] at hb'
    nlinarith
  have hq' : ‖previous + theta⁻¹ • (g - previous)‖ ≤ 3 * A * S := by
    have hh := mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr htheta.le)
    rw [← mul_assoc, inv_mul_cancel₀ htheta.ne', one_mul] at hh
    nlinarith [mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ 3 * S)]
  refine ⟨he, ?_⟩
  have hn : ‖v.result‖ ≤ ‖v.result - (previous + theta⁻¹ • (g - previous))‖ + ‖previous + theta⁻¹ • (g - previous)‖ := by
    simpa only [sub_add_cancel] using norm_add_le (v.result - (previous + theta⁻¹ • (g - previous))) (previous + theta⁻¹ • (g - previous))
  nlinarith [mul_le_mul_of_nonneg_right hu1 (by positivity : 0 ≤ A * S)]

theorem BlendStep.coarse {x previous : E} {prepared u phi S : ℝ}
    (v : BlendStep x previous prepared u) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hphi : 0 ≤ phi) (hphi1 : phi ≤ 1) (hp : |prepared - phi| ≤ u * phi)
    (hS : 0 ≤ S) (hx : ‖x‖ ≤ S) (hb : ‖previous‖ ≤ S) :
    ‖v.result - (previous + phi • (x - previous))‖ ≤ 100 * u * S ∧ ‖v.result‖ ≤ 200 * S := by
  have hd : ‖x - previous‖ ≤ 2 * S := (norm_sub_le _ _).trans (by linarith)
  have hq : ‖previous + phi • (x - previous)‖ ≤ S := by
    have he : previous + phi • (x - previous) = phi • x + (1 - phi) • previous := by module
    rw [he]
    have hh := norm_add_le (phi • x) ((1 - phi) • previous)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hphi, abs_of_nonneg (sub_nonneg.mpr hphi1)] at hh
    nlinarith [mul_le_mul_of_nonneg_left hx hphi, mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hphi1)]
  have hh := v.local_error hu hu1 hphi hp
  have huq : u ^ 2 ≤ u := by nlinarith
  have hb' := mul_le_mul hphi1 hd (norm_nonneg _) zero_le_one
  have he : ‖v.result - (previous + phi • (x - previous))‖ ≤ 100 * u * S := by
    nlinarith [mul_le_mul_of_nonneg_left hq hu,
      mul_le_mul_of_nonneg_left hb' (by positivity : 0 ≤ 3 * u + 11 * u ^ 2),
      mul_le_mul_of_nonneg_right huq hS]
  refine ⟨he, ?_⟩
  have hn : ‖v.result‖ ≤ ‖v.result - (previous + phi • (x - previous))‖ + ‖previous + phi • (x - previous)‖ := by
    simpa only [sub_add_cancel] using norm_add_le (v.result - (previous + phi • (x - previous))) (previous + phi • (x - previous))
  nlinarith [mul_le_mul_of_nonneg_right hu1 hS]

end
end InexactRealizations.Accuracy
