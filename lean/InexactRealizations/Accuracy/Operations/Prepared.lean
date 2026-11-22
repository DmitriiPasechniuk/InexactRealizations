import InexactRealizations.Accuracy.Compensated

/-! Bounds for a positive prepared scalar rounded once. -/
namespace InexactRealizations.Accuracy
noncomputable section

theorem prepared_inverse {a prepared u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2)
    (hprepared : |prepared - a| ≤ u * a) :
    0 < prepared ∧ |a / prepared - 1| ≤ u + 2 * u ^ 2 ∧ |a / prepared| ≤ 2 := by
  have habs := abs_le.mp hprepared
  have hone : 0 < 1 - u := by linarith
  have hlower : (1 - u) * a ≤ prepared := by nlinarith
  have hp : 0 < prepared := lt_of_lt_of_le (mul_pos hone ha) hlower
  have he : a / prepared - 1 = (a - prepared) / prepared := by field_simp
  have hb : |a / prepared - 1| ≤ u / (1 - u) := by
    rw [he, abs_div, abs_of_pos hp]
    calc
      _ ≤ (u * a) / prepared := div_le_div_of_nonneg_right (by simpa only [abs_sub_comm] using hprepared) hp.le
      _ ≤ (u * a) / ((1 - u) * a) := div_le_div_of_nonneg_left (mul_nonneg hu ha.le) (mul_pos hone ha) hlower
      _ = u / (1 - u) := by field_simp [ha.ne']
  refine ⟨hp, hb.trans ?_, ?_⟩
  · apply (div_le_iff₀ hone).mpr
    nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu2)]
  · rw [abs_of_pos (div_pos ha hp)]
    apply (div_le_iff₀ hp).mpr
    nlinarith

end
end InexactRealizations.Accuracy
