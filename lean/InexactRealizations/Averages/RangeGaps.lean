import InexactRealizations.Averages.ScaledComparison

/-! Two finite numeric comparisons for the joint horizon proof. -/
namespace InexactRealizations.Averages
noncomputable section
open Real

theorem condition_gt_one (I : InexactRealizations.Operators.SpectralInterval) : 1 < I.kappa :=
  (lt_div_iff₀ I.mu_pos).mpr (by simpa [InexactRealizations.Operators.SpectralInterval.kappa] using I.mu_lt_L)

theorem large_range_gap (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (A D b : ℝ) (hD : 0 < D) (hb : 0 ≤ b) (hlog : 0 < log I.kappa)
    (ha : 0 ≤ 1 - 2 * exp (-A)) (hNA : A * sqrt I.kappa ≤ (N : ℝ))
    (hbN : b ≤ inverseSquareSum N)
    (hupper : (N : ℝ) ^ 2 * log I.kappa ≤ D ^ 2 * I.kappa * sqrt I.kappa)
    (hgap : D ^ 2 * (1 + 128 * exp (-A)) <
      (1 - 2 * exp (-A)) ^ 2 * b * (1 - I.kappa⁻¹)) :
    (1 + 128 * exp (-((N : ℝ) / sqrt I.kappa))) * normalizedLimit I < normalizedLower I N := by
  have hk := condition_gt_one I
  have hs : 0 < sqrt I.kappa := sqrt_pos.mpr (lt_trans zero_lt_one hk)
  have hs2 := sq_sqrt (lt_trans zero_lt_one hk).le
  have hd : 0 < 1 - I.kappa⁻¹ := sub_pos.mpr ((inv_lt_one₀ (lt_trans zero_lt_one hk)).mpr hk)
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hx : A ≤ (N : ℝ) / sqrt I.kappa := (le_div_iff₀ hs).mpr hNA
  have he : exp (-((N : ℝ) / sqrt I.kappa)) ≤ exp (-A) := exp_le_exp.mpr (neg_le_neg hx)
  have heps : 1 - 2 * exp (-A) ≤ 1 - I.epsilon N := by linarith [epsilon_exp_bound I N]
  have hr : sqrt I.kappa * log I.kappa / D ^ 2 ≤ I.kappa ^ 2 / (N : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hD) (sq_pos_of_pos hn)).mpr
    calc
      _ = sqrt I.kappa * ((N : ℝ) ^ 2 * log I.kappa) := by ring
      _ ≤ sqrt I.kappa * (D ^ 2 * I.kappa * sqrt I.kappa) := mul_le_mul_of_nonneg_left hupper hs.le
      _ = D ^ 2 * I.kappa * (sqrt I.kappa) ^ 2 := by ring
      _ = _ := by rw [hs2]; ring
  have hf : (1 + 128 * exp (-A)) / (1 - I.kappa⁻¹) < (1 - 2 * exp (-A)) ^ 2 * b / D ^ 2 :=
    (div_lt_div_iff₀ hd (sq_pos_of_pos hD)).mpr (by simpa only [mul_comm] using hgap)
  have hf' := mul_lt_mul_of_pos_right hf (mul_pos hs hlog)
  calc
    _ ≤ (1 + 128 * exp (-A)) * normalizedLimit I :=
      mul_le_mul_of_nonneg_right (by linarith : 1 + 128 * exp (-((N : ℝ) / sqrt I.kappa)) ≤ 1 + 128 * exp (-A)) (normalized_limit_pos I).le
    _ < (1 - 2 * exp (-A)) ^ 2 * b * (sqrt I.kappa * log I.kappa / D ^ 2) := by
      simpa only [normalizedLimit, div_mul_eq_mul_div, mul_div_assoc, mul_assoc, mul_comm, mul_left_comm] using hf'
    _ ≤ (1 - 2 * exp (-A)) ^ 2 * b * (I.kappa ^ 2 / (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg (sq_nonneg _) hb)
    _ ≤ _ := normalizedLower_bound I N _ b ha heps hb hbN

theorem small_range_gap (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (A a : ℝ) (hA : 0 < A) (ha : 0 ≤ a) (hae : a ≤ 1 - I.epsilon N)
    (hNA : (N : ℝ) ≤ A * sqrt I.kappa)
    (hgap : 129 * A ^ 2 * log I.kappa < a ^ 2 * (1 - I.kappa⁻¹) * sqrt I.kappa) :
    (1 + 128 * exp (-((N : ℝ) / sqrt I.kappa))) * normalizedLimit I < normalizedLower I N := by
  have hk := condition_gt_one I
  have hs : 0 < sqrt I.kappa := sqrt_pos.mpr (lt_trans zero_lt_one hk)
  have hs2 := sq_sqrt (lt_trans zero_lt_one hk).le
  have hd : 0 < 1 - I.kappa⁻¹ := sub_pos.mpr ((inv_lt_one₀ (lt_trans zero_lt_one hk)).mpr hk)
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have he : exp (-((N : ℝ) / sqrt I.kappa)) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg hn.le hs.le))
  have hNsq : (N : ℝ) ^ 2 ≤ A ^ 2 * I.kappa := by
    have hh := (sq_le_sq₀ hn.le (mul_pos hA hs).le).mpr hNA
    simpa only [mul_pow, hs2] using hh
  have hr : I.kappa / A ^ 2 ≤ I.kappa ^ 2 / (N : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hA) (sq_pos_of_pos hn)).mpr
    have hh := mul_le_mul_of_nonneg_left hNsq (lt_trans zero_lt_one hk).le
    nlinarith
  have hf : 129 * normalizedLimit I < a ^ 2 * I.kappa / A ^ 2 := by
    unfold normalizedLimit
    rw [← mul_div_assoc]
    apply (div_lt_div_iff₀ hd (sq_pos_of_pos hA)).mpr
    have hh := mul_lt_mul_of_pos_right hgap hs
    have heq : a ^ 2 * (1 - I.kappa⁻¹) * sqrt I.kappa * sqrt I.kappa = a ^ 2 * I.kappa * (1 - I.kappa⁻¹) := by
      calc
        _ = a ^ 2 * (1 - I.kappa⁻¹) * (sqrt I.kappa) ^ 2 := by ring
        _ = _ := by rw [hs2]; ring
    rw [heq] at hh
    convert hh using 1; ring
  calc
    _ ≤ 129 * normalizedLimit I := mul_le_mul_of_nonneg_right (by linarith) (normalized_limit_pos I).le
    _ < a ^ 2 * (I.kappa / A ^ 2) := by simpa only [mul_div_assoc] using hf
    _ ≤ a ^ 2 * (I.kappa ^ 2 / (N : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hr (sq_nonneg a)
    _ ≤ _ := by simpa only [mul_one] using normalizedLower_bound I N a 1 ha hae zero_le_one (inverseSquareSum_one_le N hN)

end
end InexactRealizations.Averages
