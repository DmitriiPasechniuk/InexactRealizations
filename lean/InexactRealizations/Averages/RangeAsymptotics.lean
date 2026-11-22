import InexactRealizations.Averages.RangeGaps
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The elementary real asymptotics needed for the exact joint horizon
range. No asymptotic estimate of a method is assumed. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Real Filter Topology

theorem horizon_le_condition (k D n : ℝ) (hk : 0 < k) (hD : 0 ≤ D)
    (hl : 1 ≤ log k) (hquarter : D ≤ k ^ (1 / 4 : ℝ))
    (hn : n ≤ D * k ^ (3 / 4 : ℝ) / sqrt (log k)) : n ≤ k := by
  have hs : 1 ≤ sqrt (log k) := (one_le_sqrt).mpr hl
  calc
    _ ≤ D * k ^ (3 / 4 : ℝ) / sqrt (log k) := hn
    _ ≤ D * k ^ (3 / 4 : ℝ) := div_le_self (mul_nonneg hD (rpow_nonneg hk.le _)) hs
    _ ≤ k ^ (1 / 4 : ℝ) * k ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_right hquarter (rpow_nonneg hk.le _)
    _ = k := by rw [← rpow_add hk]; norm_num

theorem horizon_square_bound (k D n : ℝ) (hk : 0 < k) (hD : 0 ≤ D) (hn : 0 ≤ n)
    (hl : 0 < log k) (hu : n ≤ D * k ^ (3 / 4 : ℝ) / sqrt (log k)) :
    n ^ 2 * log k ≤ D ^ 2 * k * sqrt k := by
  have hmul := (le_div_iff₀ (sqrt_pos.mpr hl)).mp hu
  have hsq := (sq_le_sq₀ (mul_nonneg hn (sqrt_nonneg _)) (mul_nonneg hD (rpow_nonneg hk.le _))).mpr hmul
  have hp : (k ^ (3 / 4 : ℝ)) ^ 2 = k * sqrt k := by
    rw [← rpow_natCast, ← rpow_mul hk.le]
    rw [show (3 / 4 : ℝ) * (2 : ℕ) = 1 + 1 / 2 by norm_num, rpow_add hk, rpow_one, ← sqrt_eq_rpow]
  simpa only [mul_pow, sq_sqrt hl.le, hp, mul_assoc] using hsq

theorem exists_large_parameter (D b : ℝ) (hDb : D ^ 2 < b) :
    ∃ A : ℝ, 0 < A ∧ 0 ≤ 1 - 2 * exp (-A) ∧
      D ^ 2 * (1 + 128 * exp (-A)) < (1 - 2 * exp (-A)) ^ 2 * b := by
  let F := fun z : ℝ ↦ (1 - 2 * z) ^ 2 * b - D ^ 2 * (1 + 128 * z)
  have hc : Continuous F := by fun_prop
  have ht : Tendsto (fun A : ℝ ↦ F (exp (-A))) atTop (𝓝 (b - D ^ 2)) := by
    simpa only [Function.comp_def, F, mul_zero, sub_zero, one_pow, one_mul, add_zero, mul_one] using
      (hc.tendsto (0 : ℝ)).comp tendsto_exp_neg_atTop_nhds_zero
  have hg := ht.eventually (lt_mem_nhds (sub_pos.mpr hDb))
  have he := tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨A, hA, hga, hea⟩ := (eventually_ge_atTop (1 : ℝ) |>.and (hg.and he)).exists
  refine ⟨A, by linarith, by linarith, ?_⟩
  dsimp only [F] at hga
  linarith

theorem eventually_small_gap (A a : ℝ) (ha : 0 < a) :
    ∀ᶠ k : ℝ in atTop, 129 * A ^ 2 * log k < a ^ 2 * (1 - k⁻¹) * sqrt k := by
  have ht : Tendsto (fun k : ℝ ↦ log k / sqrt k) atTop (𝓝 0) := by
    simpa only [sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hr : Tendsto (fun k : ℝ ↦ a ^ 2 * (1 - k⁻¹) - 129 * A ^ 2 * (log k / sqrt k))
      atTop (𝓝 (a ^ 2)) := by
    convert (tendsto_const_nhds.mul (tendsto_const_nhds.sub tendsto_inv_atTop_zero)).sub
      (ht.const_mul (129 * A ^ 2)) using 1; norm_num
  filter_upwards [hr.eventually (lt_mem_nhds (sq_pos_of_pos ha)), eventually_gt_atTop (0 : ℝ)] with k hgap hk
  have hh : 129 * A ^ 2 * log k / sqrt k < a ^ 2 * (1 - k⁻¹) := by
    rw [mul_div_assoc]
    linarith
  exact (div_lt_iff₀ (sqrt_pos.mpr hk)).mp hh

theorem eventually_large_gap (A D b : ℝ)
    (hgap : D ^ 2 * (1 + 128 * exp (-A)) < (1 - 2 * exp (-A)) ^ 2 * b) :
    ∀ᶠ k : ℝ in atTop, D ^ 2 * (1 + 128 * exp (-A)) <
      (1 - 2 * exp (-A)) ^ 2 * b * (1 - k⁻¹) := by
  have ht : Tendsto (fun k : ℝ ↦ (1 - 2 * exp (-A)) ^ 2 * b * (1 - k⁻¹)) atTop
      (𝓝 ((1 - 2 * exp (-A)) ^ 2 * b)) := by
    convert (tendsto_const_nhds.sub tendsto_inv_atTop_zero).const_mul ((1 - 2 * exp (-A)) ^ 2 * b) using 1; norm_num
  exact ht.eventually (lt_mem_nhds hgap)

end
end InexactRealizations.Averages
