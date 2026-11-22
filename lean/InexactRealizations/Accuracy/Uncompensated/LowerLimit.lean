import InexactRealizations.Accuracy.Uncompensated.LowerResponse
import InexactRealizations.Accuracy.Uncompensated.LowerSeries
import InexactRealizations.Accuracy.Uncompensated.Upper

/-! The asserted positive lower limiting coefficient of L*F_av, with
the finite source sum and its reversed infinite-series envelope linked. 
-/
namespace InexactRealizations.Accuracy.Uncompensated
noncomputable section
open Filter Topology
open scoped BigOperators

def forwardTerm (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ :=
  (((N - 1 - s : ℕ) : ℝ) - 1) * InexactRealizations.Classical.decay I ^ ((N - 1 - s) + 1) *
    (1 - InexactRealizations.Classical.decay I ^ s)

theorem sum_average_indices (f : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    (∑ s : Fin (N - 2), if 2 ≤ s.val then f s.val else 0) =
      ∑ s : Fin N, if s.val + 2 < N ∧ 2 ≤ s.val then f s.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun s ↦ if 2 ≤ s then f s else 0) (N - 2),
    Fin.sum_univ_eq_sum_range (fun s ↦ if s + 2 < N ∧ 2 ≤ s then f s else 0) N]
  calc
    _ = ∑ s ∈ Finset.range (N - 2), if s + 2 < N ∧ 2 ≤ s then f s else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs' := Finset.mem_range.mp hs
      simp only [show s + 2 < N by omega, true_and]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (Nat.sub_le N 2))
      intro s _ hs
      have hs' : ¬s < N - 2 := by simpa only [Finset.mem_range] using hs
      simp only [show ¬(s + 2 < N ∧ 2 ≤ s) by omega, ite_false]

theorem lowerSeries_eq_forward (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    (∑' k : ℕ, lowerTerm I N k) =
      ∑ s : Fin (N - 2), if 2 ≤ s.val then forwardTerm I N s.val else 0 := by
  rw [tsum_eq_sum (s := Finset.range N) (by
    intro k hk
    have hk' : ¬k < N := by simpa only [Finset.mem_range] using hk
    simp only [lowerTerm, show ¬(2 ≤ k ∧ k + 3 ≤ N) by omega, ite_false])]
  rw [← Finset.sum_range_reflect (lowerTerm I N) N, sum_average_indices (forwardTerm I N) hN,
    Fin.sum_univ_eq_sum_range (fun s ↦ if s + 2 < N ∧ 2 ≤ s then forwardTerm I N s else 0) N]
  apply Finset.sum_congr rfl
  intro s hs
  have hsN := Finset.mem_range.mp hs
  have hback : N - 1 - (N - 1 - s) = s := by omega
  have hcond : (2 ≤ N - 1 - s ∧ N - 1 - s + 3 ≤ N) ↔ s + 2 < N ∧ 2 ≤ s := by omega
  simp only [lowerTerm, forwardTerm, hback, hcond]

set_option maxHeartbeats 1000000 in
theorem lowerEnvelope_le (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    lowerPrefactor I N * (∑' k : ℕ, lowerTerm I N k) ≤ I.L * UncompensatedWitness.averageFactor I N := by
  rw [lowerSeries_eq_forward I hN]
  unfold UncompensatedWitness.averageFactor
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs2 : 2 ≤ s.val
  · simp only [hs2, ite_true]
    convert average_response_lower I (s := s.val) hN (by have := s.isLt; omega) using 1
    · unfold forwardTerm
      ring
    · rfl
  · simp only [hs2, ite_false, mul_zero, le_refl]

def limitingLower (I : InexactRealizations.Operators.SpectralInterval) : ℝ :=
  2 * I.L * InexactRealizations.Classical.decay I ^ 3 /
    ((1 - InexactRealizations.Classical.decay I ^ 2) * (1 - InexactRealizations.Classical.decay I) ^ 2 * I.delta)

theorem lowerEnvelope_tendsto (I : InexactRealizations.Operators.SpectralInterval) :
    Tendsto (fun N : ℕ ↦ lowerPrefactor I N * ∑' k : ℕ, lowerTerm I N k) atTop (𝓝 (limitingLower I)) := by
  have hh := ((tendsto_natCast_div_add_atTop (1 : ℝ)).mul_const
    (2 * I.L / ((1 - InexactRealizations.Classical.decay I ^ 2) * I.delta))).mul (lowerSeries_tendsto I)
  convert hh using 1
  · funext N
    unfold lowerPrefactor
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · unfold limitingLower
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem limitingLower_condition (I : InexactRealizations.Operators.SpectralInterval) :
    limitingLower I = (Real.sqrt I.kappa - 1) ^ 2 * Real.sqrt I.kappa / 8 := by
  have he : limitingLower I = limitingUpper I * InexactRealizations.Classical.decay I / 2 := by
    unfold limitingLower limitingUpper
    ring
  rw [he, limitingUpper_condition, decay_eq_condition]
  let t := Real.sqrt I.kappa
  have hk := kappa_gt_one I
  have ht2 : t ^ 2 = I.kappa := Real.sq_sqrt (by linarith : 0 ≤ I.kappa)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  change ((I.kappa - 1) * t / 4) * ((t - 1) / (t + 1)) / 2 = (t - 1) ^ 2 * t / 8
  rw [← ht2]
  field_simp [(show t + 1 ≠ 0 by linarith)]
  ring

theorem averageFactor_eventual_lower (I : InexactRealizations.Operators.SpectralInterval) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop,
      (Real.sqrt I.kappa - 1) ^ 2 * Real.sqrt I.kappa / 8 - eps ≤
        I.L * UncompensatedWitness.averageFactor I N := by
  have hh := (tendsto_order.mp (lowerEnvelope_tendsto I)).1 (limitingLower I - eps) (by linarith)
  filter_upwards [hh, eventually_ge_atTop 2] with N hbound hN
  rw [← limitingLower_condition]
  exact hbound.le.trans (lowerEnvelope_le I hN)

end
end InexactRealizations.Accuracy.Uncompensated
