import InexactRealizations.Prose.TailFactors
import InexactRealizations.Prose.FlatGrowth
import InexactRealizations.Comparisons.Classical.Bounds
import InexactRealizations.Comparisons.Competitors.Averaging

/-! Uniform bias and impulse bounds for the actual last-half Prefix average. -/
namespace InexactRealizations.Prose.Tail
noncomputable section
open Polynomial Real
open InexactRealizations.Classical
open scoped BigOperators

theorem weights_nonneg (N : ℕ) (j : Fin (N + 1)) : 0 ≤ weights N j := by
  unfold weights
  split_ifs <;> positivity

theorem weights_sum_mul (N : ℕ) (f : Fin (N + 1) → ℝ) :
    (∑ j, weights N j * f j) = ((indices N).card : ℝ)⁻¹ * ∑ j ∈ indices N, f j := by
  simp only [weights, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hs : (Finset.univ.filter fun j : Fin (N + 1) ↦ j ∈ indices N) = indices N := by ext j; simp
  rw [hs, Finset.mul_sum]

theorem terminal_bound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) {x : ℝ} (hx : x ∈ Set.Icc I.mu I.L) :
    |(history I N).terminal.eval x| ≤ 2 * decay I ^ start N := by
  rw [terminal, eval_finsetSum]
  simp only [eval_smul, smul_eq_mul]
  calc
    _ ≤ ∑ j, weights N j * |(I.residual j.val).eval x| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_of_nonneg (weights_nonneg N j)])
    _ ≤ ∑ j, weights N j * (2 * decay I ^ start N) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ indices N
      · have hstart : start N ≤ j.val := by simpa only [indices, Finset.mem_Ici, Fin.le_def] using hj
        have hp := pow_le_pow_of_le_one (decay_mem I).1.le (decay_mem I).2.le hstart
        exact mul_le_mul_of_nonneg_left ((I.residual_abs_le j.val hx).trans
          ((epsilon_decay_bound I j.val).trans (by linarith))) (weights_nonneg N j)
      · simp only [weights, hj, ite_false, zero_mul, le_refl]
    _ = _ := by rw [← Finset.sum_mul, weights_sum, one_mul]

theorem terminal_sq_bound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    (2 * decay I ^ start N) ^ 2 ≤ 4 * decay I ^ N := by
  have hs : N ≤ 2 * start N := by unfold start; omega
  have hh := pow_le_pow_of_le_one (decay_mem I).1.le (decay_mem I).2.le hs
  rw [show 2 * start N = start N * 2 by omega, pow_mul] at hh
  nlinarith

def responseConstant (I : InexactRealizations.Operators.SpectralInterval) : ℝ :=
  (8 / I.delta) * (decay I / (1 - decay I) ^ 2)

theorem responseConstant_pos (I : InexactRealizations.Operators.SpectralInterval) : 0 < responseConstant I :=
  mul_pos (div_pos (by norm_num) I.delta_pos)
    (div_pos (decay_mem I).1 (sq_pos_of_pos (sub_pos.mpr (decay_mem I).2)))

theorem extendedResponse_bound (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (m : ℕ) (s : Fin N) (x : ℝ)
    (hx : x ∈ Set.Icc I.mu I.L) :
    |(extendedResponse I m s).eval x| ≤ (8 / I.delta) * ((m - s.val : ℕ) : ℝ) * decay I ^ (m - s.val) := by
  unfold extendedResponse
  split_ifs with hs
  · have hm : 0 < m := by omega
    have hb := InexactRealizations.Classical.response_bound I m hm ⟨s.val, hs⟩ hx
    have hw := initialWeight_le_one s.val
    have he := scaled_den_le I m (m - s.val) (Nat.sub_le _ _)
    rw [show m - (m - s.val) = s.val by omega] at he
    have hε : 0 < I.epsilon m := one_div_pos.mpr (I.den_pos m)
    have hdelta := I.delta_pos
    have hq : 0 < decay I := (decay_mem I).1
    have hden : 0 < I.den s.val := I.den_pos s.val
    have hlenpos : 0 < (m : ℝ) - s.val := sub_pos.mpr (by exact_mod_cast hs)
    have hlen : ((m - s.val : ℕ) : ℝ) = (m : ℝ) - s.val := Nat.cast_sub hs.le
    apply hb.trans
    unfold InexactRealizations.Classical.responseBound
    have hscale := mul_le_mul_of_nonneg_right he (show 0 ≤ 4 / I.delta * ((m : ℝ) - s.val) by positivity)
    have hw' := mul_le_mul_of_nonneg_left hw
      (show 0 ≤ (4 / I.delta) * (I.epsilon m * I.den s.val) * ((m : ℝ) - s.val) by positivity)
    rw [hlen]
    simp only [div_eq_mul_inv] at hscale hw' ⊢
    nlinarith
  · simp only [eval_zero, abs_zero, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hs), Nat.cast_zero, mul_zero, zero_mul, le_refl]

theorem shifted_geometric_bound (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    (∑ j : Fin (N + 1), (((j.val - s : ℕ) : ℝ) * decay I ^ (j.val - s))) ≤ decay I / (1 - decay I) ^ 2 := by
  let f := fun k : ℕ ↦ (k : ℝ) * decay I ^ k
  have he : (∑ j : Fin (N + 1), f (j.val - s)) = ∑ k ∈ Finset.range (N - s), f (k + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ f (j - s)) (N + 1)]
    have hh := InexactRealizations.Comparisons.Competitors.sum_shifted_tail (fun k ↦ f (k + 1)) N s
    rw [← hh]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : s < j
    · simp only [hj, ite_true, show j - (s + 1) + 1 = j - s by omega]
    · simp only [hj, ite_false, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hj), f, Nat.cast_zero, zero_mul]
  rw [he]
  have hsum := (hasSum_coe_mul_geometric_of_norm_lt_one
    (show ‖decay I‖ < 1 by rw [norm_eq_abs, abs_of_pos (decay_mem I).1]; exact (decay_mem I).2))
  have hh := hsum.summable.sum_le_tsum (Finset.range (N - s + 1))
    (fun k _ ↦ mul_nonneg (Nat.cast_nonneg k) (pow_nonneg (decay_mem I).1.le k))
  rw [hsum.tsum_eq, Finset.sum_range_succ'] at hh
  simpa only [f, Nat.cast_zero, zero_mul, add_zero] using hh

theorem response_bound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (s : Fin N) (x : ℝ)
    (hx : x ∈ Set.Icc I.mu I.L) :
    |((history I N).response s).eval x| ≤ responseConstant I / (indices N).card := by
  rw [response, eval_finsetSum]
  simp only [eval_smul, smul_eq_mul]
  have hd : 0 ≤ 8 / I.delta := (div_pos (by norm_num) I.delta_pos).le
  have hq : 0 < decay I := (decay_mem I).1
  calc
    _ ≤ ∑ j, weights N j * |(extendedResponse I j.val s).eval x| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_of_nonneg (weights_nonneg N j)])
    _ ≤ ∑ j, weights N j * ((8 / I.delta) * ((j.val - s.val : ℕ) : ℝ) * decay I ^ (j.val - s.val)) :=
      Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (extendedResponse_bound I j.val s x hx) (weights_nonneg N j)
    _ = ((indices N).card : ℝ)⁻¹ * (8 / I.delta) *
        ∑ j ∈ indices N, (((j.val - s.val : ℕ) : ℝ) * decay I ^ (j.val - s.val)) := by
      rw [weights_sum_mul, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ((indices N).card : ℝ)⁻¹ * (8 / I.delta) *
        ∑ j : Fin (N + 1), (((j.val - s.val : ℕ) : ℝ) * decay I ^ (j.val - s.val)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hd)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ ↦ by positivity)
    _ ≤ ((indices N).card : ℝ)⁻¹ * (8 / I.delta) * (decay I / (1 - decay I) ^ 2) :=
      mul_le_mul_of_nonneg_left (shifted_geometric_bound I N s.val) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hd)
    _ = _ := by unfold responseConstant; ring

theorem response_bound_horizon (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N) (s : Fin N) (x : ℝ)
    (hx : x ∈ Set.Icc I.mu I.L) : |((history I N).response s).eval x| ≤ 2 * responseConstant I / N := by
  have hc : (N : ℝ) ≤ 2 * ((indices N).card : ℝ) := by rw [indices_card]; exact_mod_cast (show N ≤ 2 * (N + 1 - start N) by unfold start; omega)
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hm : 0 < ((indices N).card : ℝ) := by exact_mod_cast indices_card_pos N
  apply (response_bound I N s x hx).trans
  apply (div_le_div_iff₀ hm hn).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_left hc (responseConstant_pos I).le

end
end InexactRealizations.Prose.Tail
