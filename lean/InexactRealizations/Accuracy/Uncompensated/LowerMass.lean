import InexactRealizations.Accuracy.Uncompensated.Mass
import InexactRealizations.Accuracy.Estimates.Decay

/-! Lower geometric envelope of the stored mass. The initial even-parity
mass can vanish, so the lower bound starts with factor 1-q^s. 
-/
namespace InexactRealizations.Accuracy.Uncompensated
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced

set_option maxHeartbeats 1000000 in
theorem mass_lower_geometric (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (s : ℕ) (hs : s + 2 < N) :
    (2 / ((N : ℝ) + 1)) * I.den s * (1 - InexactRealizations.Classical.decay I ^ s) /
      (1 - InexactRealizations.Classical.decay I ^ 2) ≤ mass I N (s + 2) := by
  let q := InexactRealizations.Classical.decay I
  let a := 2 / ((N : ℝ) + 1)
  have hq := InexactRealizations.Classical.decay_mem I
  have hq0 := hq.1.le
  have hgap : 0 < 1 - q ^ 2 := by dsimp [q]; nlinarith [hq.1, hq.2]
  have ha : 0 ≤ a := by dsimp [a]; positivity
  induction s using Nat.twoStepInduction with
  | zero =>
    simp only [pow_zero, sub_self, mul_zero, zero_div]
    exact mass_nonneg I hN hs
  | one =>
    have hdrop := (omega_drop_bounds hN (show 1 ≤ (1 : ℕ) by decide)).1
    have hm := mul_le_mul_of_nonneg_right hdrop (I.den_pos 1).le
    have hratio : (1 - q) / (1 - q ^ 2) ≤ 1 := by
      apply (div_le_one hgap).mpr
      have hq' : q ≤ 1 := hq.2.le
      nlinarith [mul_le_mul_of_nonneg_left hq' hq0]
    have hleft := mul_le_mul_of_nonneg_left hratio (mul_nonneg ha (I.den_pos 1).le)
    rw [mass_step, mass_one, zero_add]
    have hbound : a * I.den 1 * (1 - q) / (1 - q ^ 2) ≤ a * I.den 1 := by
      convert hleft using 1
      all_goals ring
    simpa only [pow_one] using hbound.trans hm
  | more s ih _ =>
    have hprev := ih (by omega : s + 2 < N)
    have hdrop := (omega_drop_bounds hN (show 1 ≤ s + 2 by omega)).1
    have hdrop' := mul_le_mul_of_nonneg_right hdrop (I.den_pos (s + 2)).le
    have hpow : 0 ≤ 1 - q ^ s := by
      have hh := pow_le_one₀ hq0 hq.2.le (n := s)
      linarith
    have hden := Execution.den_decay_two I s
    have hden' := mul_le_mul_of_nonneg_right hden (show 0 ≤ a * (1 - q ^ s) / (1 - q ^ 2) by positivity)
    have hprev' : a * (q ^ 2 * I.den (s + 2)) * (1 - q ^ s) / (1 - q ^ 2) ≤ mass I N (s + 2) := by
      apply le_trans _ hprev
      convert hden' using 1 <;> ring
    have hsum := add_le_add hprev' hdrop'
    have hid : a * I.den (s + 2) * (1 - q ^ (s + 2)) / (1 - q ^ 2) =
        a * (q ^ 2 * I.den (s + 2)) * (1 - q ^ s) / (1 - q ^ 2) + a * I.den (s + 2) := by
      rw [pow_add]
      field_simp [hgap.ne']
      ring
    change a * I.den (s + 2) * (1 - q ^ (s + 2)) / (1 - q ^ 2) ≤ _
    rw [hid, mass_step]
    exact hsum

theorem scaled_den_lower (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hs : s ≤ N) :
    InexactRealizations.Classical.decay I ^ (N - s) ≤ I.epsilon N * I.den s := by
  let q := InexactRealizations.Classical.decay I
  have hq := InexactRealizations.Classical.decay_mem I
  have hq0 := hq.1.le
  have hp : q ^ (2 * N) ≤ q ^ (2 * s) := by
    have he : 2 * N = 2 * s + 2 * (N - s) := by omega
    rw [he, pow_add]
    have hh := pow_le_one₀ hq0 hq.2.le (n := 2 * (N - s))
    nlinarith [mul_le_mul_of_nonneg_left hh (pow_nonneg hq0 (2 * s))]
  have heq := InexactRealizations.Classical.scaled_den_eq I N (N - s) (by omega)
  rw [Nat.sub_sub_self hs] at heq
  rw [heq]
  have hden : 0 < 1 + q ^ (2 * N) := by positivity
  apply (le_div_iff₀ hden).mpr
  nlinarith [mul_le_mul_of_nonneg_left hp (pow_nonneg hq0 (N - s))]

end
end InexactRealizations.Accuracy.Uncompensated
