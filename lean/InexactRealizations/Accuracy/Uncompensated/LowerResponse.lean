import InexactRealizations.Accuracy.Uncompensated.LowerMass

/-! Lower response envelope used in the attained large-horizon order. -/
namespace InexactRealizations.Accuracy.Uncompensated
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Accuracy.Execution

theorem square_floor_lower (k : ℕ) : (k : ℝ) ^ 2 - 1 ≤ 4 * ((k ^ 2 / 4 : ℕ) : ℝ) := by
  have hm : k ^ 2 % 4 ≤ 1 := by
    have hbound := Nat.mod_lt k (show 0 < 4 by decide)
    have hpow : k ^ 2 % 4 = (k % 4) ^ 2 % 4 := Nat.pow_mod k 2 4
    interval_cases hmod : k % 4 <;> norm_num [hmod] at hpow <;> omega
  have hnat : k ^ 2 ≤ 4 * (k ^ 2 / 4) + 1 := by omega
  have hreal : (k : ℝ) ^ 2 ≤ 4 * ((k ^ 2 / 4 : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
  linarith

def lowerPrefactor (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : ℝ :=
  2 * (N : ℝ) * I.L / (((N : ℝ) + 1) * (1 - InexactRealizations.Classical.decay I ^ 2) * I.delta)

set_option maxHeartbeats 1000000 in
theorem scaled_mass_lower (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s + 2 < N) :
    (2 / ((N : ℝ) + 1)) * InexactRealizations.Classical.decay I ^ (N - s) *
      (1 - InexactRealizations.Classical.decay I ^ s) / (1 - InexactRealizations.Classical.decay I ^ 2) ≤
        I.epsilon N * mass I N (s + 2) := by
  let q := InexactRealizations.Classical.decay I
  have hq := InexactRealizations.Classical.decay_mem I
  have hq0 := hq.1.le
  have hgap : 0 < 1 - q ^ 2 := by dsimp [q]; nlinarith [hq.1, hq.2]
  have hpow : 0 ≤ 1 - q ^ s := sub_nonneg.mpr (pow_le_one₀ hq0 hq.2.le)
  have hcoef : 0 ≤ (2 / ((N : ℝ) + 1)) * (1 - q ^ s) / (1 - q ^ 2) := by positivity
  have hden := mul_le_mul_of_nonneg_left (scaled_den_lower I (show s ≤ N by omega)) hcoef
  have hmass := mul_le_mul_of_nonneg_left (mass_lower_geometric I hN s hs)
    (one_div_pos.mpr (I.den_pos N)).le
  have hden' : (2 / ((N : ℝ) + 1)) * q ^ (N - s) * (1 - q ^ s) / (1 - q ^ 2) ≤
      I.epsilon N * ((2 / ((N : ℝ) + 1)) * I.den s * (1 - q ^ s) / (1 - q ^ 2)) := by
    convert hden using 1 <;> ring
  exact hden'.trans hmass

set_option maxHeartbeats 1000000 in
theorem average_response_lower (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s + 2 < N) :
    lowerPrefactor I N * (((N - 1 - s : ℕ) : ℝ) - 1) *
      InexactRealizations.Classical.decay I ^ ((N - 1 - s) + 1) * (1 - InexactRealizations.Classical.decay I ^ s) ≤
        I.L * averageWeight I N s := by
  let k := N - 1 - s
  let p := (k ^ 2 / 4 : ℕ)
  have hk2 : (2 : ℝ) ≤ k := by dsimp only [k]; exact_mod_cast (show 2 ≤ N - 1 - s by omega)
  have hk1 : 0 ≤ (k : ℝ) - 1 := by linarith
  have hkcast : (k : ℝ) + 1 = (N : ℝ) - s := by
    dsimp [k]
    push_cast [show 1 ≤ N by omega, show s ≤ N - 1 by omega]
    ring
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hDelta := I.delta_pos
  have hw := InexactRealizations.Balanced.omega_pos hN hs
  have hwb := (omega_next_bounds hN hs).2
  have hwb' : (N : ℝ) * InexactRealizations.Balanced.omega N (s + 2) ≤ (k : ℝ) + 1 := by
    have hh := (le_div_iff₀ hn).mp hwb
    nlinarith
  have hfloor := square_floor_lower k
  have hquot : (N : ℝ) * ((k : ℝ) - 1) ≤ 4 * (p : ℝ) / InexactRealizations.Balanced.omega N (s + 2) := by
    apply (le_div_iff₀ hw).mpr
    nlinarith [mul_le_mul_of_nonneg_left hwb' (show 0 ≤ (k : ℝ) - 1 by linarith)]
  have hmass0 := mass_nonneg I hN hs
  have he := (one_div_pos.mpr (I.den_pos N)).le
  have hscale : 0 ≤ I.L * I.epsilon N * mass I N (s + 2) / I.delta := by positivity
  have hbase := mul_le_mul_of_nonneg_left hquot hscale
  have hbase' : ((N : ℝ) * ((k : ℝ) - 1) * I.L / I.delta) *
      (I.epsilon N * mass I N (s + 2)) ≤ I.L * averageWeight I N s := by
    convert hbase using 1
    · ring
    · unfold averageWeight
      rw [InexactRealizations.Roundoff.averageResponse_endpoint, InexactRealizations.Roundoff.averageScale]
      unfold InexactRealizations.Operators.SpectralInterval.epsilon
      dsimp only [p, k]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  have hcoef : 0 ≤ (N : ℝ) * ((k : ℝ) - 1) * I.L / I.delta := by positivity
  have hlower := mul_le_mul_of_nonneg_left (scaled_mass_lower I hN hs) hcoef
  have hlower' : lowerPrefactor I N * ((k : ℝ) - 1) *
      InexactRealizations.Classical.decay I ^ (k + 1) * (1 - InexactRealizations.Classical.decay I ^ s) ≤
      ((N : ℝ) * ((k : ℝ) - 1) * I.L / I.delta) * (I.epsilon N * mass I N (s + 2)) := by
    have hexp : N - s = k + 1 := by dsimp [k]; omega
    rw [hexp] at hlower
    convert hlower using 1
    unfold lowerPrefactor
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  exact hlower'.trans hbase'

end
end InexactRealizations.Accuracy.Uncompensated
