import InexactRealizations.Accuracy.Estimates.PrefixLeading
import InexactRealizations.Accuracy.Bounds.Terminal

/-! Elementary Chebyshev ratios used to sum the first-order errors.
All constants depend on the condition number through the decay q. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced

def distanceCoefficient (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ :=
  if s < 2 then 0 else ((N : ℝ) + 3) / (2 * I.den (s - 2))

theorem distanceCoefficient_nonneg (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    0 ≤ distanceCoefficient I N s := by
  unfold distanceCoefficient
  have hd := (I.den_pos (s - 2)).le
  split_ifs <;> positivity

theorem den_decay_two (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) :
    (InexactRealizations.Classical.decay I) ^ 2 * I.den (s + 2) ≤ I.den s := by
  have hq := (InexactRealizations.Classical.decay_mem I).1.le
  have h1 := (den_decay_ratio_strict I s).le
  have h2 := mul_le_mul_of_nonneg_left (den_decay_ratio_strict I (s + 1)).le hq
  nlinarith

theorem den_decay_previous (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) :
    (InexactRealizations.Classical.decay I) ^ 2 * I.den (s + 1) ≤ I.den (s - 1) := by
  cases s with
  | zero =>
    have hq := InexactRealizations.Classical.decay_mem I
    have hd := (I.den_pos 1).le
    have h := (den_decay_ratio_strict I 0).le
    have hh := mul_le_mul_of_nonneg_right hq.2.le
      (mul_nonneg hq.1.le hd)
    norm_num only [Nat.zero_add, Nat.zero_sub, I.den_zero] at *
    nlinarith
  | succ s => simpa only [Nat.add_sub_cancel] using den_decay_two I s

theorem den_decay_one_squared (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) :
    (InexactRealizations.Classical.decay I) ^ 2 * I.den (s + 1) ≤ I.den s := by
  have hq := InexactRealizations.Classical.decay_mem I
  have hd := (I.den_pos (s + 1)).le
  have hh := mul_le_mul_of_nonneg_right hq.2.le (mul_nonneg hq.1.le hd)
  nlinarith [(den_decay_ratio_strict I s).le]

theorem distanceCoefficient_weighted (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    I.den s * distanceCoefficient I N s ≤ ((N : ℝ) + 3) / (2 * (InexactRealizations.Classical.decay I) ^ 2) := by
  have hq := (InexactRealizations.Classical.decay_mem I).1
  have hq2 : 0 < (InexactRealizations.Classical.decay I) ^ 2 := sq_pos_of_pos hq
  by_cases hs : s < 2
  · simp only [distanceCoefficient, hs, ite_true, mul_zero]
    positivity
  · simp only [distanceCoefficient, hs, ite_false]
    have hidx : s - 2 + 2 = s := by omega
    have hh := den_decay_two I (s - 2)
    rw [hidx] at hh
    have hd := I.den_pos (s - 2)
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * I.den (s - 2))
      (by positivity : 0 < 2 * (InexactRealizations.Classical.decay I) ^ 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * ((N : ℝ) + 3) by positivity)]

theorem classMass_upper {N s : ℕ} (hN : 2 ≤ N) :
    InexactRealizations.Balanced.classMass N s ≤ ((N : ℝ) + 1) / 2 := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold InexactRealizations.Balanced.classMass
  split_ifs
  · linarith
  · apply (div_le_iff₀ (by positivity : 0 < 2 * ((N : ℝ) + 1))).mpr
    nlinarith
  · exact le_rfl

theorem oracleWeight_eq (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) (s : Fin N) :
    oracleWeight I N hN s = (4 * I.epsilon N / I.delta) *
      InexactRealizations.Balanced.normalizer I N s.val * InexactRealizations.Balanced.classMass N s.val := by
  rw [oracleWeight, InexactRealizations.Balanced.response_endpoint, abs_neg,
    abs_of_pos (InexactRealizations.Balanced.responseBound_pos I hN s.isLt)]
  rfl

theorem oracleWeight_normalizer (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) (s : Fin N) :
    oracleWeight I N hN s / InexactRealizations.Balanced.normalizer I N s.val ≤
      2 * ((N : ℝ) + 1) * I.epsilon N / I.delta := by
  have hz := (InexactRealizations.Balanced.normalizer_pos I hN s.isLt).ne'
  have he : 0 ≤ 4 * I.epsilon N / I.delta := by
    have hdN := I.den_pos N
    have hd := I.delta_pos
    unfold InexactRealizations.Operators.SpectralInterval.epsilon
    positivity
  have hm := mul_le_mul_of_nonneg_left (classMass_upper (s := s.val) hN) he
  rw [oracleWeight_eq I hN s]
  convert hm using 1
  all_goals field_simp [hz]
  all_goals ring

theorem oracleWeight_theta (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) (s : Fin N) :
    oracleWeight I N hN s * theta I N s.val ≤
      2 * ((N : ℝ) + 1) * I.epsilon N * I.den s.val / I.delta := by
  have hw := (InexactRealizations.Balanced.omega_pos hN s.isLt).le
  have hw1 := InexactRealizations.Balanced.omega_le_one hN s.isLt
  have hm := (InexactRealizations.Balanced.classMass_pos (s := s.val) hN).le
  have he : 0 ≤ 4 * I.epsilon N / I.delta := by
    have hdN := I.den_pos N
    have hd := I.delta_pos
    unfold InexactRealizations.Operators.SpectralInterval.epsilon
    positivity
  have hprod : InexactRealizations.Balanced.classMass N s.val * InexactRealizations.Balanced.omega N s.val ≤ ((N : ℝ) + 1) / 2 := by
    have hh := mul_le_mul_of_nonneg_left hw1 hm
    nlinarith [classMass_upper (s := s.val) hN]
  have hh := mul_le_mul_of_nonneg_left hprod (mul_nonneg he (I.den_pos s.val).le)
  rw [oracleWeight_eq I hN s, theta_eq I hN s.isLt]
  convert hh using 1
  all_goals field_simp [(InexactRealizations.Balanced.normalizer_pos I hN s.isLt).ne']
  all_goals ring

end
end InexactRealizations.Accuracy.Execution
