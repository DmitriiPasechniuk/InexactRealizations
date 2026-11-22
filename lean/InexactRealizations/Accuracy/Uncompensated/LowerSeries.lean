import InexactRealizations.Accuracy.Uncompensated.Series
import Mathlib.Analysis.Normed.Group.Tannery

/-! The lower envelope converges to its weighted geometric series,
uniform domination being independent of the horizon. 
-/
namespace InexactRealizations.Accuracy.Uncompensated
noncomputable section
open Filter Topology
open scoped BigOperators

def lowerTerm (I : InexactRealizations.Operators.SpectralInterval) (N k : ℕ) : ℝ :=
  if 2 ≤ k ∧ k + 3 ≤ N then ((k : ℝ) - 1) * InexactRealizations.Classical.decay I ^ (k + 1) *
    (1 - InexactRealizations.Classical.decay I ^ (N - 1 - k)) else 0
def lowerLimitTerm (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) : ℝ :=
  if 2 ≤ k then ((k : ℝ) - 1) * InexactRealizations.Classical.decay I ^ (k + 1) else 0

theorem lowerTerm_nonneg (I : InexactRealizations.Operators.SpectralInterval) (N k : ℕ) : 0 ≤ lowerTerm I N k := by
  have hq := InexactRealizations.Classical.decay_mem I
  unfold lowerTerm
  split_ifs with hk
  · have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hk1 : 0 ≤ (k : ℝ) - 1 := by linarith
    exact mul_nonneg (mul_nonneg hk1 (pow_nonneg hq.1.le _))
      (sub_nonneg.mpr (pow_le_one₀ hq.1.le hq.2.le))
  · exact le_rfl

theorem lowerTerm_bound (I : InexactRealizations.Operators.SpectralInterval) (N k : ℕ) :
    ‖lowerTerm I N k‖ ≤ geometricTerm I k := by
  rw [Real.norm_eq_abs, abs_of_nonneg (lowerTerm_nonneg I N k)]
  unfold lowerTerm geometricTerm
  split_ifs with hk
  · have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hk1 : 0 ≤ (k : ℝ) - 1 := by linarith
    have hq0 := (InexactRealizations.Classical.decay_mem I).1.le
    have hpow := pow_nonneg hq0 (N - 1 - k)
    have hlead : 0 ≤ ((k : ℝ) - 1) * InexactRealizations.Classical.decay I ^ (k + 1) := by positivity
    nlinarith [mul_nonneg hlead hpow, pow_nonneg hq0 (k + 1)]
  · exact geometricTerm_nonneg I k

theorem lowerTerm_tendsto (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) :
    Tendsto (fun N : ℕ ↦ lowerTerm I N k) atTop (𝓝 (lowerLimitTerm I k)) := by
  by_cases hk : 2 ≤ k
  · have hq := InexactRealizations.Classical.decay_mem I
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hq.1.le hq.2).comp
      (Filter.tendsto_sub_atTop_nat (k + 1))
    have hc : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hh := (hc.sub hp).const_mul
      (((k : ℝ) - 1) * InexactRealizations.Classical.decay I ^ (k + 1))
    have hh' : Tendsto (fun N : ℕ ↦ (((k : ℝ) - 1) * InexactRealizations.Classical.decay I ^ (k + 1)) *
        (1 - InexactRealizations.Classical.decay I ^ (N - (k + 1)))) atTop (𝓝 (lowerLimitTerm I k)) := by
      simpa only [lowerLimitTerm, hk, ite_true, sub_zero, mul_one, Function.comp_apply] using hh
    apply hh'.congr'
    filter_upwards [eventually_ge_atTop (k + 3)] with N hN
    simp only [lowerTerm, hk, hN, and_self, ite_true]
    rw [show N - 1 - k = N - (k + 1) by omega]
  · simp only [lowerTerm, lowerLimitTerm, hk, false_and, ite_false]
    exact tendsto_const_nhds

theorem lowerLimit_hasSum (I : InexactRealizations.Operators.SpectralInterval) :
    HasSum (lowerLimitTerm I) (InexactRealizations.Classical.decay I ^ 3 / (1 - InexactRealizations.Classical.decay I) ^ 2) := by
  rw [← hasSum_nat_add_iff' 2]
  have hprefix : (∑ k ∈ Finset.range 2, lowerLimitTerm I k) = 0 := by
    norm_num [Finset.sum_range_succ, lowerLimitTerm]
  rw [hprefix, sub_zero]
  have hq : ‖InexactRealizations.Classical.decay I‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (InexactRealizations.Classical.decay_mem I).1]
    exact (InexactRealizations.Classical.decay_mem I).2
  have hh := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hq).mul_left (InexactRealizations.Classical.decay I ^ 3)
  convert hh using 1
  · funext k
    simp only [lowerLimitTerm, show 2 ≤ k + 2 by omega, ite_true, Nat.choose_one_right,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_add]
    ring
  · simp only [Nat.reduceAdd, div_eq_mul_inv, one_mul]

theorem lowerSeries_tendsto (I : InexactRealizations.Operators.SpectralInterval) :
    Tendsto (fun N : ℕ ↦ ∑' k : ℕ, lowerTerm I N k) atTop
      (𝓝 (InexactRealizations.Classical.decay I ^ 3 / (1 - InexactRealizations.Classical.decay I) ^ 2)) := by
  have hh := tendsto_tsum_of_dominated_convergence (geometricSeries_hasSum I).summable
    (lowerTerm_tendsto I) (Eventually.of_forall (fun N k ↦ lowerTerm_bound I N k))
  rw [(lowerLimit_hasSum I).tsum_eq] at hh
  exact hh

end
end InexactRealizations.Accuracy.Uncompensated
