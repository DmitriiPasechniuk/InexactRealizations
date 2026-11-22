import InexactRealizations.Averages.Prefix
import InexactRealizations.Comparisons.Classical.VarianceLimit

/-! The actual Prefix spectral variance has the stated geometric-series
limit for every spectral probability law. The summable envelope is uniform
in the horizon, so both named laws inherit genuine limits. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Polynomial Polynomial.Chebyshev MeasureTheory Filter Topology
open InexactRealizations.Classical
open scoped BigOperators
variable {I : InexactRealizations.Operators.SpectralInterval} (ρ : SpectralLaw I)

theorem moment_le_square (k : ℕ) : moment ρ k ≤ (k : ℝ) ^ 2 := by
  cases k with
  | zero => simp only [moment_zero, Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), le_refl]
  | succ k =>
    have hi : Integrable (fun x ↦ (U ℝ (k : ℤ)).eval (I.z x) ^ 2) ρ.measure :=
      ρ.continuous_integrable (by unfold InexactRealizations.Operators.SpectralInterval.z; fun_prop)
    have hh := integral_mono_ae hi (integrable_const (((k + 1 : ℕ) : ℝ) ^ 2)) (by
      filter_upwards [ρ.spectral] with x hx
      have hu := InexactRealizations.Operators.abs_U_eval_le k (abs_le.mpr (I.z_mem hx))
      have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ (k : ℝ) + 1)).mpr hu
      simpa only [sq_abs, Nat.cast_add, Nat.cast_one] using hs)
    simpa only [moment, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, integral_const,
      measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh

def spectralTerm (N k : ℕ) : ℝ :=
  if 0 < k ∧ k ≤ N then
    (I.epsilon N * I.den (N - k) * initialWeight (N - k)) ^ 2 * moment ρ k else 0

def spectralLimit : ℝ := (16 / I.delta ^ 2) * ∑' k : ℕ, moment ρ k * decay I ^ (2 * k)

theorem spectralTerm_le (N k : ℕ) :
    ‖spectralTerm ρ N k‖ ≤ 4 * ((k : ℝ) ^ 2 * decay I ^ (2 * k)) := by
  have hq : 0 < decay I := (decay_mem I).1
  unfold spectralTerm
  split_ifs with hk
  · have ha0 : 0 ≤ I.epsilon N * I.den (N - k) * initialWeight (N - k) := by
      exact mul_nonneg (mul_nonneg (one_div_pos.mpr (I.den_pos N)).le (I.den_pos _).le) (initialWeight_pos _).le
    have ha : I.epsilon N * I.den (N - k) * initialWeight (N - k) ≤ 2 * decay I ^ k := by
      calc
        _ ≤ I.epsilon N * I.den (N - k) * 1 :=
          mul_le_mul_of_nonneg_left (initialWeight_le_one _) (mul_nonneg (one_div_pos.mpr (I.den_pos N)).le (I.den_pos _).le)
        _ ≤ _ := by simpa only [mul_one] using scaled_den_le I N k hk.2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (moment_nonneg ρ k))]
    have hsq := (sq_le_sq₀ ha0 (by positivity : 0 ≤ 2 * decay I ^ k)).mpr ha
    have hh := mul_le_mul hsq (moment_le_square ρ k) (moment_nonneg ρ k) (sq_nonneg _)
    exact hh.trans_eq (by rw [decay_pow_two]; ring)
  · simp only [norm_zero]
    positivity

theorem spectralTerm_tendsto (k : ℕ) :
    Tendsto (fun N : ℕ ↦ spectralTerm ρ N k) atTop (𝓝 (moment ρ k * decay I ^ (2 * k))) := by
  by_cases hk : k = 0
  · subst k
    simpa only [spectralTerm, lt_self_iff_false, false_and, ite_false, moment_zero, zero_mul] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  · have ht := ((scaled_den_tendsto I k).pow 2).mul_const (moment ρ k)
    have he : (decay I ^ k) ^ 2 * moment ρ k = moment ρ k * decay I ^ (2 * k) := by rw [decay_pow_two]; ring
    rw [he] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop k] with N hN
    simp only [spectralTerm, show 0 < k ∧ k ≤ N by omega, and_self, ite_true,
      initialWeight, show N - k ≠ 0 by omega, ite_false, mul_one]

theorem spectral_series_summable : Summable (fun k : ℕ ↦ moment ρ k * decay I ^ (2 * k)) := by
  have hq : 0 < decay I := (decay_mem I).1
  apply (variance_series_summable I).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (moment_nonneg ρ k) (by positivity))]
  exact mul_le_mul_of_nonneg_right (moment_le_square ρ k) (by positivity)

theorem prefix_variance_tsum (N : ℕ) (hN : 0 < N) :
    ρ.variance (history I N) = (16 / I.delta ^ 2) * ∑' k : ℕ, spectralTerm ρ N k := by
  rw [tsum_eq_sum (s := Finset.range (N + 1)) (by
    intro k hk
    have hnk : ¬k ≤ N := by simpa using hk
    simp only [spectralTerm, hnk, and_false, ite_false])]
  rw [← Finset.sum_range_reflect (fun k ↦ spectralTerm ρ N k) (N + 1), Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, spectralTerm, lt_self_iff_false, false_and,
    ite_false, add_zero]
  unfold SpectralLaw.variance
  simp_rw [prefix_energy ρ N hN]
  rw [Fin.sum_univ_eq_sum_range
    (fun s ↦ (16 * I.epsilon N ^ 2 / I.delta ^ 2) * (initialWeight s * I.den s) ^ 2 * moment ρ (N - s)) N,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsN := Finset.mem_range.mp hs
  have hks : 0 < N - s ∧ N - s ≤ N := by omega
  have hback : N - (N - s) = s := by omega
  simp only [hks, and_self, ite_true, hback]
  ring

theorem prefix_variance_tendsto :
    Tendsto (fun N : ℕ ↦ ρ.variance (history I N)) atTop (𝓝 (spectralLimit ρ)) := by
  have ht := tendsto_tsum_of_dominated_convergence ((variance_series_summable I).mul_left 4)
    (spectralTerm_tendsto ρ) (Filter.Eventually.of_forall fun N k ↦ spectralTerm_le ρ N k)
  have hh := ht.const_mul (16 / I.delta ^ 2)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  exact (prefix_variance_tsum ρ N hN).symm

end
end InexactRealizations.Averages
