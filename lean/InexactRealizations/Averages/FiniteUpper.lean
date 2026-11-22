import InexactRealizations.Averages.ClosedLimits
import Mathlib.NumberTheory.Harmonic.Bounds

/-! A finite-horizon upper bound for the actual uniform spectral variance.
Its remainder decays with N/sqrt(kappa); no asymptotic certificate is assumed. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Polynomial MeasureTheory Real
open InexactRealizations.Classical
open scoped BigOperators

theorem oddHarmonic_mono : Monotone oddHarmonic := by
  intro n m hnm
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
  intro j _ _
  positivity

theorem oddHarmonic_log_bound (n : ℕ) : oddHarmonic n ≤ 1 + log n := by
  have hh : oddHarmonic n ≤ (harmonic n : ℝ) := by
    simp only [oddHarmonic, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    apply Finset.sum_le_sum
    intro j _
    simp only [Nat.cast_add, Nat.cast_one]
    apply inv_anti₀ (by positivity : 0 < (j : ℝ) + 1)
    linarith [Nat.cast_nonneg (α := ℝ) j]
  exact hh.trans (harmonic_le_one_add_log n)

theorem scaled_den_square_envelope (I : InexactRealizations.Operators.SpectralInterval) (N k : ℕ) (hk : k ≤ N) :
    (I.epsilon N * I.den (N - k)) ^ 2 ≤ decay I ^ (2 * k) + 2 * decay I ^ (2 * N) +
      decay I ^ (2 * N) * decay I ^ (2 * (N - k)) := by
  have hq : 0 < decay I := (decay_mem I).1
  have hprod : decay I ^ (2 * k) * decay I ^ (2 * (N - k)) = decay I ^ (2 * N) := by
    rw [← pow_add, ← Nat.mul_add, Nat.add_sub_of_le hk]
  have hb : I.epsilon N * I.den (N - k) ≤ decay I ^ k * (1 + decay I ^ (2 * (N - k))) := by
    rw [scaled_den_eq I N k hk]
    apply div_le_self (by positivity)
    linarith [pow_nonneg hq.le (2 * N)]
  have ha : 0 ≤ I.epsilon N * I.den (N - k) :=
    mul_nonneg (one_div_pos.mpr (I.den_pos N)).le (I.den_pos _).le
  have hs := (sq_le_sq₀ ha (by positivity)).mpr hb
  exact hs.trans_eq (by rw [← hprod, decay_pow_two]; ring)

theorem uniform_term_bound (I : InexactRealizations.Operators.SpectralInterval) (N k : ℕ) (hk : k ≤ N) :
    spectralTerm (uniform I) N k ≤ oddHarmonic k * decay I ^ (2 * k) +
      oddHarmonic N * decay I ^ (2 * N) * (2 + decay I ^ (2 * (N - k))) := by
  have hq : 0 < decay I := (decay_mem I).1
  have hmN := oddHarmonic_nonneg N
  have hmk := oddHarmonic_nonneg k
  unfold spectralTerm
  split_ifs with hpos
  · have hw := (initialWeight_le_one (N - k))
    have hw0 := (initialWeight_pos (N - k)).le
    have hw2 : initialWeight (N - k) ^ 2 ≤ 1 := by nlinarith
    have hscaled := scaled_den_square_envelope I N k hk
    rw [uniform_moment, mul_pow]
    calc
      _ ≤ (I.epsilon N * I.den (N - k)) ^ 2 * oddHarmonic k := by
        nlinarith [mul_le_mul_of_nonneg_left hw2 (mul_nonneg (sq_nonneg (I.epsilon N * I.den (N - k))) (oddHarmonic_nonneg k))]
      _ ≤ (decay I ^ (2 * k) + 2 * decay I ^ (2 * N) +
          decay I ^ (2 * N) * decay I ^ (2 * (N - k))) * oddHarmonic k :=
        mul_le_mul_of_nonneg_right hscaled (oddHarmonic_nonneg k)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right (oddHarmonic_mono hk)
          (show 0 ≤ decay I ^ (2 * N) * (2 + decay I ^ (2 * (N - k))) by positivity)
        nlinarith
  · positivity

theorem finite_geometric_bound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), decay I ^ (2 * k)) ≤ (1 - decay I ^ 2)⁻¹ := by
  have hq := decay_mem I
  have hnorm : ‖decay I ^ 2‖ < 1 := by rw [norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; nlinarith [hq.1, hq.2]
  have hh := (summable_geometric_of_norm_lt_one hnorm).sum_le_tsum (Finset.range (N + 1))
    (fun k _ ↦ pow_nonneg (sq_nonneg (decay I)) k)
  rw [tsum_geometric_of_norm_lt_one hnorm] at hh
  simpa only [← pow_mul, one_div] using hh

theorem uniform_finite_upper (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    (uniform I).variance (history I N) ≤ spectralLimit (uniform I) +
      (16 / I.delta ^ 2) * oddHarmonic N * decay I ^ (2 * N) *
        (2 * ((N : ℝ) + 1) + (1 - decay I ^ 2)⁻¹) := by
  have hq : 0 < decay I := (decay_mem I).1
  have hmN := oddHarmonic_nonneg N
  rw [prefix_variance_tsum (uniform I) N hN,
    tsum_eq_sum (s := Finset.range (N + 1)) (by
      intro k hk
      have hnk : ¬k ≤ N := by simpa using hk
      simp only [spectralTerm, hnk, and_false, ite_false])]
  have hbound := Finset.sum_le_sum (s := Finset.range (N + 1))
    (fun k hk ↦ uniform_term_bound I N k (by have := Finset.mem_range.mp hk; omega))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hbound
  have hsum : (∑ k ∈ Finset.range (N + 1), (2 + decay I ^ (2 * (N - k)))) ≤
      2 * ((N : ℝ) + 1) + (1 - decay I ^ 2)⁻¹ := by
    rw [Finset.sum_add_distrib]
    have he : (∑ k ∈ Finset.range (N + 1), decay I ^ (2 * (N - k))) =
        ∑ k ∈ Finset.range (N + 1), decay I ^ (2 * k) := by
      simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (fun k ↦ decay I ^ (2 * k)) (N + 1)
    rw [he]
    have hg := finite_geometric_bound I N
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    linarith
  have hseries := (spectral_series_summable (uniform I)).sum_le_tsum (Finset.range (N + 1))
    (fun k _ ↦ mul_nonneg (moment_nonneg (uniform I) k) (by positivity))
  simp_rw [uniform_moment] at hseries
  have hf := mul_le_mul_of_nonneg_left hsum (show 0 ≤ oddHarmonic N * decay I ^ (2 * N) by positivity)
  have hfinal := mul_le_mul_of_nonneg_left (hbound.trans (add_le_add hseries hf))
    (show 0 ≤ 16 / I.delta ^ 2 by positivity)
  simpa only [spectralLimit, uniform_moment, mul_add, mul_assoc] using hfinal

end
end InexactRealizations.Averages
