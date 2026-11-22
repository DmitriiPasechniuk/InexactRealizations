import InexactRealizations.Roundoff.Journal
import InexactRealizations.Comparisons.Classical.Exterior
import InexactRealizations.Operators.Chebyshev.Amplification

/-! The exact finite-horizon Prefix state-error factor F_N in current
and its strict condition-number bound. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
open scoped BigOperators

def prefixFactor (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : ℝ :=
  ∑ s : Fin N, ((N : ℝ) - s.val) * I.den (s.val + 1) / I.den N

def weightedDen (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : ℝ :=
  ∑ s ∈ Finset.range N, ((N : ℝ) - s) * I.den (s + 1)

theorem prefixFactor_eq (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    prefixFactor I N = weightedDen I N / I.den N := by
  rw [prefixFactor, Fin.sum_univ_eq_sum_range
    (fun s : ℕ ↦ ((N : ℝ) - s) * I.den (s + 1) / I.den N) N, ← Finset.sum_div]
  rfl

theorem den_sum_identity (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    (2 * I.eta - 2) * (∑ s ∈ Finset.range N, I.den (s + 1)) =
      I.den (N + 1) - I.den N - I.eta + 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, I.den_add_two]
    ring

theorem weightedDen_succ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    weightedDen I (N + 1) = weightedDen I N + ∑ s ∈ Finset.range (N + 1), I.den (s + 1) := by
  unfold weightedDen
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, one_mul]
  have hs : (∑ s ∈ Finset.range N, ((N : ℝ) + 1 - s) * I.den (s + 1)) =
      (∑ s ∈ Finset.range N, ((N : ℝ) - s) * I.den (s + 1)) +
        ∑ s ∈ Finset.range N, I.den (s + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hs]
  ring

theorem weightedDen_identity (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    (2 * I.eta - 2) * weightedDen I N =
      I.den (N + 1) - ((N : ℝ) + 1) * I.eta + N := by
  induction N with
  | zero => simp [weightedDen]
  | succ N ih =>
    rw [weightedDen_succ, mul_add, ih, den_sum_identity, I.den_add_two]
    push_cast
    ring

theorem decay_quadratic (I : InexactRealizations.Operators.SpectralInterval) :
    (InexactRealizations.Classical.decay I) ^ 2 + 1 = 2 * I.eta * InexactRealizations.Classical.decay I := by
  have hh := InexactRealizations.Classical.den_decay I 1
  rw [I.den_one, pow_one] at hh
  have hq := (InexactRealizations.Classical.decay_mem I).1.ne'
  field_simp [hq] at hh
  nlinarith

theorem decay_eq_condition (I : InexactRealizations.Operators.SpectralInterval) :
    InexactRealizations.Classical.decay I = (Real.sqrt I.kappa - 1) / (Real.sqrt I.kappa + 1) := by
  have hk : 1 < I.kappa := (lt_div_iff₀ I.mu_pos).mpr (by simpa [InexactRealizations.Operators.SpectralInterval.kappa] using I.mu_lt_L)
  have hs : 1 < Real.sqrt I.kappa := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ I.kappa), Real.sqrt_nonneg I.kappa]
  have heta : I.eta * (I.kappa - 1) = I.kappa + 1 := by
    unfold InexactRealizations.Operators.SpectralInterval.eta InexactRealizations.Operators.SpectralInterval.kappa InexactRealizations.Operators.SpectralInterval.delta
    field_simp [I.mu_pos.ne', (sub_pos.mpr I.mu_lt_L).ne']
  have hsq := Real.sq_sqrt (by linarith : 0 ≤ I.kappa)
  have hq := InexactRealizations.Classical.decay_mem I
  have hquad := decay_quadratic I
  have hprod : ((Real.sqrt I.kappa + 1) * InexactRealizations.Classical.decay I - (Real.sqrt I.kappa - 1)) *
      ((Real.sqrt I.kappa - 1) * InexactRealizations.Classical.decay I - (Real.sqrt I.kappa + 1)) = 0 := by
    calc
      _ = (I.kappa - 1) * ((InexactRealizations.Classical.decay I) ^ 2 + 1) -
          2 * (I.kappa + 1) * InexactRealizations.Classical.decay I := by
        linear_combination (InexactRealizations.Classical.decay I - 1) ^ 2 * hsq
      _ = 0 := by rw [hquad, ← heta]; ring
  have hsecond : (Real.sqrt I.kappa - 1) * InexactRealizations.Classical.decay I - (Real.sqrt I.kappa + 1) < 0 := by
    nlinarith [mul_lt_mul_of_pos_left hq.2 (sub_pos.mpr hs)]
  have hfirst := (mul_eq_zero.mp hprod).resolve_right hsecond.ne
  apply (eq_div_iff (by linarith : Real.sqrt I.kappa + 1 ≠ 0)).mpr
  nlinarith

theorem den_decay_ratio_strict (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    InexactRealizations.Classical.decay I * I.den (N + 1) < I.den N := by
  have hq := InexactRealizations.Classical.decay_mem I
  have hid : I.den N - InexactRealizations.Classical.decay I * I.den (N + 1) =
      (1 - (InexactRealizations.Classical.decay I) ^ 2) * (InexactRealizations.Classical.decay I) ^ N / 2 := by
    rw [InexactRealizations.Classical.den_decay, InexactRealizations.Classical.den_decay, pow_succ]
    field_simp [hq.1.ne']
    ring
  have hp : 0 < (1 - (InexactRealizations.Classical.decay I) ^ 2) * (InexactRealizations.Classical.decay I) ^ N / 2 := by
    have hs : (InexactRealizations.Classical.decay I) ^ 2 < 1 := by nlinarith [hq.1, hq.2]
    exact div_pos (mul_pos (sub_pos.mpr hs) (pow_pos hq.1 N)) (by norm_num)
  linarith

theorem prefixFactor_decay_bound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    prefixFactor I N < 1 / (1 - InexactRealizations.Classical.decay I) ^ 2 := by
  have hq := InexactRealizations.Classical.decay_mem I
  have hden : 0 < (1 - InexactRealizations.Classical.decay I) ^ 2 := sq_pos_of_pos (sub_pos.mpr hq.2)
  have hfactor : (1 - InexactRealizations.Classical.decay I) ^ 2 =
      InexactRealizations.Classical.decay I * (2 * I.eta - 2) := by nlinarith [decay_quadratic I]
  rw [prefixFactor_eq]
  apply (div_lt_iff₀ (I.den_pos N)).mpr
  rw [one_div_mul_eq_div]
  apply (lt_div_iff₀ hden).mpr
  rw [hfactor]
  calc
    _ = InexactRealizations.Classical.decay I * (I.den (N + 1) - ((N : ℝ) + 1) * I.eta + N) := by
      rw [← weightedDen_identity]
      ring
    _ < InexactRealizations.Classical.decay I * I.den (N + 1) := by
      apply mul_lt_mul_of_pos_left _ hq.1
      have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith [I.eta_gt_one]
    _ < I.den N := den_decay_ratio_strict I N

theorem prefixFactor_condition_bound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    prefixFactor I N < (Real.sqrt I.kappa + 1) ^ 2 / 4 := by
  have hid : 1 / (1 - InexactRealizations.Classical.decay I) ^ 2 = (Real.sqrt I.kappa + 1) ^ 2 / 4 := by
    rw [decay_eq_condition]
    have hp : 0 < Real.sqrt I.kappa + 1 := by positivity
    field_simp [hp.ne']
    ring
  exact (prefixFactor_decay_bound I N).trans_eq hid

theorem additive_condition_bound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    I.L * InexactRealizations.Lower.additiveScale I N < I.kappa := by
  have hL : 0 < I.L := lt_trans I.mu_pos I.mu_lt_L
  have he : 0 < I.epsilon N := one_div_pos.mpr (I.den_pos N)
  unfold InexactRealizations.Lower.additiveScale InexactRealizations.Operators.SpectralInterval.kappa
  rw [← mul_div_assoc]
  apply (div_lt_div_iff_of_pos_right I.mu_pos).mpr
  nlinarith

end
end InexactRealizations.Accuracy
