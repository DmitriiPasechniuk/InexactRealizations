import InexactRealizations.Prose.SingleCall
import InexactRealizations.Budgets.PeakExamples
import InexactRealizations.Properties.Asymptotics
import InexactRealizations.Comparisons.Classical.VarianceLimit

/-! The exponential relative-gain penalty of Flat asserted in the
introduction. It already grows exponentially relative to D_N, an attained
upper bound on the best gain under every call budget. 
-/
namespace InexactRealizations.Prose
noncomputable section
open Polynomial Real Filter Topology
open InexactRealizations.Budgets InexactRealizations.Classical
open scoped BigOperators ENNReal NNReal

theorem corner_scale_ratio (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    InexactRealizations.Lower.additiveScale I N / InexactRealizations.Lower.derivativeScale I N =
      (I.den N - 1) / ((N : ℝ) ^ 2 * (I.eta - 1)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd := I.delta_pos.ne'
  have hm := I.mu_pos.ne'
  have ht := (I.den_pos N).ne'
  have he : I.eta - 1 = 2 * I.mu / I.delta := by
    change (I.L + I.mu) / I.delta - 1 = 2 * I.mu / I.delta
    field_simp
    unfold InexactRealizations.Operators.SpectralInterval.delta
    ring
  rw [he]
  unfold InexactRealizations.Lower.additiveScale InexactRealizations.Lower.derivativeScale InexactRealizations.Operators.SpectralInterval.epsilon
  field_simp

theorem flat_corner_scale_ratio (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    InexactRealizations.Lower.additiveScale I N / ((N : ℝ) * InexactRealizations.Lower.derivativeScale I N) =
      (I.den N - 1) / ((N : ℝ) ^ 3 * (I.eta - 1)) := by
  rw [mul_comm (N : ℝ), ← div_div, corner_scale_ratio I N hN, div_div]
  congr 1
  ring

theorem epsilon_decay_bound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : I.epsilon N ≤ 2 * decay I ^ N := by
  have hp : 0 < decay I ^ N := pow_pos (decay_mem I).1 N
  rw [InexactRealizations.Operators.SpectralInterval.epsilon, den_decay]
  field_simp
  nlinarith [sq_nonneg (decay I ^ N)]

theorem exponential_corner_scale_zero (I : InexactRealizations.Operators.SpectralInterval) (b : ℝ) (hb : 0 < b)
    (hbq : b * decay I < 1) :
    Tendsto (fun N : ℕ ↦ b ^ N * (N : ℝ) * InexactRealizations.Lower.derivativeScale I N) atTop (𝓝 0) := by
  have hq := decay_mem I
  have hd := I.delta_pos
  have hnon (N : ℕ) : 0 ≤ b ^ N * (N : ℝ) * InexactRealizations.Lower.derivativeScale I N := by
    unfold InexactRealizations.Lower.derivativeScale
    have he : 0 < I.epsilon N := one_div_pos.mpr (I.den_pos N)
    positivity
  have hbound (N : ℕ) : b ^ N * (N : ℝ) * InexactRealizations.Lower.derivativeScale I N ≤
      (4 / I.delta) * ((N : ℝ) ^ 3 * (b * decay I) ^ N) := by
    have hh := mul_le_mul_of_nonneg_left (epsilon_decay_bound I N)
      (show 0 ≤ 2 * b ^ N * (N : ℝ) ^ 3 / I.delta by positivity)
    convert hh using 1
    · unfold InexactRealizations.Lower.derivativeScale
      ring
    · rw [mul_pow]
      ring
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one 3 (mul_pos hb hq.1).le hbq).const_mul (4 / I.delta)
  have ht0 : Tendsto (fun N : ℕ ↦ (4 / I.delta) * ((N : ℝ) ^ 3 * (b * decay I) ^ N)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht
  exact squeeze_zero hnon hbound ht0

theorem flat_relative_corner_lower (p : ℝ≥0∞) (hp : 1 ≤ p) (I : InexactRealizations.Operators.SpectralInterval)
    (N : ℕ) (hN : 2 ≤ N) (r : ℝ) (hr : 0 < r) :
    InexactRealizations.Lower.additiveScale I N / N ≤ localRelativeGain p (InexactRealizations.Flat.history I N hN) I r := by
  let q := dualExponent p
  let : p.HolderConjugate q := holder_dualExponent p hp
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hl := operator_kernel_lower (p := p) (q := q) (InexactRealizations.Flat.history I N hN) I false I.mu I.mu
    ⟨le_rfl, I.mu_lt_L.le⟩ ⟨le_rfl, I.mu_lt_L.le⟩
  have hc := coordinate_le_norm (p := q)
    (fun s ↦ InexactRealizations.Lower.physicalKernel (InexactRealizations.Flat.history I N hN) s I.mu I.mu) ⟨0, by omega⟩
  rw [InexactRealizations.Lower.physicalKernel, InexactRealizations.Properties.first_query_one _ (by omega), eval_one, mul_one,
    InexactRealizations.Flat.response_mu, abs_neg, abs_of_nonneg (div_nonneg (InexactRealizations.Risk.additiveScale_nonneg I N) (Nat.cast_nonneg N))] at hc
  rw [localRelativeGain_eq_operatorGain p hp _ I r hr]
  exact hc.trans hl

theorem flat_relative_exponential (I : InexactRealizations.Operators.SpectralInterval) :
    ∃ b : ℝ, 1 < b ∧ ∀ᶠ N : ℕ in atTop, ∀ hN : 2 ≤ N,
      ∀ (p : ℝ≥0∞), 1 ≤ p → ∀ (r : ℝ), 0 < r →
        b ^ N * InexactRealizations.Lower.derivativeScale I N ≤ localRelativeGain p (InexactRealizations.Flat.history I N hN) I r := by
  have hq := decay_mem I
  obtain ⟨b, hb, hbq⟩ := exists_between ((one_lt_inv₀ hq.1).mpr hq.2)
  have hprod : b * decay I < 1 := (lt_div_iff₀ hq.1).mp (by simpa only [one_div] using hbq)
  have ht := (InexactRealizations.Properties.additiveScale_tendsto I).sub (exponential_corner_scale_zero I b (lt_trans zero_lt_one hb) hprod)
  have he : ∀ᶠ N : ℕ in atTop, b ^ N * (N : ℝ) * InexactRealizations.Lower.derivativeScale I N < InexactRealizations.Lower.additiveScale I N := by
    have hh := ht.eventually (lt_mem_nhds (show 0 < 1 / I.mu - 0 by simpa only [sub_zero] using one_div_pos.mpr I.mu_pos))
    filter_upwards [hh] with N hN
    linarith
  refine ⟨b, hb, ?_⟩
  filter_upwards [he] with N hN hN2 p hp r hr
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hh : b ^ N * InexactRealizations.Lower.derivativeScale I N ≤ InexactRealizations.Lower.additiveScale I N / N := by
    apply (le_div_iff₀ hn).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hN.le
  exact hh.trans (flat_relative_corner_lower p hp I N hN2 r hr)

theorem operatorGain_le_perCall {N : ℕ} (p : ℝ≥0∞) (hp : 1 ≤ p)
    (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (hN : 0 < N) (symmetric : Bool) :
    operatorGain p h I symmetric ≤ operatorGain ∞ h I symmetric := by
  let q := dualExponent p
  let : p.HolderConjugate q := holder_dualExponent p hp
  let : (∞ : ℝ≥0∞).HolderConjugate 1 := ENNReal.HolderConjugate.top_one
  let : Fact (1 ≤ p) := ⟨hp⟩
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  apply csSup_le (operatorValues_nonempty (p := p) (q := q) h I symmetric)
  intro v hv
  cases hv with
  | execution E H hH D delta hd hD hsym initial hi =>
    have hdtop : Budget ∞ delta := by
      refine ⟨hd.1, ?_⟩
      rw [callNorm_top]
      apply ciSup_le
      intro s
      rw [abs_of_nonneg (hd.1 s)]
      exact hd.coordinate s
    exact le_csSup (operatorValues_bddAbove (p := ∞) (q := 1) h I symmetric)
      (OperatorValue.execution E H hH D delta hdtop hD hsym initial hi)

theorem balanced_relative_le_corner (p : ℝ≥0∞) (hp : 1 ≤ p) (I : InexactRealizations.Operators.SpectralInterval)
    (N : ℕ) (hN : 2 ≤ N) (r : ℝ) (hr : 0 < r) :
    localRelativeGain p (InexactRealizations.Balanced.history I N hN) I r ≤ InexactRealizations.Lower.derivativeScale I N := by
  rw [localRelativeGain_eq_operatorGain p hp _ I r hr]
  have hh := operatorGain_le_perCall p hp (InexactRealizations.Balanced.history I N hN) I (by omega) false
  rw [← localRelativeGain_eq_operatorGain ∞ le_top _ I r hr,
    (InexactRealizations.Budgets.PeakExamples.balanced_perCall_optima I hN r hr).2] at hh
  exact hh

theorem flat_exponential_vs_balanced (I : InexactRealizations.Operators.SpectralInterval) :
    ∃ b : ℝ, 1 < b ∧ ∀ᶠ N : ℕ in atTop, ∀ hN : 2 ≤ N,
      ∀ (p : ℝ≥0∞), 1 ≤ p → ∀ (r : ℝ), 0 < r →
        b ^ N * localRelativeGain p (InexactRealizations.Balanced.history I N hN) I r ≤
          localRelativeGain p (InexactRealizations.Flat.history I N hN) I r := by
  obtain ⟨b, hb, hh⟩ := flat_relative_exponential I
  refine ⟨b, hb, ?_⟩
  filter_upwards [hh] with N hN hN2 p hp r hr
  exact (mul_le_mul_of_nonneg_left (balanced_relative_le_corner p hp I N hN2 r hr)
    (pow_nonneg (lt_trans zero_lt_one hb).le N)).trans (hN hN2 p hp r hr)

end
end InexactRealizations.Prose
