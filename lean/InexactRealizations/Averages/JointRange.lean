import InexactRealizations.Averages.RangeAsymptotics

/-! with exactly the printed joint horizon range and its
pi/sqrt(6) threshold, for every actual positive-noise additive optimum. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Real Filter Topology
open InexactRealizations.Classical

theorem journal_joint_range (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) (hδtop : δ < π / sqrt 6) :
    ∃ κ0 : ℝ, ∀ (I : InexactRealizations.Operators.SpectralInterval), κ0 ≤ I.kappa →
      ∀ (N : ℕ), 2 ≤ N → c * sqrt I.kappa ≤ (N : ℝ) →
        (N : ℝ) ≤ (π / sqrt 6 - δ) * I.kappa ^ (3 / 4 : ℝ) / sqrt (log I.kappa) →
        ∀ h : InexactRealizations.History N, h.ChebyshevExact I → AdditiveOptimal h I →
          (uniform I).variance (history I N) < (uniform I).variance h := by
  let D := π / sqrt 6 - δ
  have hD : 0 < D := sub_pos.mpr hδtop
  have hDtop : D < π / sqrt 6 := by dsimp only [D]; linarith
  have hcrit : D ^ 2 < π ^ 2 / 6 := by
    have hh := (sq_lt_sq₀ hD.le (by positivity : 0 ≤ π / sqrt 6)).mpr hDtop
    simpa only [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)] using hh
  obtain ⟨b, hDb, hbtop⟩ := exists_between hcrit
  have hb : 0 < b := (sq_nonneg D).trans_lt hDb
  obtain ⟨A, hA, ha, hAgap⟩ := exists_large_parameter D b hDb
  obtain ⟨N0, hN0⟩ := inverseSquareSum_eventually_lower b hbtop
  let a := 1 - (cosh c)⁻¹
  have hap : 0 < a := by
    have hh : 1 < cosh c := one_lt_cosh.mpr hc.ne'
    exact sub_pos.mpr ((inv_lt_one₀ (cosh_pos c)).mpr hh)
  have hlog : ∀ᶠ k : ℝ in atTop, 1 ≤ log k := tendsto_log_atTop.eventually_ge_atTop 1
  have hquarter : ∀ᶠ k : ℝ in atTop, D ≤ k ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop D
  have hNc : ∀ᶠ k : ℝ in atTop, (N0 : ℝ) ≤ c * sqrt k :=
    (tendsto_sqrt_atTop.const_mul_atTop hc).eventually_ge_atTop (N0 : ℝ)
  have hall : ∀ᶠ k : ℝ in atTop,
      9 ≤ k ∧ 1 ≤ log k ∧ D ≤ k ^ (1 / 4 : ℝ) ∧ (N0 : ℝ) ≤ c * sqrt k ∧
      129 * A ^ 2 * log k < a ^ 2 * (1 - k⁻¹) * sqrt k ∧
      D ^ 2 * (1 + 128 * exp (-A)) < (1 - 2 * exp (-A)) ^ 2 * b * (1 - k⁻¹) := by
    filter_upwards [eventually_ge_atTop (9 : ℝ), hlog, hquarter, hNc,
      eventually_small_gap A a hap, eventually_large_gap A D b hAgap] with k hk hl hq hn hs hg
    exact ⟨hk, hl, hq, hn, hs, hg⟩
  obtain ⟨κ0, hκ0⟩ := eventually_atTop.mp hall
  refine ⟨κ0, ?_⟩
  intro I hI N hN hNcN hNu h he ho
  obtain ⟨hk, hl, hq, hn, hs, hg⟩ := hκ0 I.kappa hI
  have hkp : 0 < I.kappa := lt_trans zero_lt_one (condition_gt_one I)
  have hNpos : 0 < N := by omega
  have hlogpos : 0 < log I.kappa := by linarith
  have hNk : (N : ℝ) ≤ I.kappa := horizon_le_condition I.kappa D N hkp hD.le hl hq hNu
  apply strict_comparison_of_normalized h I he hNpos ho hk hl hNk
  by_cases hNA : A * sqrt I.kappa ≤ (N : ℝ)
  · have hN0N : N0 ≤ N := by exact_mod_cast hn.trans hNcN
    exact large_range_gap I N hNpos A D b hD hb.le hlogpos ha hNA (hN0 N hN0N).le
      (horizon_square_bound I.kappa D N hkp hD.le (Nat.cast_nonneg N) hlogpos hNu) hg
  · have hae : a ≤ 1 - I.epsilon N := by
      have hh := epsilon_cosh_bound I N c hc.le hNcN
      dsimp only [a]
      linarith
    exact small_range_gap I N hNpos A a hA hap.le hae (le_of_lt (lt_of_not_ge hNA)) hs

end
end InexactRealizations.Averages
