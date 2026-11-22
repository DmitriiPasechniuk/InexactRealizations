import InexactRealizations.Algorithms.AveragedBalancedData

/-! Bounds and defined divisions of the printed ratio preparation. -/
namespace InexactRealizations.Algorithms.AveragedBalanced
noncomputable section
open InexactRealizations.Balanced

theorem alpha_bounds (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) :
    0 < alpha I s ∧ alpha I s < 4 / I.delta := by
  cases s with
  | zero =>
    simp only [alpha]
    refine ⟨div_pos (by norm_num) I.sum_pos, ?_⟩
    apply (div_lt_div_iff₀ I.sum_pos I.delta_pos).mpr
    unfold InexactRealizations.Operators.SpectralInterval.delta
    linarith [I.mu_pos, I.mu_lt_L]
  | succ s =>
    rw [alpha]
    exact ⟨div_pos (mul_pos (by norm_num) (ratio_unit I (s + 1)).1) I.delta_pos,
      (div_lt_div_iff_of_pos_right I.delta_pos).mpr (by linarith [(ratio_unit I (s + 1)).2])⟩

theorem beta_bounds (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) :
    0 ≤ beta I s ∧ beta I s < 1 := by
  cases s with
  | zero => simp [beta]
  | succ s =>
    have h0 := ratio_unit I s
    have h1 := ratio_unit I (s + 1)
    have hh := mul_lt_mul_of_pos_left h1.2 h0.1
    simp only [mul_one] at hh
    exact ⟨(mul_pos h0.1 h1.1).le, hh.trans h0.2⟩

theorem preparation_defined (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    0 < I.eta ∧ 0 < I.L + I.mu ∧ 0 < I.delta ∧
    (∀ j, 0 < 2 * I.eta - ratio I j) ∧
    (∀ s : Fin N, 0 < zeta I N s.val ∧ 0 < theta I N s.val) ∧
    ∀ s, 2 ≤ s → s + 2 < N → 0 < zeta I N s - omega N (s + 2) := by
  exact ⟨lt_trans zero_lt_one I.eta_gt_one, I.sum_pos, I.delta_pos,
    fun j ↦ lt_trans zero_lt_one (ratio_denominator I j),
    fun s ↦ ⟨(zeta_unit I hN s.isLt).1, (theta_unit I hN s.isLt).1⟩,
    fun _ hs hsN ↦ phi_denominator_pos I hN hs hsN⟩

end
end InexactRealizations.Algorithms.AveragedBalanced
