import InexactRealizations.Accuracy.Estimates.Leading

/-! Separating the target-size and initial-error parts of the nominal
Prefix and uncorrected-average local bounds. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Roundoff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {H : E →ₗ[ℝ] E} {initial target : E}

def prefixInitialCoefficient (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) : ℝ :=
  (3 + 4 * beta I s) / I.den s + 3 * beta I s / I.den (s - 1) +
    2 * alpha I s * I.L / I.den s + 1 / I.den (s + 1)

theorem prefixInitialCoefficient_nonneg (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) :
    0 ≤ prefixInitialCoefficient I s := by
  have hb := (beta_bounds I s).1
  have ha := (alpha_bounds I s).1.le
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hd := I.den_pos s
  have hp := I.den_pos (s - 1)
  have hn := I.den_pos (s + 1)
  unfold prefixInitialCoefficient
  positivity

set_option maxHeartbeats 1000000 in
theorem prefix_leading_bound (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H)
    (s : ℕ) (hs : s < N) :
    nominalPrefixLeading I N H initial target s ≤
      8 * ‖target‖ + ‖initial - target‖ * prefixInitialCoefficient I s := by
  let x := Nominal.x I N H initial target s
  let b := nominalStates I N H initial target s 1
  let g := Nominal.recovered I N H initial target s
  let r := ‖initial - target‖
  let rho := ‖target‖
  have hx0 : ‖x - target‖ ≤ r / I.den s := nominal_state_bound
    (Nominal.execution I N H initial target) hN hH s hs.le
  have hb0 : ‖b - target‖ ≤ r / I.den (s - 1) := by
    dsimp only [b]
    rw [Nominal.previous]
    exact nominal_state_bound (Nominal.execution I N H initial target) hN hH (s - 1) (by omega)
  have hx : ‖x‖ ≤ rho + r / I.den s := norm_from_distance hx0
  have hb : ‖b‖ ≤ rho + r / I.den (s - 1) := norm_from_distance hb0
  have hd : ‖x - b‖ ≤ r / I.den s + r / I.den (s - 1) := by
    have he : x - b = (x - target) - (b - target) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add hx0 hb0)
  have hbeta := beta_bounds I s
  have hbeta0 := hbeta.1
  have halpha := (alpha_bounds I s).1.le
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hZ : ‖(1 + beta I s) • x - beta I s • b‖ ≤
      rho + (1 + beta I s) * (r / I.den s) + beta I s * (r / I.den (s - 1)) := by
    have he : ((1 + beta I s) • x - beta I s • b) - target =
        (1 + beta I s) • (x - target) - beta I s • (b - target) := by module
    have hn := norm_sub_le ((1 + beta I s) • (x - target)) (beta I s • (b - target))
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hbeta.1,
      abs_of_nonneg (by positivity : 0 ≤ 1 + beta I s)] at hn
    have hbound : ‖((1 + beta I s) • x - beta I s • b) - target‖ ≤
        (1 + beta I s) * (r / I.den s) + beta I s * (r / I.den (s - 1)) := by
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_left hx0 (by positivity : 0 ≤ 1 + beta I s),
        mul_le_mul_of_nonneg_left hb0 hbeta.1]
    linarith [norm_from_distance hbound]
  have hg : ‖g‖ ≤ I.L * (r / I.den s) := by
    dsimp only [g]
    rw [Nominal.recovered_gradient I N H initial target hN s hs]
    exact (InexactRealizations.Analysis.hessian_action_bound I H hH _).trans
      (mul_le_mul_of_nonneg_left hx0 hL)
  have hn : ‖(1 + beta I s) • x - beta I s • b - alpha I s • g‖ ≤
      rho + r / I.den (s + 1) := by
    change ‖(1 + beta I s) • Nominal.x I N H initial target s -
      beta I s • nominalStates I N H initial target s 1 -
      alpha I s • Nominal.recovered I N H initial target s‖ ≤ _
    rw [Nominal.prefix_update]
    exact nominal_state_size hN hH (s + 1) (by omega)
  have hlead : nominalPrefixLeading I N H initial target s ≤
      (4 + 3 * beta I s) * rho + r * prefixInitialCoefficient I s := by
    unfold nominalPrefixLeading prefixInitialCoefficient
    change beta I s * ‖x - b‖ + 2 * (1 + beta I s) * ‖x‖ + beta I s * ‖b‖ +
      ‖(1 + beta I s) • x - beta I s • b‖ + 2 * alpha I s * ‖g‖ +
      ‖(1 + beta I s) • x - beta I s • b - alpha I s • g‖ ≤ _
    have hd' := mul_le_mul_of_nonneg_left hd hbeta.1
    have hx' := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2 * (1 + beta I s) by positivity)
    have hb' := mul_le_mul_of_nonneg_left hb hbeta.1
    have hg' := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2 * alpha I s by positivity)
    dsimp only [r] at *
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hrho : 0 ≤ rho := norm_nonneg _
  have hcoef : (4 + 3 * beta I s) * rho ≤ 8 * rho := by
    nlinarith [mul_le_mul_of_nonneg_right hbeta.2.le hrho]
  change nominalPrefixLeading I N H initial target s ≤ 8 * rho + r * prefixInitialCoefficient I s
  linarith

omit [FiniteDimensional ℝ E] in
theorem nominal_average_update (s : ℕ) (hs2 : 2 ≤ s) (hsN : s + 2 < N) :
    representedAverage (nominalStates I N H initial target s) + phi I N s •
      (Nominal.x I N H initial target s - representedAverage (nominalStates I N H initial target s)) =
        Nominal.average I N H initial target s := by
  have hh := (Nominal.execution I N H initial target).average_eq s hsN
  change Nominal.average I N H initial target s = updatedAverage (phi I N s)
    (earlierAverage (Nominal.average I N H initial target) s) (Nominal.x I N H initial target s) 0 at hh
  rw [Nominal.earlier_average I N H initial target s hs2] at hh
  simpa only [updatedAverage, add_zero] using hh.symm

theorem average_leading_bound (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H)
    (s : ℕ) (hs2 : 2 ≤ s) (hs : s + 2 < N) :
    nominalAverageLeading I N H initial target s ≤ ‖target‖ +
      3 * phi I N s * nominalDistance I N H initial target s + ‖initial - target‖ / mass I N (s + 2) := by
  unfold nominalAverageLeading nominalDistance
  rw [nominal_average_update s hs2 hs]
  have hb := nominal_average_bound (Nominal.execution I N H initial target) hN hH s (by omega) hs
  have hn : ‖Nominal.average I N H initial target s‖ ≤ ‖target‖ + ‖initial - target‖ / mass I N (s + 2) :=
    norm_from_distance hb
  linarith

end
end InexactRealizations.Accuracy.Execution
