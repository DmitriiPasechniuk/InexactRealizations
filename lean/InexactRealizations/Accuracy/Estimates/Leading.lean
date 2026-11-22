import InexactRealizations.Accuracy.Errors.Query
import InexactRealizations.Accuracy.Errors.Recovery
import InexactRealizations.Accuracy.Errors.Gradient
import InexactRealizations.Accuracy.Errors.Average
import InexactRealizations.Accuracy.Errors.Prefix
import InexactRealizations.Accuracy.Errors.Uncompensated

/-! Bounds on the nominal operands which multiply first-order errors.
The weighted old average is treated without dividing by its possibly
zero startup mass. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open Polynomial InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Roundoff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {H : E →ₗ[ℝ] E} {initial target : E}

theorem nominal_state_size (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H)
    (s : ℕ) (hs : s ≤ N) :
    ‖Nominal.x I N H initial target s‖ ≤ ‖target‖ + ‖initial - target‖ / I.den s :=
  norm_from_distance (nominal_state_bound (Nominal.execution I N H initial target) hN hH s hs)

theorem nominal_query_size (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H)
    (s : ℕ) (hs : s < N) :
    ‖Nominal.query I N H initial target s‖ ≤
      ‖target‖ + ‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s :=
  norm_from_distance (nominal_query_bound (Nominal.execution I N H initial target) hN hH s hs)

theorem nominal_prior_average_weighted (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H)
    (s : ℕ) (hs2 : 2 ≤ s) (hs : s < N) :
    mass I N s * ‖representedAverage (nominalStates I N H initial target s) - target‖ ≤ ‖initial - target‖ := by
  have hw := nominal_average_weighted (Nominal.execution I N H initial target) hN (s - 2) (by omega)
  have hidx : s - 2 + 2 = s := by omega
  rw [hidx] at hw
  have ha := Nominal.earlier_average I N H initial target s hs2
  simp only [earlierAverage, show ¬s < 2 by omega, ite_false] at ha
  change mass I N s • (Nominal.average I N H initial target (s - 2) - target) = _ at hw
  rw [ha] at hw
  have hp (lam : ℝ) (hlam : lam ∈ Set.Icc I.mu I.L) :
      |(physicalRemainder I N s).eval lam| ≤ 1 := by
    rw [physicalRemainder_eval]
    exact (InexactRealizations.Balanced.abs_remainder_eval_le hN hs (abs_le.mpr (I.z_mem hlam))).trans
      (by linarith [(InexactRealizations.Balanced.omega_pos hN hs).le])
  have hh := InexactRealizations.Analysis.polynomial_action_bound I H hH (physicalRemainder I N s) 1
    zero_le_one hp (initial - target)
  rw [← hw, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mass_nonneg I hN hs), one_mul] at hh
  exact hh

theorem nominal_prior_average_theta (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H)
    (s : ℕ) (hs2 : 2 ≤ s) (hs : s < N) :
    (1 - theta I N s) * ‖representedAverage (nominalStates I N H initial target s)‖ ≤
      (1 - theta I N s) * ‖target‖ + ‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s := by
  have hw := nominal_prior_average_weighted (initial := initial) (target := target) hN hH s hs2 hs
  have hz := (InexactRealizations.Balanced.normalizer_pos I hN hs).le
  have hh : (1 - theta I N s) *
      ‖representedAverage (nominalStates I N H initial target s) - target‖ ≤
      ‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s := by
    rw [theta_mass I hN hs, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hw hz
  have hn := norm_from_distance (le_refl ‖representedAverage (nominalStates I N H initial target s) - target‖)
  have ht := (theta_unit I hN hs).2
  nlinarith [mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr ht)]

theorem nominal_distance_size (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H)
    (s : ℕ) (hs2 : 2 ≤ s) (hs : s < N) :
    nominalDistance I N H initial target s ≤ ((N : ℝ) + 3) * ‖initial - target‖ / (2 * I.den (s - 2)) := by
  have ha := Nominal.earlier_average I N H initial target s hs2
  simp only [earlierAverage, show ¬s < 2 by omega, ite_false] at ha
  unfold nominalDistance
  rw [← ha]
  exact nominal_distance_bound (Nominal.execution I N H initial target) hN hH s hs2 hs

theorem query_leading_bound (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H)
    (s : ℕ) (hs2 : 2 ≤ s) (hs : s < N) :
    nominalQueryLeading I N H initial target s ≤
      (2 - theta I N s) * ‖target‖ + 2 * ‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s +
      3 * theta I N s * nominalDistance I N H initial target s := by
  have hb := nominal_prior_average_theta (initial := initial) (target := target) hN hH s hs2 hs
  have hq := nominal_query_size (initial := initial) (target := target) hN hH s hs
  unfold nominalQueryLeading nominalDistance
  simp only [mul_div_assoc]
  nlinarith

theorem recovery_leading_bound (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H)
    (s : ℕ) (hs2 : 2 ≤ s) (hs : s < N) :
    nominalRecoveryLeading I N H initial target s ≤ I.L *
      (3 * theta I N s * nominalDistance I N H initial target s +
        theta I N s * (‖initial - target‖ / I.den s)) := by
  have ht := (theta_unit I hN hs).1.le
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hd := InexactRealizations.Analysis.hessian_action_bound I H hH
    (Nominal.x I N H initial target s - representedAverage (nominalStates I N H initial target s))
  have hx := InexactRealizations.Analysis.hessian_action_bound I H hH (Nominal.x I N H initial target s - target)
  have hb := nominal_state_bound (Nominal.execution I N H initial target) hN hH s hs.le
  unfold nominalRecoveryLeading nominalDistance
  rw [Nominal.oracle_gradient_difference I N H initial target hN s hs2 hs,
    Nominal.recovered_gradient I N H initial target hN s hs, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ht]
  nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 3 * theta I N s),
    mul_le_mul_of_nonneg_left (hb.trans (le_refl _)) hL,
    mul_le_mul_of_nonneg_left (hx.trans (mul_le_mul_of_nonneg_left hb hL)) ht]

theorem gradient_leading_bound (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H)
    (s : ℕ) (hs2 : 2 ≤ s) (hs : s + 2 < N) :
    nominalGradientLeading I N H initial target s ≤ I.L *
      (3 * phi I N s * nominalDistance I N H initial target s +
        ‖initial - target‖ / mass I N (s + 2)) := by
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hp := (phi_unit I hN hs2 hs).1.le
  have hd := InexactRealizations.Analysis.hessian_action_bound I H hH
    (Nominal.x I N H initial target s - representedAverage (nominalStates I N H initial target s))
  have ha := nominal_average_bound (Nominal.execution I N H initial target) hN hH s (by omega) hs
  change ‖Nominal.average I N H initial target s - target‖ ≤ _ at ha
  have hg := InexactRealizations.Analysis.hessian_action_bound I H hH (Nominal.average I N H initial target s - target)
  unfold nominalGradientLeading nominalDistance
  rw [Nominal.gradient_update_identity I N H initial target hN s hs2 hs,
    Nominal.recovered_prior_difference I N H initial target hN s hs2 (by omega)]
  nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 3 * phi I N s),
    mul_le_mul_of_nonneg_left ha hL]

end
end InexactRealizations.Accuracy.Execution
