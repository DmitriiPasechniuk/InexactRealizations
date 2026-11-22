import InexactRealizations.Accuracy.Errors.AverageFirstOrder
import InexactRealizations.Accuracy.Estimates.Decay

/-! The finite-horizon accuracy bound obtained from the literal rounded
run. The remaining scalar estimates replace these finite sums by their
cubic horizon and condition-number bounds. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Roundoff
open scoped BigOperators

def hatInitialCoefficient (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ :=
  3 / InexactRealizations.Balanced.normalizer I N s + 6 * theta I N s * distanceCoefficient I N s
def averageInitialCoefficient (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ :=
  if s < 2 then 0 else 9 * phi I N s * distanceCoefficient I N s + 1 / mass I N (s + 2)
def finiteInitialCoefficient (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) : ℝ :=
  (∑ s : Fin N, oracleWeight I N hN s * I.L * hatInitialCoefficient I N s.val) +
  (∑ s : Fin (N - 2), averageWeight I N s.val * I.L * averageInitialCoefficient I N s.val) +
  ∑ s : Fin N, stateWeight I N s.val * prefixInitialCoefficient I s.val
def finiteQuadraticCoefficient (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) : ℝ :=
  (∑ s : Fin N, oracleWeight I N hN s * I.L) *
    (queryEnvelope I.kappa N + queryRemainder I.kappa N + recoveryRemainder I.kappa N) +
  (∑ s : Fin (N - 2), averageWeight I N s.val * I.L) *
    (gradientRemainder I.kappa N + averageRemainder I.kappa N) +
  prefixFactor I N * prefixRemainder I.kappa N

theorem weighted_sum_affine {ι : Type*} [Fintype ι] (w f : ι → ℝ) (A B C D : ℝ) :
    (∑ i, w i * (A + B * f i * D + C)) =
      (A + C) * (∑ i, w i) + (B * D) * (∑ i, w i * f i) := by
  calc
    _ = ∑ i, ((A + C) * w i + (B * D) * (w i * f i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem sum_scaled_profile {ι : Type*} [Fintype ι] (w f : ι → ℝ) (c : ℝ) :
    (∑ i, w i * c * f i) = c * ∑ i, w i * f i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {H : E →ₗ[ℝ] E} {initial target : E}

theorem activeDistance_bound (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H)
    (s : ℕ) (hs : s < N) : activeDistance I N H initial target s ≤
      distanceCoefficient I N s * ‖initial - target‖ := by
  by_cases hsmall : s < 2
  · simp only [activeDistance, distanceCoefficient, hsmall, ite_true, zero_mul, le_refl]
  · simp only [activeDistance, distanceCoefficient, hsmall, ite_false]
    convert nominal_distance_size (initial := initial) (target := target) hN hH s (by omega) hs using 1
    ring

set_option maxHeartbeats 2000000 in
theorem Run.finite_accuracy {u uO : ℝ} {p : Prepared I N u}
    (v : Run p H initial target uO) (hc : v.Compensated) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hH : InexactRealizations.Analysis.Admissible I H) :
    ‖v.x N - target‖ ≤ I.epsilon N * ‖initial - target‖ +
      (u + uO) * finiteInitialCoefficient I N hN * ‖initial - target‖ +
      (2 * (u + uO) * I.L * InexactRealizations.Lower.additiveScale I N + 8 * u * prefixFactor I N) * ‖target‖ +
      (u + uO) ^ 2 * finiteQuadraticCoefficient I N hN * (‖initial - target‖ + ‖target‖) := by
  let r := ‖initial - target‖
  let rho := ‖target‖
  let M := r + rho
  let delta := u + uO
  let Ch := queryEnvelope I.kappa N + queryRemainder I.kappa N + recoveryRemainder I.kappa N
  let Ca := gradientRemainder I.kappa N + averageRemainder I.kappa N
  let Cx := prefixRemainder I.kappa N
  have hr : 0 ≤ r := norm_nonneg _
  have hrho : 0 ≤ rho := norm_nonneg _
  have hM : 0 ≤ M := add_nonneg hr hrho
  have hi : ‖initial‖ ≤ M := norm_from_distance (le_refl ‖initial - target‖) |>.trans (by dsimp [M, r, rho]; linarith)
  have htarg : ‖target‖ ≤ M := by dsimp [M, rho]; linarith
  have hdelta : 0 ≤ delta := add_nonneg hu huO
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hCa : 0 ≤ Ca := by
    dsimp [Ca]
    exact add_nonneg (remainders_nonneg I N).2.2.2.1 (remainders_nonneg I N).2.2.1
  have hhat (s : Fin N) : ‖hatNoise I N H v.localErrors s.val‖ ≤
      2 * delta * I.L * rho + delta * I.L * hatInitialCoefficient I N s.val * r + delta ^ 2 * I.L * Ch * M := by
    have hh := v.hat_error_first_order hN hu hu2 huO huO1 hM hi htarg hH s.val s.isLt
    have hd := activeDistance_bound (initial := initial) (target := target) hN hH s.val s.isLt
    have htheta := (theta_unit I hN s.isLt).1.le
    have hl : 2 * rho + 3 * (r / InexactRealizations.Balanced.normalizer I N s.val) +
        6 * theta I N s.val * activeDistance I N H initial target s.val ≤
        2 * rho + hatInitialCoefficient I N s.val * r := by
      unfold hatInitialCoefficient
      simp only [div_eq_mul_inv]
      nlinarith [mul_le_mul_of_nonneg_left hd (show 0 ≤ 6 * theta I N s.val by positivity)]
    have hh' := hh.trans (add_le_add (mul_le_mul_of_nonneg_left hl (mul_nonneg hdelta hL)) le_rfl)
    convert hh' using 1
    ring
  have hav (s : Fin (N - 2)) : ‖averageNoise H v.localErrors s.val‖ ≤
      delta * I.L * averageInitialCoefficient I N s.val * r + delta ^ 2 * I.L * Ca * M := by
    have hs : s.val + 2 < N := by have := s.isLt; omega
    by_cases hsmall : s.val < 2
    · rw [v.startup_average_noise s.val hsmall hs, norm_zero]
      simp only [averageInitialCoefficient, hsmall, ite_true, mul_zero, zero_mul, zero_add]
      positivity
    · have hh := v.average_noise_first_order hc hN hu hu2 huO huO1 hM hi htarg hH s.val (by omega) hs
      have hd := activeDistance_bound (initial := initial) (target := target) hN hH s.val (by omega)
      simp only [activeDistance, hsmall, ite_false] at hd
      have hphi := (phi_unit I hN (show 2 ≤ s.val by omega) hs).1.le
      have hm := (mass_next_pos I hN (show 2 ≤ s.val by omega) hs).le
      have hcoef : 0 ≤ averageInitialCoefficient I N s.val := by
        simp only [averageInitialCoefficient, hsmall, ite_false]
        have hd0 := distanceCoefficient_nonneg I N s.val
        positivity
      have hl : 9 * phi I N s.val * nominalDistance I N H initial target s.val + r / mass I N (s.val + 2) ≤
          averageInitialCoefficient I N s.val * r := by
        simp only [averageInitialCoefficient, hsmall, ite_false, div_eq_mul_inv]
        nlinarith [mul_le_mul_of_nonneg_left hd (show 0 ≤ 9 * phi I N s.val by positivity)]
      have hhl := hh.trans (add_le_add (mul_le_mul_of_nonneg_left hl (mul_nonneg hu hL)) le_rfl)
      have huDelta : u * I.L * (averageInitialCoefficient I N s.val * r) ≤
          delta * I.L * averageInitialCoefficient I N s.val * r := by
        dsimp only [delta]
        nlinarith [mul_nonneg huO (show 0 ≤ I.L * averageInitialCoefficient I N s.val * r by positivity)]
      convert hhl.trans (add_le_add huDelta le_rfl) using 1
  have hpre (s : Fin N) : ‖v.localErrors.state (s.val + 1)‖ ≤
      8 * u * rho + delta * r * prefixInitialCoefficient I s.val + delta ^ 2 * Cx * M := by
    have hh := v.prefix_error_first_order hN hu hu2 huO huO1 hM hi htarg hH s.val s.isLt
    have hcoef := prefixInitialCoefficient_nonneg I s.val
    have hmore : u * r * prefixInitialCoefficient I s.val ≤ delta * r * prefixInitialCoefficient I s.val := by
      dsimp only [delta]
      nlinarith [mul_nonneg huO (mul_nonneg hr hcoef)]
    exact hh.trans (add_le_add (add_le_add le_rfl hmore) le_rfl)
  have hsumH := Finset.sum_le_sum (s := Finset.univ)
    (fun s _ ↦ mul_le_mul_of_nonneg_left (hhat s) (oracleWeight_nonneg I hN s))
  have hsumA := Finset.sum_le_sum (s := Finset.univ)
    (fun (s : Fin (N - 2)) _ ↦ mul_le_mul_of_nonneg_left (hav s)
      (averageWeight_nonneg I (s := s.val) hN (by have := s.isLt; omega)))
  have hsumX := Finset.sum_le_sum (s := Finset.univ)
    (fun s _ ↦ mul_le_mul_of_nonneg_left (hpre s) (stateWeight_nonneg I s.isLt))
  rw [weighted_sum_affine] at hsumH
  have hsumA' : (∑ s : Fin (N - 2), averageWeight I N s.val * ‖averageNoise H v.localErrors s.val‖) ≤
      (delta ^ 2 * I.L * Ca * M) * (∑ s : Fin (N - 2), averageWeight I N s.val) +
        (delta * I.L * r) * (∑ s : Fin (N - 2), averageWeight I N s.val * averageInitialCoefficient I N s.val) := by
    convert hsumA using 1
    symm
    simpa only [zero_add] using weighted_sum_affine (fun s : Fin (N - 2) ↦ averageWeight I N s.val)
      (fun s ↦ averageInitialCoefficient I N s.val) 0 (delta * I.L) (delta ^ 2 * I.L * Ca * M) r
  have hsumX' : (∑ s : Fin N, stateWeight I N s.val * ‖v.localErrors.state (s.val + 1)‖) ≤
      (8 * u * rho + delta ^ 2 * Cx * M) * (∑ s : Fin N, stateWeight I N s.val) +
        (delta * r) * (∑ s : Fin N, stateWeight I N s.val * prefixInitialCoefficient I s.val) := by
    convert hsumX using 1
    symm
    simpa only [mul_one] using weighted_sum_affine (fun s : Fin N ↦ stateWeight I N s.val)
      (fun s ↦ prefixInitialCoefficient I s.val) (8 * u * rho) (delta * r) (delta ^ 2 * Cx * M) 1
  have hh := (v.terminal_norm_bound hN hH).trans
    (add_le_add (add_le_add (add_le_add le_rfl hsumH) hsumA') hsumX')
  have hsumW : (∑ s : Fin N, oracleWeight I N hN s) = InexactRealizations.Lower.additiveScale I N :=
    balanced_response_abs_sum I N hN
  have hsumF : (∑ s : Fin N, stateWeight I N s.val) = prefixFactor I N := rfl
  convert hh using 1
  dsimp only [finiteInitialCoefficient, finiteQuadraticCoefficient, Ch, Ca, Cx, M, delta, r, rho]
  rw [sum_scaled_profile, sum_scaled_profile]
  simp only [← Finset.sum_mul]
  rw [hsumW, hsumF]
  ring

end
end InexactRealizations.Accuracy.Execution
