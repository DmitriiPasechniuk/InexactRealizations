import InexactRealizations.Accuracy.Bounds.Finite
import InexactRealizations.Accuracy.UncompensatedWitness

/-! Uncompensated terminal accuracy, with the extra target coefficient
only at actually rounded average updates s>=2. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Roundoff
open scoped BigOperators

def averageMask (s : ℕ) : ℝ := if 2 ≤ s then 1 else 0

def uncompensatedInitialCoefficient (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ :=
  if s < 2 then 0 else 6 * phi I N s * distanceCoefficient I N s + 2 / mass I N (s + 2)

def finiteUncompensatedInitialCoefficient (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) : ℝ :=
  (∑ s : Fin N, oracleWeight I N hN s * I.L * hatInitialCoefficient I N s.val) +
  (∑ s : Fin (N - 2), averageWeight I N s.val * I.L * uncompensatedInitialCoefficient I N s.val) +
  ∑ s : Fin N, stateWeight I N s.val * prefixInitialCoefficient I s.val

def finiteUncompensatedQuadraticCoefficient (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) : ℝ :=
  (∑ s : Fin N, oracleWeight I N hN s * I.L) *
    (queryEnvelope I.kappa N + queryRemainder I.kappa N + recoveryRemainder I.kappa N) +
  (∑ s : Fin (N - 2), averageWeight I N s.val * I.L) *
    (gradientRemainder I.kappa N + uncompensatedRemainder I.kappa N) +
  prefixFactor I N * prefixRemainder I.kappa N

theorem weighted_sum_two_profiles {ι : Type*} [Fintype ι] (w f g : ι → ℝ) (A B C D : ℝ) :
    (∑ i, w i * (A * g i + B * f i * D + C)) =
      A * (∑ i, w i * g i) + (B * D) * (∑ i, w i * f i) + C * (∑ i, w i) := by
  calc
    _ = ∑ i, (A * (w i * g i) + (B * D) * (w i * f i) + C * w i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {H : E →ₗ[ℝ] E} {initial target : E}

set_option maxHeartbeats 2000000 in
theorem Run.finite_uncompensated_accuracy {u uO : ℝ} {p : Prepared I N u}
    (v : Run p H initial target uO) (hc : v.Uncompensated) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hH : InexactRealizations.Analysis.Admissible I H) :
    ‖v.x N - target‖ ≤ I.epsilon N * ‖initial - target‖ +
      (u + uO) * finiteUncompensatedInitialCoefficient I N hN * ‖initial - target‖ +
      (2 * (u + uO) * I.L * InexactRealizations.Lower.additiveScale I N + 8 * u * prefixFactor I N +
        u * I.L * UncompensatedWitness.averageFactor I N) * ‖target‖ +
      (u + uO) ^ 2 * finiteUncompensatedQuadraticCoefficient I N hN * (‖initial - target‖ + ‖target‖) := by
  let r := ‖initial - target‖
  let rho := ‖target‖
  let M := r + rho
  let delta := u + uO
  let Ch := queryEnvelope I.kappa N + queryRemainder I.kappa N + recoveryRemainder I.kappa N
  let Ca := gradientRemainder I.kappa N + uncompensatedRemainder I.kappa N
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
    exact add_nonneg (remainders_nonneg I N).2.2.2.1 (remainders_nonneg I N).2.2.2.2.2
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
      u * I.L * rho * averageMask s.val +
        delta * I.L * uncompensatedInitialCoefficient I N s.val * r + delta ^ 2 * I.L * Ca * M := by
    have hs : s.val + 2 < N := by have := s.isLt; omega
    by_cases hsmall : s.val < 2
    · rw [v.startup_average_noise s.val hsmall hs, norm_zero]
      simp only [uncompensatedInitialCoefficient, averageMask, show ¬2 ≤ s.val by omega,
        hsmall, ite_true, ite_false, mul_zero, zero_mul, zero_add]
      positivity
    · have hh := v.uncompensated_noise_first_order hc hN hu hu2 huO huO1 hM hi htarg hH s.val (by omega) hs
      have hd := activeDistance_bound (initial := initial) (target := target) hN hH s.val (by omega)
      simp only [activeDistance, hsmall, ite_false] at hd
      have hphi := (phi_unit I hN (show 2 ≤ s.val by omega) hs).1.le
      have hm := (mass_next_pos I hN (show 2 ≤ s.val by omega) hs).le
      have hcoef : 0 ≤ uncompensatedInitialCoefficient I N s.val := by
        simp only [uncompensatedInitialCoefficient, hsmall, ite_false]
        have hd0 := distanceCoefficient_nonneg I N s.val
        positivity
      have hl : 6 * phi I N s.val * nominalDistance I N H initial target s.val + 2 * (r / mass I N (s.val + 2)) ≤
          uncompensatedInitialCoefficient I N s.val * r := by
        simp only [uncompensatedInitialCoefficient, hsmall, ite_false, div_eq_mul_inv]
        nlinarith [mul_le_mul_of_nonneg_left hd (show 0 ≤ 6 * phi I N s.val by positivity)]
      have hhl : ‖averageNoise H v.localErrors s.val‖ ≤ u * I.L * rho +
          u * I.L * (uncompensatedInitialCoefficient I N s.val * r) + delta ^ 2 * I.L * Ca * M := by
        have hh' := mul_le_mul_of_nonneg_left hl (mul_nonneg hu hL)
        nlinarith
      have huDelta : u * I.L * (uncompensatedInitialCoefficient I N s.val * r) ≤
          delta * I.L * uncompensatedInitialCoefficient I N s.val * r := by
        dsimp only [delta]
        nlinarith [mul_nonneg huO (show 0 ≤ I.L * uncompensatedInitialCoefficient I N s.val * r by positivity)]
      simp only [averageMask, show 2 ≤ s.val by omega, ite_true, mul_one]
      exact hhl.trans (add_le_add (add_le_add le_rfl huDelta) le_rfl)
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
      (u * I.L * rho) * (∑ s : Fin (N - 2), averageWeight I N s.val * averageMask s.val) +
      (delta * I.L * r) * (∑ s : Fin (N - 2), averageWeight I N s.val * uncompensatedInitialCoefficient I N s.val) +
      (delta ^ 2 * I.L * Ca * M) * (∑ s : Fin (N - 2), averageWeight I N s.val) := by
    convert hsumA using 1
    symm
    exact weighted_sum_two_profiles (fun s : Fin (N - 2) ↦ averageWeight I N s.val)
      (fun s ↦ uncompensatedInitialCoefficient I N s.val) (fun s ↦ averageMask s.val)
      (u * I.L * rho) (delta * I.L) (delta ^ 2 * I.L * Ca * M) r
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
  have hsumAv : (∑ s : Fin (N - 2), averageWeight I N s.val * averageMask s.val) =
      UncompensatedWitness.averageFactor I N := by
    unfold UncompensatedWitness.averageFactor
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : 2 ≤ s.val <;> simp only [averageMask, hs, ite_true, ite_false, mul_one, mul_zero, averageWeight]
  convert hh using 1
  dsimp only [finiteUncompensatedInitialCoefficient, finiteUncompensatedQuadraticCoefficient, Ch, Ca, Cx, M, delta, r, rho]
  rw [sum_scaled_profile, sum_scaled_profile]
  simp only [← Finset.sum_mul]
  rw [hsumW, hsumF, hsumAv]
  ring

end
end InexactRealizations.Accuracy.Execution
