import InexactRealizations.Accuracy.Errors.Remainders
import InexactRealizations.Accuracy.Execution.At

/-! The actual recovered-gradient residual with nominal first-order
terms and a derived uniform quadratic remainder. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def nominalRecoveryLeading (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E)
    (initial target : E) (s : ℕ) : ℝ :=
  3 * ‖Nominal.answer I N H initial target s - nominalStates I N H initial target s 7‖ +
    theta I N s * ‖Nominal.recovered I N H initial target s‖

namespace Run
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO M : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

set_option maxHeartbeats 1000000 in
theorem recovery_error_reference (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (s : ℕ) (hs : s < N) (hs2 : 2 ≤ s) :
    theta I N s * ‖v.localErrors.recovery s‖ ≤ u * nominalRecoveryLeading I N H initial target s +
      (u + uO) ^ 2 * I.L * recoveryRemainder I.kappa N * M := by
  let E0 := stateEnvelope I.kappa N
  let F0 := variationEnvelope I.kappa N
  let G0 := answerEnvelope I.kappa N
  let delta := u + uO
  have hE : 0 ≤ E0 := le_trans zero_le_one (stateEnvelope_one I N)
  have hF : 0 ≤ F0 := variationEnvelope_nonneg I N
  have hG : 0 ≤ G0 := (envelopes_nonneg I N).2.1
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hdelta : 0 ≤ delta := add_nonneg hu huO
  have hframe := v.operand_bounds hN hu hu2 huO huO1 hM hinitial htarget hH s hs
  let a := v.stages ⟨s, hs⟩
  have hans : v.answer s = a.answer := v.answer_at ⟨s, hs⟩
  have hg0 : ‖a.answer - Nominal.answer I N H initial target s‖ ≤ delta * I.L * G0 * M := by
    rw [← hans]
    exact hframe.answer_close
  have hb0 : ‖v.states s 7 - nominalStates I N H initial target s 7‖ ≤ I.L * (delta * F0 * M) := hframe.old_gradient_close
  have hg : ‖a.answer - Nominal.answer I N H initial target s‖ ≤ delta * (I.L * (G0 + F0) * M) := by
    nlinarith [mul_nonneg hdelta (show 0 ≤ I.L * F0 * M by positivity)]
  have hb : ‖v.states s 7 - nominalStates I N H initial target s 7‖ ≤ delta * (I.L * (G0 + F0) * M) := by
    nlinarith [mul_nonneg hdelta (show 0 ≤ I.L * G0 * M by positivity)]
  have hgs : ‖a.answer‖ ≤ 10000 * I.L * E0 * M := by rw [← hans]; nlinarith [hframe.answer_size]
  have hbs : ‖v.states s 7‖ ≤ 10000 * I.L * E0 * M := by
    have hh : ‖v.states s 7‖ ≤ I.L * (E0 * M) := hframe.old_gradient_size
    nlinarith [mul_nonneg hL (mul_nonneg hE hM)]
  let op := a.recoveryOperations hs2
  have ht := theta_unit I hN hs
  have hop := op.reference_error (g0 := Nominal.answer I N H initial target s)
    (b0 := nominalStates I N H initial target s 7) (theta := theta I N s) (eps := delta)
    (K := I.L * (G0 + F0) * M) (S := 10000 * I.L * E0 * M)
    hu hu2 (by dsimp [delta]; linarith) ht.1 ht.2 (p.theta_error ⟨s, hs⟩)
    (by positivity) (by positivity) hg hb hgs hbs
  change theta I N s * ‖v.recovered s - (Roundoff.earlierAverage v.gradient s +
    (theta I N s)⁻¹ • (v.answer s - Roundoff.earlierAverage v.gradient s))‖ ≤ _
  rw [v.earlier_gradient s hs hs2, v.recovered_at ⟨s, hs⟩, hans]
  simp only [Stage.recovered, observedRecovered, show ¬s < 2 by omega, dite_false]
  convert hop using 1
  · rfl
  · unfold nominalRecoveryLeading recoveryRemainder
    simp only [Nominal.recovered, Nominal.answer, exactRecovered, show ¬s < 2 by omega, ite_false]
    dsimp only [E0, F0, G0, delta]
    ring

end Run
end
end InexactRealizations.Accuracy.Execution
