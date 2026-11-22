import InexactRealizations.Accuracy.Errors.Remainders
import InexactRealizations.Accuracy.Execution.At

/-! Local gradient-average errors derived from the actual three rounded
operations, compared with the unrounded execution. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def nominalGradientLeading (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E)
    (initial target : E) (s : ℕ) : ℝ :=
  ‖nominalStates I N H initial target s 7 + phi I N s •
    (Nominal.recovered I N H initial target s - nominalStates I N H initial target s 7)‖ +
    3 * phi I N s * ‖Nominal.recovered I N H initial target s - nominalStates I N H initial target s 7‖

namespace Run
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO M : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

set_option maxHeartbeats 1000000 in
theorem gradient_error_reference (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (s : ℕ) (hs2 : 2 ≤ s) (hsN : s + 2 < N) :
    ‖v.localErrors.gradient s‖ ≤ u * nominalGradientLeading I N H initial target s +
      (u + uO) ^ 2 * I.L * gradientRemainder I.kappa N * M := by
  let E0 := stateEnvelope I.kappa N
  let F0 := variationEnvelope I.kappa N
  let R0 := recoveryEnvelope I.kappa N
  let A := parameterBound I.kappa N
  let delta := u + uO
  have hE : 0 ≤ E0 := le_trans zero_le_one (stateEnvelope_one I N)
  have hF : 0 ≤ F0 := variationEnvelope_nonneg I N
  have hR : 0 ≤ R0 := (envelopes_nonneg I N).2.2
  have hA : 1 ≤ A := parameterBound_one I N
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hdelta : 0 ≤ delta := add_nonneg hu huO
  have hs : s < N := by omega
  have hf := v.operand_bounds hN hu hu2 huO huO1 hM hinitial htarget hH s hs
  let a := v.stages ⟨s, hs⟩
  have hr : v.recovered s = a.recovered := v.recovered_at ⟨s, hs⟩
  have hx : ‖a.recovered - Nominal.recovered I N H initial target s‖ ≤
      delta * (I.L * (R0 + F0) * M) := by
    rw [← hr]
    have hh := hf.recovered_close
    nlinarith [mul_nonneg hdelta (show 0 ≤ I.L * F0 * M by positivity)]
  have hb : ‖v.states s 7 - nominalStates I N H initial target s 7‖ ≤
      delta * (I.L * (R0 + F0) * M) := by
    have hh := hf.old_gradient_close
    nlinarith [mul_nonneg hdelta (show 0 ≤ I.L * R0 * M by positivity)]
  have hxs : ‖a.recovered‖ ≤ 20000000 * A * I.L * E0 * M := by
    rw [← hr]
    nlinarith [hf.recovered_size]
  have hbs : ‖v.states s 7‖ ≤ 20000000 * A * I.L * E0 * M := by
    have hh : ‖v.states s 7‖ ≤ I.L * (E0 * M) := hf.old_gradient_size
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) (show 0 ≤ I.L * E0 * M by positivity),
      show 0 ≤ I.L * E0 * M by positivity]
  let op := a.gradientOperations hs2 hsN
  have hp := phi_unit I hN hs2 hsN
  have hop := op.reference_error (x0 := Nominal.recovered I N H initial target s)
    (b0 := nominalStates I N H initial target s 7) (phi := phi I N s) (eps := delta)
    (K := I.L * (R0 + F0) * M) (S := 20000000 * A * I.L * E0 * M)
    hu (by linarith) (by dsimp [delta]; linarith) hp.1.le hp.2 (p.phi_error ⟨s, hs⟩ hsN)
    (by positivity) (by positivity) hx hb hxs hbs
  change ‖v.gradient s - (Roundoff.earlierAverage v.gradient s +
    phi I N s • (v.recovered s - Roundoff.earlierAverage v.gradient s))‖ ≤ _
  rw [v.earlier_gradient s hs hs2, v.gradient_at ⟨s, hs⟩, hr]
  simp only [Stage.nextGradient, hsN, dite_true, show ¬s < 2 by omega, dite_false]
  convert hop using 1
  · rfl
  · unfold nominalGradientLeading gradientRemainder
    dsimp only [E0, F0, R0, A, delta]
    ring

end Run
end
end InexactRealizations.Accuracy.Execution
