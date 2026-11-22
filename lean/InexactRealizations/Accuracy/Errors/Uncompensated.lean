import InexactRealizations.Accuracy.Errors.Remainders
import InexactRealizations.Accuracy.Execution.At

/-! The corresponding uncorrected average. Its nominal result contributes
the additional target-size term. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def nominalAverageLeading (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E)
    (initial target : E) (s : ℕ) : ℝ :=
  ‖representedAverage (nominalStates I N H initial target s) + phi I N s •
    (Nominal.x I N H initial target s - representedAverage (nominalStates I N H initial target s))‖ +
    3 * phi I N s * ‖Nominal.x I N H initial target s - representedAverage (nominalStates I N H initial target s)‖

namespace Run
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO M : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

set_option maxHeartbeats 1000000 in
theorem uncompensated_error_reference (v : Run p H initial target uO) (hc : v.Uncompensated) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (s : ℕ) (hs2 : 2 ≤ s) (hsN : s + 2 < N) :
    ‖v.localErrors.average s‖ ≤ u * nominalAverageLeading I N H initial target s +
      (u + uO) ^ 2 * uncompensatedRemainder I.kappa N * M := by
  let E0 := stateEnvelope I.kappa N
  let F0 := variationEnvelope I.kappa N
  let delta := u + uO
  have hE : 0 ≤ E0 := le_trans zero_le_one (stateEnvelope_one I N)
  have hF : 0 ≤ F0 := variationEnvelope_nonneg I N
  have hdelta : 0 ≤ delta := add_nonneg hu huO
  have hs : s < N := by omega
  have hf := v.operand_bounds hN hu hu2 huO huO1 hM hinitial htarget hH s hs
  rcases hc ⟨s, hs⟩ hs2 hsN with ⟨op, hchoice⟩
  have hx : ‖v.states s 0 - Nominal.x I N H initial target s‖ ≤ delta * (2 * F0 * M) := by
    have hh := hf.x_close
    nlinarith [show 0 ≤ delta * F0 * M by positivity]
  have hb : ‖representedAverage (v.states s) - representedAverage (nominalStates I N H initial target s)‖ ≤
      delta * (2 * F0 * M) := by nlinarith [hf.average_close]
  have hxs : ‖v.states s 0‖ ≤ 2 * E0 * M := by
    have hh : ‖v.states s 0‖ ≤ E0 * M := hf.x_size
    nlinarith [show 0 ≤ E0 * M by positivity]
  have hbs : ‖representedAverage (v.states s)‖ ≤ 2 * E0 * M := by
    have h3 : ‖v.states s 3‖ ≤ E0 * M := hf.raw_average_size
    have h5 : ‖v.states s 5‖ ≤ E0 * M := hf.correction_size
    exact (norm_add_le _ _).trans (by linarith)
  have hp := phi_unit I hN hs2 hsN
  have hop := op.reference_error (x0 := Nominal.x I N H initial target s)
    (b0 := representedAverage (nominalStates I N H initial target s))
    (phi := phi I N s) (eps := delta) (K := 2 * F0 * M) (S := 2 * E0 * M)
    hu (by linarith) (by dsimp [delta]; linarith) hp.1.le hp.2 (p.phi_error ⟨s, hs⟩ hsN)
    (by positivity) (by positivity) hx hb hxs hbs
  change ‖v.average s - (Roundoff.earlierAverage v.average s +
    phi I N s • (v.x s - Roundoff.earlierAverage v.average s))‖ ≤ _
  rw [v.earlier_average s hs hs2, v.average_at ⟨s, hs⟩]
  simp only [Stage.nextAverage, Stage.nextCorrection, hsN, dite_true,
    show ¬s < 2 by omega, dite_false, hchoice, add_zero]
  convert hop using 1
  · rfl
  · unfold nominalAverageLeading uncompensatedRemainder
    dsimp only [E0, F0, delta]
    ring

end Run
end
end InexactRealizations.Accuracy.Execution
