import InexactRealizations.Accuracy.Errors.Remainders
import InexactRealizations.Accuracy.Execution.At

/-! Actual left-to-right Prefix arithmetic, with a single prepared beta
shared by both products. No local-error bound is assumed. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def nominalPrefixLeading (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E)
    (initial target : E) (s : ℕ) : ℝ :=
  let x := Nominal.x I N H initial target s
  let b := nominalStates I N H initial target s 1
  let g := Nominal.recovered I N H initial target s
  beta I s * ‖x - b‖ + 2 * (1 + beta I s) * ‖x‖ + beta I s * ‖b‖ +
    ‖(1 + beta I s) • x - beta I s • b‖ + 2 * alpha I s * ‖g‖ +
    ‖(1 + beta I s) • x - beta I s • b - alpha I s • g‖

namespace Run
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO M : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

set_option maxHeartbeats 2000000 in
theorem prefix_error_reference (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (s : ℕ) (hs : s < N) :
    ‖v.localErrors.state (s + 1)‖ ≤ u * nominalPrefixLeading I N H initial target s +
      (u + uO) ^ 2 * prefixRemainder I.kappa N * M := by
  let E0 := stateEnvelope I.kappa N
  let F0 := variationEnvelope I.kappa N
  let R0 := recoveryEnvelope I.kappa N
  let A := parameterBound I.kappa N
  let delta := u + uO
  have hE : 0 ≤ E0 := le_trans zero_le_one (stateEnvelope_one I N)
  have hF : 0 ≤ F0 := variationEnvelope_nonneg I N
  have hR : 0 ≤ R0 := (envelopes_nonneg I N).2.2
  have hA : 0 ≤ A := le_trans zero_le_one (parameterBound_one I N)
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hdelta : 0 ≤ delta := add_nonneg hu huO
  have ha := (alpha_bounds I s).1.le
  have hb := beta_bounds I s
  have hal : alpha I s * I.L ≤ A := alpha_scaled_bound I N s
  have hf := v.operand_bounds hN hu hu2 huO huO1 hM hinitial htarget hH s hs
  let a := v.stages ⟨s, hs⟩
  have hr : v.recovered s = a.recovered := v.recovered_at ⟨s, hs⟩
  have hg : alpha I s * ‖a.recovered - Nominal.recovered I N H initial target s‖ ≤
      delta * (A * R0 * M) := by
    rw [← hr]
    have hh := mul_le_mul_of_nonneg_left hf.recovered_close ha
    have hh' := mul_le_mul_of_nonneg_right hal (show 0 ≤ delta * R0 * M by positivity)
    nlinarith
  have hgs : alpha I s * ‖a.recovered‖ ≤ 20000000 * A ^ 2 * E0 * M := by
    rw [← hr]
    have hh := mul_le_mul_of_nonneg_left hf.recovered_size ha
    have hh' := mul_le_mul_of_nonneg_right hal (show 0 ≤ 20000000 * A * E0 * M by positivity)
    nlinarith
  let op := a.prefixOperations
  have hop := op.reference_error (x0 := Nominal.x I N H initial target s)
    (b0 := nominalStates I N H initial target s 1) (g0 := Nominal.recovered I N H initial target s)
    (alpha := alpha I s) (beta := beta I s) (eps := delta)
    (K := F0 * M) (J := A * R0 * M) (S := E0 * M) (T := 20000000 * A ^ 2 * E0 * M)
    hu (by linarith) (by dsimp [delta]; linarith) ha hb.1 hb.2.le
    (p.alpha_error ⟨s, hs⟩) (p.beta_error ⟨s, hs⟩)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (by nlinarith [hf.x_close]) (by nlinarith [hf.previous_close]) hg hf.x_size hf.previous_size hgs
  change ‖v.x (s + 1) - ((1 + beta I s) • v.x s - beta I s • v.x (s - 1) -
    alpha I s • v.recovered s)‖ ≤ _
  rw [v.state_at ⟨s, hs⟩, ← v.previous_x s hs, hr]
  convert hop using 1
  · rfl
  · unfold nominalPrefixLeading prefixRemainder
    dsimp only [E0, F0, R0, A, delta]
    ring

end Run
end
end InexactRealizations.Accuracy.Execution
