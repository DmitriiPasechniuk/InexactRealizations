import InexactRealizations.Accuracy.Errors.Remainders

/-! The local query residual of the actual run, with nominal leading
terms and a derived uniform quadratic remainder. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def nominalQueryLeading (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E)
    (initial target : E) (s : ℕ) : ℝ :=
  (1 - theta I N s) * ‖representedAverage (nominalStates I N H initial target s)‖ +
  3 * theta I N s * ‖Nominal.x I N H initial target s - representedAverage (nominalStates I N H initial target s)‖ +
  ‖Nominal.query I N H initial target s‖

namespace Run
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO M : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

set_option maxHeartbeats 1000000 in
theorem query_error_reference (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (s : ℕ) (hs : s < N) (hs2 : 2 ≤ s) :
    ‖v.localErrors.query s‖ ≤ u * nominalQueryLeading I N H initial target s +
      (u + uO) ^ 2 * queryRemainder I.kappa N * M := by
  let E0 := stateEnvelope I.kappa N
  let F0 := variationEnvelope I.kappa N
  let delta := u + uO
  have hE : 0 ≤ E0 := le_trans zero_le_one (stateEnvelope_one I N)
  have hF : 0 ≤ F0 := variationEnvelope_nonneg I N
  have hdelta : 0 ≤ delta := add_nonneg hu huO
  have hdFM : 0 ≤ delta * F0 * M := by positivity
  have hframe := v.operand_bounds hN hu hu2 huO huO1 hM hinitial htarget hH s hs
  have hx0 : ‖v.states s 0 - Nominal.x I N H initial target s‖ ≤ delta * F0 * M := hframe.x_close
  have hb0 : ‖representedAverage (v.states s) - representedAverage (nominalStates I N H initial target s)‖ ≤
      2 * delta * F0 * M := hframe.average_close
  have hx : ‖v.states s 0 - Nominal.x I N H initial target s‖ ≤ delta * (2 * F0 * M) := by nlinarith
  have hb : ‖representedAverage (v.states s) - representedAverage (nominalStates I N H initial target s)‖ ≤
      delta * (2 * F0 * M) := by nlinarith
  have hxs : ‖v.states s 0‖ ≤ 2 * E0 * M := by
    have hh : ‖v.states s 0‖ ≤ E0 * M := hframe.x_size
    nlinarith [mul_nonneg hE hM]
  have hbs : ‖representedAverage (v.states s)‖ ≤ 2 * E0 * M := by
    have hh := norm_add_le (v.states s 3) (v.states s 5)
    have h3 : ‖v.states s 3‖ ≤ E0 * M := hframe.raw_average_size
    have h5 : ‖v.states s 5‖ ≤ E0 * M := hframe.correction_size
    exact hh.trans (by linarith)
  let a := v.stages ⟨s, hs⟩
  let op := a.queryOperations hs2
  have ht := theta_unit I hN hs
  have hop := op.reference_error (x0 := Nominal.x I N H initial target s)
    (b0 := representedAverage (nominalStates I N H initial target s))
    (theta := theta I N s) (eps := delta) (K := 2 * F0 * M) (S := 2 * E0 * M)
    hu (by linarith) (by dsimp [delta]; linarith) ht.1.le ht.2 (p.theta_error ⟨s, hs⟩)
    (by positivity) (by positivity) hx hb (by nlinarith) (by nlinarith)
  change ‖v.query s - (Roundoff.earlierAverage v.average s + theta I N s •
    (v.x s - Roundoff.earlierAverage v.average s))‖ ≤ _
  rw [v.earlier_average s hs hs2, query, dite_eq_left hs]
  simp only [Stage.query, observedQuery, show ¬s < 2 by omega, dite_false]
  convert hop using 1
  · rfl
  · unfold nominalQueryLeading queryRemainder
    simp only [Nominal.query, Nominal.x, exactQuery, show ¬s < 2 by omega, ite_false]
    dsimp only [E0, F0]
    ring

end Run
end
end InexactRealizations.Accuracy.Execution
