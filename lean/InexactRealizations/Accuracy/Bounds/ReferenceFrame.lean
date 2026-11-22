import InexactRealizations.Accuracy.Execution.Startup
import InexactRealizations.Accuracy.Execution.NominalIdentities

/-! Operand estimates derived from the actual run, collected for the
local first-order comparisons. This structure is a proved conclusion,
never an additional hypothesis in the article-facing accuracy theorem. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO M : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

structure OperandBounds (v : Run p H initial target uO) (s : ℕ) (M : ℝ) : Prop where
  x_close : ‖v.states s 0 - Nominal.x I N H initial target s‖ ≤ (u + uO) * variationEnvelope I.kappa N * M
  previous_close : ‖v.states s 1 - nominalStates I N H initial target s 1‖ ≤ (u + uO) * variationEnvelope I.kappa N * M
  average_close : ‖representedAverage (v.states s) - representedAverage (nominalStates I N H initial target s)‖ ≤
    2 * (u + uO) * variationEnvelope I.kappa N * M
  old_gradient_close : ‖v.states s 7 - nominalStates I N H initial target s 7‖ ≤
    I.L * ((u + uO) * variationEnvelope I.kappa N * M)
  answer_close : ‖v.answer s - Nominal.answer I N H initial target s‖ ≤ (u + uO) * I.L * answerEnvelope I.kappa N * M
  recovered_close : ‖v.recovered s - Nominal.recovered I N H initial target s‖ ≤
    (u + uO) * I.L * recoveryEnvelope I.kappa N * M
  x_size : ‖v.states s 0‖ ≤ stateEnvelope I.kappa N * M
  previous_size : ‖v.states s 1‖ ≤ stateEnvelope I.kappa N * M
  raw_average_size : ‖v.states s 3‖ ≤ stateEnvelope I.kappa N * M
  correction_size : ‖v.states s 5‖ ≤ stateEnvelope I.kappa N * M
  old_gradient_size : ‖v.states s 7‖ ≤ I.L * (stateEnvelope I.kappa N * M)
  answer_size : ‖v.answer s‖ ≤ 10000 * I.L * (stateEnvelope I.kappa N * M)
  recovered_size : ‖v.recovered s‖ ≤ 20000000 * parameterBound I.kappa N * I.L * (stateEnvelope I.kappa N * M)
  correction_small : ‖v.states s 5‖ ≤ u * (600 * stateEnvelope I.kappa N * M)

set_option maxHeartbeats 1000000 in
theorem Run.operand_bounds (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (s : ℕ) (hs : s < N) : OperandBounds v s M := by
  have he := stateEnvelope_one I N
  have hv := v.global_state_bound hN hu hu2 huO huO1 hM hinitial htarget hH s hs.le
  have hd := v.global_state_close hN hu hu2 huO huO1 hM hinitial htarget hH s hs.le
  have hS : 0 ≤ stateEnvelope I.kappa N * M := by positivity
  have htarg : ‖target‖ ≤ stateEnvelope I.kappa N * M := htarget.trans
    (by nlinarith [mul_le_mul_of_nonneg_right he hM])
  have hu1 : u ≤ 1 := by linarith
  let a := v.stages ⟨s, hs⟩
  have hans : ‖v.answer s‖ ≤ 10000 * I.L * (stateEnvelope I.kappa N * M) := by
    change ‖(if hs : s < N then (v.stages ⟨s, hs⟩).answer else 0)‖ ≤ _
    rw [dite_eq_left hs]
    exact (a.answer_size_error hN hu hu1 huO huO1 hS hv hH htarg).2
  have hrec : ‖v.recovered s‖ ≤ 20000000 * parameterBound I.kappa N * I.L * (stateEnvelope I.kappa N * M) := by
    change ‖(if hs : s < N then (v.stages ⟨s, hs⟩).recovered else 0)‖ ≤ _
    rw [dite_eq_left hs]
    exact (a.recovered_size_error hN hu hu2 huO huO1 hS hv hH htarg).2
  refine ⟨Bounded.scalar hd 0 (by decide), Bounded.scalar hd 1 (by decide), ?_,
    Bounded.gradient hd 7 (by decide),
    v.global_answer_close hN hu hu2 huO huO1 hM hinitial htarget hH s hs,
    v.global_recovered_close hN hu hu2 huO huO1 hM hinitial htarget hH s hs,
    hv.scalar 0 (by decide), hv.scalar 1 (by decide), hv.scalar 3 (by decide), hv.scalar 5 (by decide),
    hv.gradient 7 (by decide), hans, hrec,
    v.older_correction_bound hN hu hu2 huO huO1 hM hinitial htarget hH s hs⟩
  have h3 := Bounded.scalar hd 3 (by decide)
  have h5 := Bounded.scalar hd 5 (by decide)
  have heq : representedAverage (v.states s) - representedAverage (nominalStates I N H initial target s) =
      (v.states s 3 - nominalStates I N H initial target s 3) +
      (v.states s 5 - nominalStates I N H initial target s 5) := by unfold representedAverage; abel
  rw [heq]
  nlinarith [norm_add_le (v.states s 3 - nominalStates I N H initial target s 3)
    (v.states s 5 - nominalStates I N H initial target s 5)]

end
end InexactRealizations.Accuracy.Execution
