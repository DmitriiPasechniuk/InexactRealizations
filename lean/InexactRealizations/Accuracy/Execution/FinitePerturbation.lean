import InexactRealizations.Accuracy.Execution.Run
import InexactRealizations.Accuracy.Execution.Unrounded

/-! Uniform finite-horizon propagation. Actual register bounds and their
distance from the nominal execution are proved by finite induction from
the operation model. No local-error or terminal-error certificate is assumed. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def nominalStates (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E) (initial target : E) : ℕ → State E
  | 0 => initialState initial
  | s + 1 => exactStep I N s (nominalStates I N H initial target s) H target

omit [NormedSpace ℝ E] in
theorem initialState_bounded (initial : E) {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hi : ‖initial‖ ≤ M) :
    Bounded (initialState initial) L M := by
  intro i
  fin_cases i <;> simp [initialState, weight, hi, hM, mul_nonneg hL hM]

namespace Run
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO M : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

theorem state_bound (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (n : ℕ) (hn : n ≤ N) :
    Bounded (v.states n) I.L ((stageConstant I.kappa N) ^ n * M) := by
  let C := stageConstant I.kappa N
  have hC : 1 ≤ C := stageConstant_one I N
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  change Bounded (v.states n) I.L (C ^ n * M)
  induction n with
  | zero =>
    rw [v.initial_eq]
    simpa only [pow_zero, one_mul] using initialState_bounded initial hL hM hinitial
  | succ n ih =>
    have hlt : n < N := by omega
    have hv := ih (by omega)
    have hp : 1 ≤ C ^ n := one_le_pow₀ hC
    have ht : ‖target‖ ≤ C ^ n * M := htarget.trans (by nlinarith [mul_le_mul_of_nonneg_right hp hM])
    have hh := (v.stages ⟨n, hlt⟩).uniform_size hN hu hu2 huO huO1
      (by positivity : 0 ≤ C ^ n * M) hv hH ht
    rw [v.step_eq ⟨n, hlt⟩]
    convert hh using 1
    rw [pow_succ]
    ring

theorem state_close (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (n : ℕ) (hn : n ≤ N) :
    Close (v.states n) (nominalStates I N H initial target n) I.L
      ((u + uO) * n * (stageConstant I.kappa N) ^ n * M) := by
  let C := stageConstant I.kappa N
  have hC : 1 ≤ C := stageConstant_one I N
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  change Close (v.states n) (nominalStates I N H initial target n) I.L ((u + uO) * n * C ^ n * M)
  induction n with
  | zero =>
    intro i
    rw [v.initial_eq]
    simp [nominalStates]
  | succ n ih =>
    have hlt : n < N := by omega
    have hc := ih (by omega)
    have hv := v.state_bound hN hu hu2 huO huO1 hM hinitial htarget hH n (by omega)
    have hp : 1 ≤ C ^ n := one_le_pow₀ hC
    have ht : ‖target‖ ≤ C ^ n * M := htarget.trans (by nlinarith [mul_le_mul_of_nonneg_right hp hM])
    have h1 := (v.stages ⟨n, hlt⟩).uniform_defect hN hu hu2 huO huO1
      (by positivity : 0 ≤ C ^ n * M) hv hH ht
    have h2 := exactStep_lipschitz target hN ⟨n, hlt⟩
      (by positivity : 0 ≤ (u + uO) * (n : ℝ) * C ^ n * M) hc hH
    have hh := h1.trans h2
    rw [v.step_eq ⟨n, hlt⟩, nominalStates]
    convert hh using 1
    push_cast
    rw [pow_succ]
    ring

end Run
end
end InexactRealizations.Accuracy.Execution
