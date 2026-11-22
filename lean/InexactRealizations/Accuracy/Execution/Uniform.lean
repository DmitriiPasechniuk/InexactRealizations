import InexactRealizations.Accuracy.Execution.Nominal

/-! Uniform envelopes for every actual register, query and gradient.
All envelopes are functions only of N,kappa; the initial-size factor is
kept separate. These estimates justify the quadratic rounding remainder. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def stateEnvelope (kappa : ℝ) (N : ℕ) : ℝ := stageConstant kappa N ^ N
def variationEnvelope (kappa : ℝ) (N : ℕ) : ℝ := ((N : ℝ) + 1) * stateEnvelope kappa N
def queryEnvelope (kappa : ℝ) (N : ℕ) : ℝ := 2000 * stateEnvelope kappa N + 2 * variationEnvelope kappa N
def answerEnvelope (kappa : ℝ) (N : ℕ) : ℝ := 5000 * stateEnvelope kappa N + 2 * variationEnvelope kappa N
def recoveryEnvelope (kappa : ℝ) (N : ℕ) : ℝ :=
  20000000 * parameterBound kappa N * stateEnvelope kappa N + 5 * parameterBound kappa N * variationEnvelope kappa N

theorem stateEnvelope_one (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : 1 ≤ stateEnvelope I.kappa N :=
  one_le_pow₀ (stageConstant_one I N)

theorem variationEnvelope_nonneg (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : 0 ≤ variationEnvelope I.kappa N := by
  have he := stateEnvelope_one I N
  unfold variationEnvelope
  positivity

theorem exactQuery_sub (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (v w : State E) :
    exactQuery I N s v - exactQuery I N s w = exactQuery I N s (fun i ↦ v i - w i) := by
  by_cases hs : s < 2
  all_goals simp [exactQuery, representedAverage, hs, smul_sub]
  all_goals module

theorem exactRecovered_sub (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (v w : State E)
    (H : E →ₗ[ℝ] E) (target : E) :
    exactRecovered I N s v H target - exactRecovered I N s w H target =
      exactRecovered I N s (fun i ↦ v i - w i) H 0 := by
  by_cases hs : s < 2
  all_goals simp [exactRecovered, exactAnswer, exactQuery, representedAverage, hs, map_sub, smul_sub]
  all_goals module

namespace Run
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO M : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

theorem global_state_bound (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (n : ℕ) (hn : n ≤ N) :
    Bounded (v.states n) I.L (stateEnvelope I.kappa N * M) := by
  have hh := v.state_bound hN hu hu2 huO huO1 hM hinitial htarget hH n hn
  apply hh.mono (lt_trans I.mu_pos I.mu_lt_L).le
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (stageConstant_one I N) hn) hM

theorem global_state_close (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (n : ℕ) (hn : n ≤ N) :
    Close (v.states n) (nominalStates I N H initial target n) I.L
      ((u + uO) * variationEnvelope I.kappa N * M) := by
  have hh := v.state_close hN hu hu2 huO huO1 hM hinitial htarget hH n hn
  apply hh.mono (lt_trans I.mu_pos I.mu_lt_L).le
  have hc := stageConstant_one I N
  have hnR : (n : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast (show n ≤ N + 1 by omega)
  have hp := pow_le_pow_right₀ hc hn
  have hmul := mul_le_mul hnR hp (by positivity : 0 ≤ stageConstant I.kappa N ^ n)
    (by positivity : 0 ≤ (N : ℝ) + 1)
  have hdelta : 0 ≤ u + uO := add_nonneg hu huO
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul hdelta) hM
  simpa only [variationEnvelope, stateEnvelope, mul_assoc] using hb

theorem global_query_close (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (s : ℕ) (hs : s < N) :
    ‖v.query s - Nominal.query I N H initial target s‖ ≤ (u + uO) * queryEnvelope I.kappa N * M := by
  have he := stateEnvelope_one I N
  have hF := variationEnvelope_nonneg I N
  have hS : 0 ≤ stateEnvelope I.kappa N * M := by positivity
  have hv := v.global_state_bound hN hu hu2 huO huO1 hM hinitial htarget hH s hs.le
  have hd := v.global_state_close hN hu hu2 huO huO1 hM hinitial htarget hH s hs.le
  let a := v.stages ⟨s, hs⟩
  have hq := (a.query_size_error hN hu (by linarith) hS hv).1
  have hdiff : ‖exactQuery I N s (v.states s) - exactQuery I N s (nominalStates I N H initial target s)‖ ≤
      2 * ((u + uO) * variationEnvelope I.kappa N * M) := by
    rw [exactQuery_sub]
    exact exact_query_size hN (by positivity) hd (s := ⟨s, hs⟩)
  change ‖(if hs : s < N then (v.stages ⟨s, hs⟩).query else 0) - _‖ ≤ _
  rw [dite_eq_left hs]
  have ht : ‖a.query - Nominal.query I N H initial target s‖ ≤
      ‖a.query - exactQuery I N s (v.states s)‖ +
        ‖exactQuery I N s (v.states s) - Nominal.query I N H initial target s‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (a.query - exactQuery I N s (v.states s))
      (exactQuery I N s (v.states s) - Nominal.query I N H initial target s)
  have hsmall : 2000 * u * (stateEnvelope I.kappa N * M) ≤ 2000 * (u + uO) * (stateEnvelope I.kappa N * M) := by
    nlinarith [mul_nonneg huO hS]
  have hh := ht.trans (add_le_add (hq.trans hsmall) hdiff)
  convert hh using 1
  unfold queryEnvelope
  ring

theorem global_answer_close (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (s : ℕ) (hs : s < N) :
    ‖v.answer s - Nominal.answer I N H initial target s‖ ≤
      (u + uO) * I.L * answerEnvelope I.kappa N * M := by
  have he := stateEnvelope_one I N
  have hF := variationEnvelope_nonneg I N
  have hS : 0 ≤ stateEnvelope I.kappa N * M := by positivity
  have hD : 0 ≤ (u + uO) * variationEnvelope I.kappa N * M := by positivity
  have hv := v.global_state_bound hN hu hu2 huO huO1 hM hinitial htarget hH s hs.le
  have hd := v.global_state_close hN hu hu2 huO huO1 hM hinitial htarget hH s hs.le
  let a := v.stages ⟨s, hs⟩
  have htarg : ‖target‖ ≤ stateEnvelope I.kappa N * M := htarget.trans
    (by nlinarith [mul_le_mul_of_nonneg_right he hM])
  have hq := (a.answer_size_error hN hu (by linarith) huO huO1 hS hv hH htarg).1
  have hdiff : ‖exactAnswer I N s (v.states s) H target - Nominal.answer I N H initial target s‖ ≤
      2 * I.L * ((u + uO) * variationEnvelope I.kappa N * M) := by
    have hid : exactAnswer I N s (v.states s) H target - Nominal.answer I N H initial target s =
        H (exactQuery I N s (fun i ↦ v.states s i - nominalStates I N H initial target s i)) := by
      rw [← exactQuery_sub I N s (v.states s) (nominalStates I N H initial target s)]
      simp only [exactAnswer, Nominal.answer, map_sub]
      abel
    rw [hid]
    exact (hH _).trans (by
      have hb := exact_query_size hN hD hd (s := ⟨s, hs⟩)
      nlinarith [mul_le_mul_of_nonneg_left hb (lt_trans I.mu_pos I.mu_lt_L).le])
  change ‖(if hs : s < N then (v.stages ⟨s, hs⟩).answer else 0) - _‖ ≤ _
  rw [dite_eq_left hs]
  have ht : ‖a.answer - Nominal.answer I N H initial target s‖ ≤
      ‖a.answer - exactAnswer I N s (v.states s) H target‖ +
        ‖exactAnswer I N s (v.states s) H target - Nominal.answer I N H initial target s‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (a.answer - exactAnswer I N s (v.states s) H target)
      (exactAnswer I N s (v.states s) H target - Nominal.answer I N H initial target s)
  have hh := ht.trans (add_le_add hq hdiff)
  convert hh using 1
  unfold answerEnvelope
  ring

theorem global_recovered_close (v : Run p H initial target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hM : 0 ≤ M) (hinitial : ‖initial‖ ≤ M) (htarget : ‖target‖ ≤ M)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (s : ℕ) (hs : s < N) :
    ‖v.recovered s - Nominal.recovered I N H initial target s‖ ≤
      (u + uO) * I.L * recoveryEnvelope I.kappa N * M := by
  have he := stateEnvelope_one I N
  have hF := variationEnvelope_nonneg I N
  have hS : 0 ≤ stateEnvelope I.kappa N * M := by positivity
  have hD : 0 ≤ (u + uO) * variationEnvelope I.kappa N * M := by positivity
  have hv := v.global_state_bound hN hu hu2 huO huO1 hM hinitial htarget hH s hs.le
  have hd := v.global_state_close hN hu hu2 huO huO1 hM hinitial htarget hH s hs.le
  let a := v.stages ⟨s, hs⟩
  have htarg : ‖target‖ ≤ stateEnvelope I.kappa N * M := htarget.trans
    (by nlinarith [mul_le_mul_of_nonneg_right he hM])
  have hr := (a.recovered_size_error hN hu hu2 huO huO1 hS hv hH htarg).1
  have hdiff : ‖exactRecovered I N s (v.states s) H target - Nominal.recovered I N H initial target s‖ ≤
      5 * parameterBound I.kappa N * I.L * ((u + uO) * variationEnvelope I.kappa N * M) := by
    rw [Nominal.recovered, exactRecovered_sub]
    exact exact_recovered_size hN hD hd hH (by simpa only [norm_zero] using hD) (s := ⟨s, hs⟩)
  change ‖(if hs : s < N then (v.stages ⟨s, hs⟩).recovered else 0) - _‖ ≤ _
  rw [dite_eq_left hs]
  have ht : ‖a.recovered - Nominal.recovered I N H initial target s‖ ≤
      ‖a.recovered - exactRecovered I N s (v.states s) H target‖ +
        ‖exactRecovered I N s (v.states s) H target - Nominal.recovered I N H initial target s‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (a.recovered - exactRecovered I N s (v.states s) H target)
      (exactRecovered I N s (v.states s) H target - Nominal.recovered I N H initial target s)
  have hh := ht.trans (add_le_add hr hdiff)
  convert hh using 1
  unfold recoveryEnvelope
  ring

end Run
end
end InexactRealizations.Accuracy.Execution
