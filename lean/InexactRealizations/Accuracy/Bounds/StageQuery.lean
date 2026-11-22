import InexactRealizations.Accuracy.Bounds.State
import InexactRealizations.Accuracy.Bounds.Parameters

/-! Query and oracle perturbation at one actual rounded stage. -/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO S : ℝ} {p : Prepared I N u}
  {s : Fin N} {v : State E} {H : E →ₗ[ℝ] E} {target : E}

theorem exact_query_size (hN : 2 ≤ N) (hS : 0 ≤ S) (hv : Bounded v I.L S) :
    ‖exactQuery I N s.val v‖ ≤ 2 * S := by
  have hx := hv.scalar 0 (by decide)
  have hb : ‖representedAverage v‖ ≤ 2 * S := by
    exact (norm_add_le _ _).trans (by linarith [hv.scalar 3 (by decide), hv.scalar 5 (by decide)])
  unfold exactQuery
  split_ifs
  · linarith
  · exact affine_size _ (theta_unit I hN s.isLt).1.le (theta_unit I hN s.isLt).2 _ _ _ (by linarith) hb

theorem Stage.query_size_error (a : Stage p s v H target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hS : 0 ≤ S) (hv : Bounded v I.L S) :
    ‖a.query - exactQuery I N s.val v‖ ≤ 2000 * u * S ∧ ‖a.query‖ ≤ 4000 * S := by
  have hx := hv.scalar 0 (by decide)
  by_cases hs : s.val < 2
  · simp only [Stage.query, observedQuery, hs, dite_true, exactQuery, ite_true, sub_self, norm_zero]
    constructor <;> nlinarith
  · have hb : ‖representedAverage v‖ ≤ 2 * S := by
      exact (norm_add_le _ _).trans (by linarith [hv.scalar 3 (by decide), hv.scalar 5 (by decide)])
    have hh := (a.queryOperations (by omega)).coarse hu hu1 (theta_unit I hN s.isLt).1.le
      (theta_unit I hN s.isLt).2 (p.theta_error s) (by positivity : 0 ≤ 2 * S) (by linarith : ‖v 0‖ ≤ 2 * S) hb
    change ‖observedQuery s v (p.theta s) u a.queryOperations - _‖ ≤ _ ∧
      ‖observedQuery s v (p.theta s) u a.queryOperations‖ ≤ _
    simp only [observedQuery, hs, dite_false, exactQuery, ite_false]
    constructor <;> nlinarith [hh.1, hh.2]

theorem Stage.noise_size (a : Stage p s v H target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (huO : 0 ≤ uO) (hS : 0 ≤ S) (hv : Bounded v I.L S)
    (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (htarget : ‖target‖ ≤ S) :
    ‖a.noise‖ ≤ 4001 * uO * I.L * S := by
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hq := (a.query_size_error hN hu hu1 hS hv).2
  have ht := (hH target).trans (mul_le_mul_of_nonneg_left htarget hL)
  have hb : I.L * ‖a.query‖ + ‖H target‖ ≤ 4001 * I.L * S := by
    nlinarith [mul_le_mul_of_nonneg_left hq hL]
  calc
    _ ≤ uO * (I.L * ‖a.query‖ + ‖H target‖) := a.noise_bound
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hb huO]

theorem Stage.answer_size_error (a : Stage p s v H target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hS : 0 ≤ S) (hv : Bounded v I.L S) (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (htarget : ‖target‖ ≤ S) :
    ‖a.answer - exactAnswer I N s.val v H target‖ ≤ 5000 * (u + uO) * I.L * S ∧
      ‖a.answer‖ ≤ 10000 * I.L * S := by
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hq := a.query_size_error hN hu hu1 hS hv
  have hn := a.noise_size hN hu hu1 huO hS hv hH htarget
  have he : a.answer - exactAnswer I N s.val v H target =
      H (a.query - exactQuery I N s.val v) + a.noise := by
    simp only [Stage.answer, observedAnswer, Stage.query, exactAnswer, map_sub]
    abel
  have hnom : ‖exactAnswer I N s.val v H target‖ ≤ 3 * I.L * S := by
    have hquery := exact_query_size hN hS hv (s := s)
    exact (hH _).trans (by nlinarith [mul_le_mul_of_nonneg_left (norm_sub_le (exactQuery I N s.val v) target) hL])
  have herr : ‖a.answer - exactAnswer I N s.val v H target‖ ≤ 5000 * (u + uO) * I.L * S := by
    rw [he]
    have hh := (norm_add_le (H (a.query - exactQuery I N s.val v)) a.noise).trans (add_le_add (hH _) hn)
    nlinarith [mul_le_mul_of_nonneg_left hq.1 hL, mul_nonneg hu (mul_nonneg hL hS),
      mul_nonneg huO (mul_nonneg hL hS)]
  refine ⟨herr, ?_⟩
  have hact : ‖a.answer‖ ≤ I.L * (‖a.query‖ + ‖target‖) + ‖a.noise‖ := by
    change ‖H (a.query - target) + a.noise‖ ≤ _
    exact (norm_add_le _ _).trans (add_le_add ((hH _).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hL)) le_rfl)
  nlinarith [mul_le_mul_of_nonneg_left hq.2 hL,
    mul_le_mul_of_nonneg_right huO1 (mul_nonneg hL hS)]

end
end InexactRealizations.Accuracy.Execution
