import InexactRealizations.Accuracy.Bounds.StageUpdates
import InexactRealizations.Accuracy.Bounds.StagePrefix

/-! A uniform bound and defect estimate for one complete rounded stage.
The constant depends only on N and kappa; the natural L scaling of
gradient registers is retained throughout. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO S : ℝ} {p : Prepared I N u}
  {s : Fin N} {v : State E} {H : E →ₗ[ℝ] E} {target : E}

def stageConstant (kappa : ℝ) (N : ℕ) : ℝ := 1000000000000 * (parameterBound kappa N) ^ 2

theorem stageConstant_one (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : 1 ≤ stageConstant I.kappa N := by
  have h := parameterBound_one I N
  unfold stageConstant
  nlinarith

set_option maxHeartbeats 1000000 in
theorem Stage.uniform_size (a : Stage p s v H target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hS : 0 ≤ S) (hv : Bounded v I.L S) (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (htarget : ‖target‖ ≤ S) :
    Bounded a.output I.L (stageConstant I.kappa N * S) := by
  let A := parameterBound I.kappa N
  let C := stageConstant I.kappa N
  have hA : 1 ≤ A := parameterBound_one I N
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hAA : A ≤ A ^ 2 := by nlinarith
  have hC : 1 ≤ C := stageConstant_one I N
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hu1 : u ≤ 1 := by linarith
  have hcopy : S ≤ C * S := by nlinarith [mul_le_mul_of_nonneg_right hC hS]
  have hp := a.prefix_size_error hN hu hu2 huO huO1 hS hv hH htarget
  have ha := a.averages_size_error hN hu hu1 hS hv
  have hg := a.gradient_size_error hN hu hu2 huO huO1 hS hv hH htarget
  have hX : ‖a.prefixOperations.result‖ ≤ C * S := by
    have hb : (50000000000 : ℝ) * A ^ 2 ≤ C := by dsimp [C, stageConstant, A]; nlinarith [sq_nonneg (parameterBound I.kappa N)]
    exact hp.2.trans (mul_le_mul_of_nonneg_right hb hS)
  have havg : ‖a.nextAverage‖ ≤ C * S := by
    have hb : (10000 : ℝ) ≤ C := by dsimp [C, stageConstant]; nlinarith
    exact ha.2.2.1.trans (mul_le_mul_of_nonneg_right hb hS)
  have hcorr : ‖a.nextCorrection‖ ≤ C * S := by
    have hb : (1000 : ℝ) ≤ C := by dsimp [C, stageConstant]; nlinarith
    exact ha.2.2.2.trans (mul_le_mul_of_nonneg_right hb hS)
  have hgrad : ‖a.nextGradient‖ ≤ I.L * (C * S) := by
    have hb : (4000000000 : ℝ) * A ≤ C := by dsimp [C, stageConstant]; nlinarith
    have hh := mul_le_mul_of_nonneg_right hb (mul_nonneg hL hS)
    have hhg := hg.2
    change ‖a.nextGradient‖ ≤ 4000000000 * A * I.L * S at hhg
    nlinarith
  have hvg : ‖v 6‖ ≤ I.L * (C * S) := by
    have hh := mul_le_mul_of_nonneg_left hcopy hL
    exact (hv.gradient 6 (by decide)).trans hh
  intro i
  fin_cases i
  · simpa [Stage.output, weight] using hX
  · simpa [Stage.output, weight] using (hv.scalar 0 (by decide)).trans hcopy
  · simpa [Stage.output, weight] using havg
  · simpa [Stage.output, weight] using (hv.scalar 2 (by decide)).trans hcopy
  · simpa [Stage.output, weight] using hcorr
  · simpa [Stage.output, weight] using (hv.scalar 4 (by decide)).trans hcopy
  · simpa [Stage.output, weight] using hgrad
  · simpa [Stage.output, weight] using hvg

set_option maxHeartbeats 1000000 in
theorem Stage.uniform_defect (a : Stage p s v H target uO) (hN : 2 ≤ N)
    (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hS : 0 ≤ S) (hv : Bounded v I.L S) (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (htarget : ‖target‖ ≤ S) :
    Close a.output (exactStep I N s.val v H target) I.L (stageConstant I.kappa N * (u + uO) * S) := by
  let A := parameterBound I.kappa N
  let C := stageConstant I.kappa N
  have hA : 1 ≤ A := parameterBound_one I N
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have hAA : A ≤ A ^ 2 := by nlinarith
  have hC : 1 ≤ C := stageConstant_one I N
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hu1 : u ≤ 1 := by linarith
  have hdelta : 0 ≤ (u + uO) * S := by positivity
  have hdeltaL : 0 ≤ (u + uO) * I.L * S := by positivity
  have hzero : 0 ≤ C * (u + uO) * S := by positivity
  have hzeroG : 0 ≤ I.L * (C * (u + uO) * S) := by positivity
  have hp := a.prefix_size_error hN hu hu2 huO huO1 hS hv hH htarget
  have ha := a.averages_size_error hN hu hu1 hS hv
  have hg := a.gradient_size_error hN hu hu2 huO huO1 hS hv hH htarget
  have hX : ‖a.prefixOperations.result - exactStep I N s.val v H target 0‖ ≤ C * (u + uO) * S := by
    have hb : (40000000000 : ℝ) * A ^ 2 ≤ C := by dsimp [C, stageConstant, A]; nlinarith [sq_nonneg (parameterBound I.kappa N)]
    have hh := mul_le_mul_of_nonneg_right hb hdelta
    have hhx := hp.1
    change ‖a.prefixOperations.result - exactStep I N s.val v H target 0‖ ≤ 40000000000 * A ^ 2 * (u + uO) * S at hhx
    nlinarith
  have havg : ‖a.nextAverage - exactStep I N s.val v H target 2‖ ≤ C * (u + uO) * S := by
    have hb : (6000 : ℝ) ≤ C := by dsimp [C, stageConstant]; nlinarith
    have hh := mul_le_mul_of_nonneg_right hb hdelta
    nlinarith [ha.1, mul_nonneg huO hS]
  have hcorr : ‖a.nextCorrection - exactStep I N s.val v H target 4‖ ≤ C * (u + uO) * S := by
    have hb : (600 : ℝ) ≤ C := by dsimp [C, stageConstant]; nlinarith
    have hh := mul_le_mul_of_nonneg_right hb hdelta
    nlinarith [ha.2.1, mul_nonneg huO hS]
  have hgrad : ‖a.nextGradient - exactStep I N s.val v H target 6‖ ≤ I.L * (C * (u + uO) * S) := by
    have hb : (3000000000 : ℝ) * A ≤ C := by dsimp [C, stageConstant]; nlinarith
    have hh := mul_le_mul_of_nonneg_right hb hdeltaL
    have hhg := hg.1
    change ‖a.nextGradient - exactStep I N s.val v H target 6‖ ≤ 3000000000 * A * (u + uO) * I.L * S at hhg
    nlinarith
  intro i
  fin_cases i
  · simpa [Stage.output, weight] using hX
  · simpa [Stage.output, exactStep, weight] using hzero
  · simpa [Stage.output, weight] using havg
  · simpa [Stage.output, exactStep, weight] using hzero
  · simpa [Stage.output, weight] using hcorr
  · simpa [Stage.output, exactStep, weight] using hzero
  · simpa [Stage.output, weight] using hgrad
  · simpa [Stage.output, exactStep, weight] using hzeroG

end
end InexactRealizations.Accuracy.Execution
