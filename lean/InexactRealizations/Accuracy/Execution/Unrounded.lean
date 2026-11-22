import InexactRealizations.Accuracy.Bounds.StageUniform

/-! Zero-roundoff operations and the exact affine state map. This gives
the nominal execution and its dimension-independent Lipschitz estimate
without an external stability or differentiability assumption. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def QueryStep.unrounded (x b : E) (theta : ℝ) : QueryStep x b theta 0 where
  start := b
  difference := x - b
  product := theta • (x - b)
  result := b + theta • (x - b)
  start_error := by simp
  difference_error := by simp
  product_error := by simp
  result_error := by simp

def RecoveryStep.unrounded (g b : E) (theta : ℝ) : RecoveryStep g b theta 0 where
  difference := g - b
  quotient := theta⁻¹ • (g - b)
  result := b + theta⁻¹ • (g - b)
  difference_error := by simp
  quotient_error := by simp
  result_error := by simp

def BlendStep.unrounded (x b : E) (phi : ℝ) : BlendStep x b phi 0 where
  difference := x - b
  product := phi • (x - b)
  result := b + phi • (x - b)
  difference_error := by simp
  product_error := by simp
  result_error := by simp

def CompensatedStep.unrounded (x b c : E) (phi : ℝ) : CompensatedStep x b c phi phi 0 where
  difference := x - b
  corrected := (x - b) - c
  product := phi • ((x - b) - c)
  a := c + phi • ((x - b) - c)
  c := b + (c + phi • ((x - b) - c))
  d := c + phi • ((x - b) - c)
  nextCorrection := 0
  difference_error := by simp
  corrected_error := by simp
  product_error := by simp
  a_error := by simp
  c_error := by simp
  d_error := by simp
  correction_error := by simp

def PrefixStep.unrounded (x previous gradient : E) (alpha beta : ℝ) : PrefixStep x previous gradient alpha beta 0 where
  onePlusBeta := 1 + beta
  currentProduct := (1 + beta) • x
  previousProduct := beta • previous
  difference := (1 + beta) • x - beta • previous
  gradientProduct := alpha • gradient
  result := (1 + beta) • x - beta • previous - alpha • gradient
  one_error := by simp
  current_error := by simp
  previous_error := by simp
  difference_error := by simp
  gradient_error := by simp
  result_error := by simp

namespace Execution
open InexactRealizations.Algorithms.AveragedBalanced

def Prepared.unrounded (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : Prepared I N 0 where
  alpha s := InexactRealizations.Algorithms.AveragedBalanced.alpha I s.val
  beta s := InexactRealizations.Algorithms.AveragedBalanced.beta I s.val
  theta s := InexactRealizations.Algorithms.AveragedBalanced.theta I N s.val
  phi s := InexactRealizations.Algorithms.AveragedBalanced.phi I N s.val
  alpha_error _ := by simp
  beta_error _ := by simp
  theta_error _ := by simp
  phi_error _ _ := by simp

def Stage.unrounded (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (s : Fin N) (v : State E)
    (H : E →ₗ[ℝ] E) (target : E) : Stage (Prepared.unrounded I N) s v H target 0 where
  queryOperations _ := QueryStep.unrounded _ _ _
  noise := 0
  noise_bound := by simp
  recoveryOperations _ := RecoveryStep.unrounded _ _ _
  averageOperations _ _ := .inl (CompensatedStep.unrounded _ _ _ _)
  gradientOperations _ _ := BlendStep.unrounded _ _ _
  prefixOperations := PrefixStep.unrounded _ _ _ _ _

set_option maxHeartbeats 2000000 in
theorem Stage.unrounded_output (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (s : Fin N) (v : State E)
    (H : E →ₗ[ℝ] E) (target : E) :
    (Stage.unrounded I s v H target).output = exactStep I N s.val v H target := by
  by_cases hs : s.val < 2 <;> by_cases hv : s.val + 2 < N
  all_goals
    ext i
    fin_cases i <;>
      simp [Stage.unrounded, Prepared.unrounded, Stage.output, Stage.nextAverage, Stage.nextCorrection,
        Stage.nextGradient, Stage.answer, observedQuery, observedAnswer,
        observedRecovered, QueryStep.unrounded, RecoveryStep.unrounded, CompensatedStep.unrounded,
        BlendStep.unrounded, PrefixStep.unrounded, exactStep, exactRecovered, exactAnswer, exactQuery,
        representedAverage, hs, hv]
  all_goals module

set_option maxHeartbeats 2000000 in
theorem exactStep_sub (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (v w : State E)
    (H : E →ₗ[ℝ] E) (target : E) :
    (fun i ↦ exactStep I N s v H target i - exactStep I N s w H target i) =
      exactStep I N s (fun i ↦ v i - w i) H 0 := by
  by_cases hs : s < 2 <;> by_cases hv : s + 2 < N
  all_goals
    ext i
    fin_cases i <;>
      simp [exactStep, exactRecovered, exactAnswer, exactQuery, representedAverage, hs, hv,
        map_add, map_sub, map_smul, smul_add, smul_sub]
  all_goals module

theorem exactStep_bounded {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {H : E →ₗ[ℝ] E}
    {target : E} {v : State E} {S : ℝ} (hN : 2 ≤ N) (s : Fin N)
    (hS : 0 ≤ S) (hv : Bounded v I.L S) (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) (htarget : ‖target‖ ≤ S) :
    Bounded (exactStep I N s.val v H target) I.L (stageConstant I.kappa N * S) := by
  rw [← Stage.unrounded_output I s v H target]
  exact (Stage.unrounded I s v H target).uniform_size hN (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hS hv hH htarget

theorem exactStep_lipschitz {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {H : E →ₗ[ℝ] E}
    (target : E) {v w : State E} {D : ℝ} (hN : 2 ≤ N) (s : Fin N)
    (hD : 0 ≤ D) (hv : Close v w I.L D) (hH : ∀ z : E, ‖H z‖ ≤ I.L * ‖z‖) :
    Close (exactStep I N s.val v H target) (exactStep I N s.val w H target) I.L
      (stageConstant I.kappa N * D) := by
  change Bounded (fun i ↦ exactStep I N s.val v H target i - exactStep I N s.val w H target i) I.L _
  rw [exactStep_sub]
  exact exactStep_bounded hN s hD hv hH (by simpa only [norm_zero] using hD)

end Execution
end
end InexactRealizations.Accuracy
