import InexactRealizations.Accuracy.Operations.Componentwise
import InexactRealizations.Accuracy.CompensatedAccuracy

/-! Article-facing execution model: each individual vector instruction
has componentwise relative error <=u. The normwise records used in the
proof are constructed from those assumptions, not additionally assumed. 
-/
namespace InexactRealizations.Accuracy.Componentwise
noncomputable section
open InexactRealizations.Accuracy.Execution
variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ ι

structure Stage {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u : ℝ}
    (p : Prepared I N u) (s : Fin N) (v : State V) (H : V →ₗ[ℝ] V) (target : V) (uO : ℝ) (hu : 0 ≤ u) where
  queryOperations : 2 ≤ s.val → QueryStep (v 0) (representedAverage v) (p.theta s) u
  noise : V
  noise_bound : ‖noise‖ ≤ uO * (I.L * ‖observedQuery s v (p.theta s) u
    (fun hs ↦ (queryOperations hs).toNormed hu)‖ + ‖H target‖)
  recoveryOperations : 2 ≤ s.val → RecoveryStep
    (observedAnswer s v (p.theta s) u (fun hs ↦ (queryOperations hs).toNormed hu) H target noise)
    (v 7) (p.theta s) u
  averageOperations : 2 ≤ s.val → s.val + 2 < N →
    Sum (CompensatedStep (v 0) (v 3) (v 5) (InexactRealizations.Algorithms.AveragedBalanced.phi I N s.val) (p.phi s) u)
      (BlendStep (v 0) (representedAverage v) (p.phi s) u)
  gradientOperations : 2 ≤ s.val → s.val + 2 < N → BlendStep
    (observedRecovered s v (p.theta s) u
      (observedAnswer s v (p.theta s) u (fun hs ↦ (queryOperations hs).toNormed hu) H target noise)
      (fun hs ↦ (recoveryOperations hs).toNormed hu)) (v 7) (p.phi s) u
  prefixOperations : PrefixStep (v 0) (v 1)
    (observedRecovered s v (p.theta s) u
      (observedAnswer s v (p.theta s) u (fun hs ↦ (queryOperations hs).toNormed hu) H target noise)
      (fun hs ↦ (recoveryOperations hs).toNormed hu)) (p.alpha s) (p.beta s) u

def Stage.toNormed {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ} {p : Prepared I N u}
    {s : Fin N} {v : State V} {H : V →ₗ[ℝ] V} {target : V} {hu : 0 ≤ u}
    (a : Stage p s v H target uO hu) : Execution.Stage p s v H target uO where
  queryOperations hs := (a.queryOperations hs).toNormed hu
  noise := a.noise
  noise_bound := a.noise_bound
  recoveryOperations hs := (a.recoveryOperations hs).toNormed hu
  averageOperations hs hv := match a.averageOperations hs hv with
    | .inl op => .inl (op.toNormed hu)
    | .inr op => .inr (op.toNormed hu)
  gradientOperations hs hv := (a.gradientOperations hs hv).toNormed hu
  prefixOperations := a.prefixOperations.toNormed hu

structure Run {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u : ℝ}
    (p : Prepared I N u) (H : V →ₗ[ℝ] V) (initial target : V) (uO : ℝ) (hu : 0 ≤ u) where
  states : ℕ → State V
  initial_eq : states 0 = initialState initial
  stages : ∀ s : Fin N, Stage p s (states s.val) H target uO hu
  step_eq : ∀ s : Fin N, states (s.val + 1) = (stages s).toNormed.output

def Run.toNormed {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ} {p : Prepared I N u}
    {H : V →ₗ[ℝ] V} {initial target : V} {hu : 0 ≤ u}
    (v : Run p H initial target uO hu) : Execution.Run p H initial target uO where
  states := v.states
  initial_eq := v.initial_eq
  stages s := (v.stages s).toNormed
  step_eq := v.step_eq

theorem compensated_accuracy {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ} {p : Prepared I N u}
    {H : V →ₗ[ℝ] V} {initial target : V} {hu : 0 ≤ u}
    (v : Run p H initial target uO hu) (hc : v.toNormed.Compensated) (hN : 2 ≤ N)
    (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1) (hH : InexactRealizations.Analysis.Admissible I H) :
    ‖v.states N 0 - target‖ ≤
      I.epsilon N * (1 + cubicConstant I.kappa * (u + uO) * (N : ℝ) ^ 3) * ‖initial - target‖ +
      (2 * (u + uO) * I.L * InexactRealizations.Lower.additiveScale I N + 8 * u * prefixFactor I N) * ‖target‖ +
      (u + uO) ^ 2 * quadraticConstant I.kappa N * (‖initial - target‖ + ‖target‖) :=
  Execution.compensated_accuracy v.toNormed hc hN hu hu2 huO huO1 hH

end
end InexactRealizations.Accuracy.Componentwise
