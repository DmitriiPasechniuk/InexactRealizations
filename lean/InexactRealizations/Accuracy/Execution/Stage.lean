import InexactRealizations.Accuracy.Operations.CoarseState
import InexactRealizations.Algorithms.AveragedBalancedBounds

/-! Literal rounded execution. The eight persistent vectors
are indexed by age: X,X', recent/older averages, recent/older corrections,
recent/older gradients. The query/answer temporary Y is contained in the
operation records. Swapping the two age slots each call is exactly the
printed parity indexing; no update is introduced on an unused slot.
The average operation is tagged as compensated or uncompensated, to cover
both parts with the same propagation estimates. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms InexactRealizations.Algorithms.AveragedBalanced
abbrev State (E : Type*) := Fin 8 → E
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure Prepared (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (u : ℝ) where
  alpha : Fin N → ℝ
  beta : Fin N → ℝ
  theta : Fin N → ℝ
  phi : Fin N → ℝ
  alpha_error : ∀ s, |alpha s - AveragedBalanced.alpha I s.val| ≤ u * AveragedBalanced.alpha I s.val
  beta_error : ∀ s, |beta s - AveragedBalanced.beta I s.val| ≤ u * AveragedBalanced.beta I s.val
  theta_error : ∀ s, |theta s - AveragedBalanced.theta I N s.val| ≤ u * AveragedBalanced.theta I N s.val
  phi_error : ∀ s, s.val + 2 < N →
    |phi s - AveragedBalanced.phi I N s.val| ≤ u * AveragedBalanced.phi I N s.val

def representedAverage (v : State E) : E := v 3 + v 5

def observedQuery {N : ℕ} (s : Fin N) (v : State E) (prepared u : ℝ)
    (ops : 2 ≤ s.val → QueryStep (v 0) (representedAverage v) prepared u) : E :=
  if hs : s.val < 2 then v 0 else (ops (by omega)).result

def observedAnswer {N : ℕ} (s : Fin N) (v : State E) (prepared u : ℝ)
    (ops : 2 ≤ s.val → QueryStep (v 0) (representedAverage v) prepared u)
    (H : E →ₗ[ℝ] E) (target noise : E) : E :=
  H (observedQuery s v prepared u ops - target) + noise

def observedRecovered {N : ℕ} (s : Fin N) (v : State E) (prepared u : ℝ) (g : E)
    (ops : 2 ≤ s.val → RecoveryStep g (v 7) prepared u) : E :=
  if hs : s.val < 2 then g else (ops (by omega)).result

structure Stage {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u : ℝ}
    (p : Prepared I N u) (s : Fin N) (v : State E) (H : E →ₗ[ℝ] E) (target : E) (uO : ℝ) where
  queryOperations : 2 ≤ s.val → QueryStep (v 0) (representedAverage v) (p.theta s) u
  noise : E
  noise_bound : ‖noise‖ ≤ uO * (I.L * ‖observedQuery s v (p.theta s) u queryOperations‖ + ‖H target‖)
  recoveryOperations : 2 ≤ s.val → RecoveryStep
    (observedAnswer s v (p.theta s) u queryOperations H target noise) (v 7) (p.theta s) u
  averageOperations : 2 ≤ s.val → s.val + 2 < N →
    Sum (CompensatedStep (v 0) (v 3) (v 5) (AveragedBalanced.phi I N s.val) (p.phi s) u)
      (BlendStep (v 0) (representedAverage v) (p.phi s) u)
  gradientOperations : 2 ≤ s.val → s.val + 2 < N → BlendStep
    (observedRecovered s v (p.theta s) u
      (observedAnswer s v (p.theta s) u queryOperations H target noise) recoveryOperations)
    (v 7) (p.phi s) u
  prefixOperations : PrefixStep (v 0) (v 1)
    (observedRecovered s v (p.theta s) u
      (observedAnswer s v (p.theta s) u queryOperations H target noise) recoveryOperations)
    (p.alpha s) (p.beta s) u

namespace Stage
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ} {p : Prepared I N u}
  {s : Fin N} {v : State E} {H : E →ₗ[ℝ] E} {target : E}

def query (a : Stage p s v H target uO) : E := observedQuery s v (p.theta s) u a.queryOperations
def answer (a : Stage p s v H target uO) : E := observedAnswer s v (p.theta s) u a.queryOperations H target a.noise
def recovered (a : Stage p s v H target uO) : E := observedRecovered s v (p.theta s) u a.answer a.recoveryOperations
def nextAverage (a : Stage p s v H target uO) : E :=
  if hv : s.val + 2 < N then if hs : s.val < 2 then v 0 else
    match a.averageOperations (by omega) hv with
    | .inl op => op.c
    | .inr op => op.result
  else v 3
def nextCorrection (a : Stage p s v H target uO) : E :=
  if hv : s.val + 2 < N then if hs : s.val < 2 then 0 else
    match a.averageOperations (by omega) hv with
    | .inl op => op.nextCorrection
    | .inr _ => 0
  else v 5
def nextGradient (a : Stage p s v H target uO) : E :=
  if hv : s.val + 2 < N then if hs : s.val < 2 then a.answer else (a.gradientOperations (by omega) hv).result else v 7
def output (a : Stage p s v H target uO) : State E :=
  ![a.prefixOperations.result, v 0, a.nextAverage, v 2, a.nextCorrection, v 4, a.nextGradient, v 6]

def Compensated (a : Stage p s v H target uO) : Prop :=
  ∀ (hs : 2 ≤ s.val) (hv : s.val + 2 < N), ∃ op, a.averageOperations hs hv = Sum.inl op

def Uncompensated (a : Stage p s v H target uO) : Prop :=
  ∀ (hs : 2 ≤ s.val) (hv : s.val + 2 < N), ∃ op, a.averageOperations hs hv = Sum.inr op

end Stage

def exactQuery (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (v : State E) : E :=
  if s < 2 then v 0 else representedAverage v + theta I N s • (v 0 - representedAverage v)
def exactAnswer (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (v : State E) (H : E →ₗ[ℝ] E) (target : E) : E :=
  H (exactQuery I N s v - target)
def exactRecovered (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (v : State E) (H : E →ₗ[ℝ] E) (target : E) : E :=
  if s < 2 then exactAnswer I N s v H target else
    v 7 + (theta I N s)⁻¹ • (exactAnswer I N s v H target - v 7)

def exactStep (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (v : State E) (H : E →ₗ[ℝ] E) (target : E) : State E :=
  let g := exactRecovered I N s v H target
  ![(1 + beta I s) • v 0 - beta I s • v 1 - alpha I s • g, v 0,
    (if s + 2 < N then if s < 2 then v 0 else
      representedAverage v + phi I N s • (v 0 - representedAverage v) else v 3), v 2,
    (if s + 2 < N then 0 else v 5), v 4,
    (if s + 2 < N then if s < 2 then exactAnswer I N s v H target else v 7 + phi I N s • (g - v 7) else v 7), v 6]

end
end InexactRealizations.Accuracy.Execution
