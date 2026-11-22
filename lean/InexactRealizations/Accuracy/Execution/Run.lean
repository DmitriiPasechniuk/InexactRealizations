import InexactRealizations.Accuracy.Execution.Stage
import InexactRealizations.Roundoff.Journal

/-! Full actual rounded execution and the exact local-error equations.
The run is specified only by the printed scalar/vector operations and
oracle error bound. The local residuals are definitions, not certificates. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Roundoff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def initialState (initial : E) : State E := ![initial, initial, initial, initial, 0, 0, 0, 0]

structure Run {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u : ℝ}
    (p : Prepared I N u) (H : E →ₗ[ℝ] E) (initial target : E) (uO : ℝ) where
  states : ℕ → State E
  initial_eq : states 0 = initialState initial
  stages : ∀ s : Fin N, Stage p s (states s.val) H target uO
  step_eq : ∀ s : Fin N, states (s.val + 1) = (stages s).output

namespace Run
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ} {p : Prepared I N u}
  {H : E →ₗ[ℝ] E} {initial target : E}

def Compensated (v : Run p H initial target uO) : Prop := ∀ s, (v.stages s).Compensated
def Uncompensated (v : Run p H initial target uO) : Prop := ∀ s, (v.stages s).Uncompensated

def x (v : Run p H initial target uO) (s : ℕ) : E := v.states s 0
def query (v : Run p H initial target uO) (s : ℕ) : E :=
  if hs : s < N then (v.stages ⟨s, hs⟩).query else 0
def answer (v : Run p H initial target uO) (s : ℕ) : E :=
  if hs : s < N then (v.stages ⟨s, hs⟩).answer else 0
def recovered (v : Run p H initial target uO) (s : ℕ) : E :=
  if hs : s < N then (v.stages ⟨s, hs⟩).recovered else 0
def noise (v : Run p H initial target uO) (s : ℕ) : E :=
  if hs : s < N then (v.stages ⟨s, hs⟩).noise else 0
def average (v : Run p H initial target uO) (s : ℕ) : E := v.states (s + 1) 2 + v.states (s + 1) 4
def gradient (v : Run p H initial target uO) (s : ℕ) : E := v.states (s + 1) 6

theorem previous_x (v : Run p H initial target uO) (s : ℕ) (hs : s < N) :
    v.states s 1 = v.x (s - 1) := by
  cases s with
  | zero => change v.states 0 1 = v.states 0 0; rw [v.initial_eq]; rfl
  | succ s => rw [v.step_eq ⟨s, by omega⟩]; rfl

theorem earlier_average (v : Run p H initial target uO) (s : ℕ) (hs : s < N) (hs2 : 2 ≤ s) :
    earlierAverage v.average s = representedAverage (v.states s) := by
  cases s with
  | zero => omega
  | succ s => cases s with
    | zero => omega
    | succ s =>
      change v.states (s + 1) 2 + v.states (s + 1) 4 = v.states (s + 2) 3 + v.states (s + 2) 5
      rw [v.step_eq ⟨s + 1, by omega⟩]
      rfl

theorem earlier_gradient (v : Run p H initial target uO) (s : ℕ) (hs : s < N) (hs2 : 2 ≤ s) :
    earlierAverage v.gradient s = v.states s 7 := by
  cases s with
  | zero => omega
  | succ s => cases s with
    | zero => omega
    | succ s =>
      change v.states (s + 1) 6 = v.states (s + 2) 7
      rw [v.step_eq ⟨s + 1, by omega⟩]
      rfl

def localErrors (v : Run p H initial target uO) : LocalErrorStreams E where
  oracle := v.noise
  query s := v.query s - (earlierAverage v.average s + theta I N s • (v.x s - earlierAverage v.average s))
  recovery s := v.recovered s - (earlierAverage v.gradient s + (theta I N s)⁻¹ •
    (v.answer s - earlierAverage v.gradient s))
  average s := v.average s - (earlierAverage v.average s + phi I N s • (v.x s - earlierAverage v.average s))
  gradient s := v.gradient s - (earlierAverage v.gradient s + phi I N s • (v.recovered s - earlierAverage v.gradient s))
  state
    | 0 => 0
    | s + 1 => v.x (s + 1) - ((1 + beta I s) • v.x s - beta I s • v.x (s - 1) - alpha I s • v.recovered s)

def execution (v : Run p H initial target uO) :
    LocalExecution I N H initial target v.localErrors where
  x := v.x
  y := v.query
  g := v.answer
  recovered := v.recovered
  average := v.average
  gradient := v.gradient
  initial_eq := by change v.states 0 0 = initial; rw [v.initial_eq]; rfl
  query_eq s _ := by simp only [computedQuery, localErrors]; abel
  answer_eq s hs := by
    simp only [answer, query, noise, hs, dite_true, Stage.answer, Stage.query, observedAnswer,
      computedAnswer, localErrors]
  recovered_eq s _ := by simp only [recoveredGradient, localErrors]; abel
  average_eq s _ := by simp only [updatedAverage, localErrors]; abel
  gradient_eq s _ := by simp only [updatedAverage, localErrors]; abel
  state_eq s _ := by simp only [localErrors]; abel

end Run
end
end InexactRealizations.Accuracy.Execution
