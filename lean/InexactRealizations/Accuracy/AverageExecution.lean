import InexactRealizations.Roundoff.Journal

/-! Actual uncompensated averaged-Prefix execution with exact arithmetic
except for a specified error on the last addition of each average update.
The two logical average slots below are indexed by age, implementing the
two parity registers; entries after their last use are set to zero. 
-/
namespace InexactRealizations.Accuracy.AverageExecution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

structure State (E : Type*) where
  x : E
  previous : E
  recentAverage : E
  olderAverage : E
  recentGradient : E
  olderGradient : E

def oldAverage (s : ℕ) (v : State E) : E := if s < 2 then 0 else v.olderAverage
def oldGradient (s : ℕ) (v : State E) : E := if s < 2 then 0 else v.olderGradient
def query (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (v : State E) : E :=
  oldAverage s v + theta I N s • (v.x - oldAverage s v)
def answer (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (H : E →ₗ[ℝ] E)
    (target : E) (v : State E) : E := H (query I N s v - target)
def recovered (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (H : E →ₗ[ℝ] E)
    (target : E) (v : State E) : E :=
  oldGradient s v + (theta I N s)⁻¹ • (answer I N s H target v - oldGradient s v)
def idealAverage (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (v : State E) : E :=
  oldAverage s v + phi I N s • (v.x - oldAverage s v)

def step (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (H : E →ₗ[ℝ] E)
    (target : E) (error : ℕ → E → E) (v : State E) : State E where
  x := (1 + beta I s) • v.x - beta I s • v.previous - alpha I s • recovered I N s H target v
  previous := v.x
  recentAverage := if s + 2 < N then
    idealAverage I N s v + (if s < 2 then 0 else error s (idealAverage I N s v)) else 0
  olderAverage := v.recentAverage
  recentGradient := if s + 2 < N then
    oldGradient s v + phi I N s • (recovered I N s H target v - oldGradient s v) else 0
  olderGradient := v.recentGradient

def states (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E)
    (initial target : E) (error : ℕ → E → E) : ℕ → State E
  | 0 => ⟨initial, initial, 0, 0, 0, 0⟩
  | s + 1 => step I N s H target error (states I N H initial target error s)

variable (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E)
  (initial target : E) (error : ℕ → E → E)

def localErrors : InexactRealizations.Roundoff.LocalErrorStreams E where
  oracle _ := 0
  query _ := 0
  recovery _ := 0
  average s := if s < 2 then 0 else error s (idealAverage I N s (states I N H initial target error s))
  gradient _ := 0
  state _ := 0

theorem previous_state (s : ℕ) :
    (states I N H initial target error s).previous = (states I N H initial target error (s - 1)).x := by
  cases s <;> rfl

theorem earlier_average (s : ℕ) :
    oldAverage s (states I N H initial target error s) =
      InexactRealizations.Roundoff.earlierAverage (fun j ↦ (states I N H initial target error (j + 1)).recentAverage) s := by
  cases s with
  | zero => rfl
  | succ s => cases s with
    | zero => rfl
    | succ s => rfl

theorem earlier_gradient (s : ℕ) :
    oldGradient s (states I N H initial target error s) =
      InexactRealizations.Roundoff.earlierAverage (fun j ↦ (states I N H initial target error (j + 1)).recentGradient) s := by
  cases s with
  | zero => rfl
  | succ s => cases s with
    | zero => rfl
    | succ s => rfl

def execution : InexactRealizations.Roundoff.LocalExecution I N H initial target (localErrors I N H initial target error) where
  x s := (states I N H initial target error s).x
  y s := query I N s (states I N H initial target error s)
  g s := answer I N s H target (states I N H initial target error s)
  recovered s := recovered I N s H target (states I N H initial target error s)
  average s := (states I N H initial target error (s + 1)).recentAverage
  gradient s := (states I N H initial target error (s + 1)).recentGradient
  initial_eq := rfl
  query_eq s _ := by
    simp only [query, InexactRealizations.Roundoff.computedQuery, localErrors, add_zero, ← earlier_average]
  answer_eq s _ := by
    simp only [answer, InexactRealizations.Roundoff.computedAnswer, localErrors, add_zero]
  recovered_eq s _ := by
    simp only [recovered, InexactRealizations.Roundoff.recoveredGradient, localErrors, add_zero, ← earlier_gradient]
  average_eq s hs := by
    dsimp only [InexactRealizations.Roundoff.updatedAverage, localErrors]
    rw [← earlier_average]
    simp only [states, step, hs, ite_true, idealAverage]
  gradient_eq s hs := by
    dsimp only [InexactRealizations.Roundoff.updatedAverage, localErrors]
    rw [← earlier_gradient]
    simp only [states, step, hs, ite_true, add_zero]
  state_eq s _ := by
    simp only [states, step, localErrors, add_zero, previous_state]

end
end InexactRealizations.Accuracy.AverageExecution
