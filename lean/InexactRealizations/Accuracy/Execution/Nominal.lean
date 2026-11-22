import InexactRealizations.Accuracy.Execution.FinitePerturbation
import InexactRealizations.Accuracy.Estimates.QuerySize

/-! The nominal state trajectory satisfies exactly local
equations with zero oracle and local errors, including both startup calls. 
-/
namespace InexactRealizations.Accuracy.Execution.Nominal
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Roundoff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E) (initial target : E)

def x (s : ℕ) : E := nominalStates I N H initial target s 0
def query (s : ℕ) : E := exactQuery I N s (nominalStates I N H initial target s)
def answer (s : ℕ) : E := exactAnswer I N s (nominalStates I N H initial target s) H target
def recovered (s : ℕ) : E := exactRecovered I N s (nominalStates I N H initial target s) H target
def average (s : ℕ) : E := nominalStates I N H initial target (s + 1) 2 + nominalStates I N H initial target (s + 1) 4
def gradient (s : ℕ) : E := nominalStates I N H initial target (s + 1) 6

theorem previous (s : ℕ) : nominalStates I N H initial target s 1 = x I N H initial target (s - 1) := by
  cases s <;> rfl

theorem earlier_average (s : ℕ) (hs : 2 ≤ s) :
    earlierAverage (average I N H initial target) s = representedAverage (nominalStates I N H initial target s) := by
  cases s with
  | zero => omega
  | succ s => cases s with
    | zero => omega
    | succ s => rfl

theorem earlier_gradient (s : ℕ) (hs : 2 ≤ s) :
    earlierAverage (gradient I N H initial target) s = nominalStates I N H initial target s 7 := by
  cases s with
  | zero => omega
  | succ s => cases s with
    | zero => omega
    | succ s => rfl

def execution : LocalExecution I N H initial target (zeroErrors E) where
  x := x I N H initial target
  y := query I N H initial target
  g := answer I N H initial target
  recovered := recovered I N H initial target
  average := average I N H initial target
  gradient := gradient I N H initial target
  initial_eq := rfl
  query_eq s _ := by
    by_cases hs : s < 2
    · simp [query, exactQuery, x, computedQuery, theta, earlierAverage, hs, zeroErrors]
    · rw [earlier_average I N H initial target s (by omega)]
      simp only [query, exactQuery, hs, ite_false, x, computedQuery, zeroErrors, add_zero]
  answer_eq s _ := by simp [answer, query, exactAnswer, computedAnswer, zeroErrors]
  recovered_eq s _ := by
    by_cases hs : s < 2
    · simp [recovered, exactRecovered, answer, recoveredGradient, theta, earlierAverage, hs, zeroErrors]
    · rw [earlier_gradient I N H initial target s (by omega)]
      simp only [recovered, exactRecovered, hs, ite_false, answer, recoveredGradient, zeroErrors, add_zero]
  average_eq s hvalid := by
    by_cases hs : s < 2
    · simp [average, nominalStates, exactStep, updatedAverage, earlierAverage, phi, x, hvalid, hs, zeroErrors]
    · rw [earlier_average I N H initial target s (by omega)]
      simp [average, nominalStates, exactStep, hvalid, hs, updatedAverage, zeroErrors, x]
  gradient_eq s hvalid := by
    by_cases hs : s < 2
    · simp [gradient, nominalStates, exactStep, recovered, exactRecovered, updatedAverage,
        earlierAverage, phi, hvalid, hs, zeroErrors]
    · rw [earlier_gradient I N H initial target s (by omega)]
      simp [gradient, nominalStates, exactStep, hvalid, hs, updatedAverage, zeroErrors, recovered]
  state_eq s _ := by
    change (1 + beta I s) • x I N H initial target s -
      beta I s • nominalStates I N H initial target s 1 - alpha I s • recovered I N H initial target s = _
    rw [previous]
    simp only [zeroErrors, add_zero]

end
end InexactRealizations.Accuracy.Execution.Nominal
