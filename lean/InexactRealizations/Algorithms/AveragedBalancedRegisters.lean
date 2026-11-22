import InexactRealizations.Algorithms.Tape
import Mathlib.Data.Fin.VecNotation

/-! The current nine-vector averaged-Prefix program. Slots are
X, X', average0, average1, correction0, correction1, gradient0, gradient1, Y.
The componentwise compensated update has the exact linear semantics proved
below and uses only the two printed scalar temporaries. 
-/
namespace InexactRealizations.Algorithms
noncomputable section
open scoped BigOperators

structure AveragedParameters (N : ℕ) where
  alpha : Fin N → ℝ
  beta : Fin N → ℝ
  theta : Fin N → ℝ
  phi : Fin N → ℝ

namespace AveragedParameters
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

def averageSlot (s : ℕ) : Fin 9 := if Even s then 2 else 3
def correctionSlot (s : ℕ) : Fin 9 := if Even s then 4 else 5
def gradientSlot (s : ℕ) : Fin 9 := if Even s then 6 else 7

@[simp] theorem combination_single (i : Fin 9) (a : ℝ) (u : Fin 9 → E) :
    combination (Pi.single i a) u = a • u i := by
  classical
  simp [combination, Pi.single_apply, ite_smul]

@[simp] theorem combination_add (a b : Fin 9 → ℝ) (u : Fin 9 → E) :
    combination (a + b) u = combination a u + combination b u := by
  simp [combination, add_smul, Finset.sum_add_distrib]

@[simp] theorem combination_zero (u : Fin 9 → E) : combination (0 : Fin 9 → ℝ) u = 0 := by
  simp [combination]

def queryInstructions (data : AveragedParameters N) (s : Fin N) : List (LinearInstruction 9) :=
  if s.val < 2 then [.assign 8 (Pi.single 0 1)] else
    [.assign 8 (Pi.single (averageSlot s.val) 1 + Pi.single (correctionSlot s.val) 1),
     .assign 8 (Pi.single 0 (data.theta s) + Pi.single 8 (1 - data.theta s))]

def recoveryInstructions (data : AveragedParameters N) (s : Fin N) : List (LinearInstruction 9) :=
  if s.val < 2 then [] else
    [.assign 8 (Pi.single (gradientSlot s.val) (1 - (data.theta s)⁻¹) + Pi.single 8 (data.theta s)⁻¹)]

def averageInstructions (data : AveragedParameters N) (s : Fin N) : List (LinearInstruction 9) :=
  if s.val + 2 < N then
    if s.val < 2 then
      [.assign (averageSlot s.val) (Pi.single 0 1), .assign (correctionSlot s.val) 0,
       .assign (gradientSlot s.val) (Pi.single 8 1)]
    else
      [.assign (averageSlot s.val) (Pi.single 0 (data.phi s) + Pi.single (averageSlot s.val) (1 - data.phi s) +
        Pi.single (correctionSlot s.val) (1 - data.phi s)),
       .assign (correctionSlot s.val) 0,
       .assign (gradientSlot s.val) (Pi.single (gradientSlot s.val) (1 - data.phi s) + Pi.single 8 (data.phi s))]
  else []

def program (data : AveragedParameters N) : RegisterProgram 9 N where
  initial := ![1,1,1,1,0,0,0,0,0]
  before := data.queryInstructions
  queryRegister _ := 8
  answerRegister _ := 8
  after s := data.recoveryInstructions s ++ data.averageInstructions s ++
    [.assign 1 (Pi.single 0 (1 + data.beta s) + Pi.single 1 (-data.beta s) + Pi.single 8 (-data.alpha s)),
     .permute (Equiv.swap 0 1)]
  outputRegister := 0

def queryValue (data : AveragedParameters N) (s : Fin N) (u : Fin 9 → E) : E :=
  if s.val < 2 then u 0 else
    data.theta s • u 0 + (1 - data.theta s) • (u (averageSlot s.val) + u (correctionSlot s.val))

def recoveredValue (data : AveragedParameters N) (s : Fin N) (u : Fin 9 → E) (answer : E) : E :=
  if s.val < 2 then answer else
    (1 - (data.theta s)⁻¹) • u (gradientSlot s.val) + (data.theta s)⁻¹ • answer

def nextState (data : AveragedParameters N) (s : Fin N) (u : Fin 9 → E) (answer : E) : Fin 9 → E :=
  let recovered := data.recoveredValue s u answer
  fun i ↦
    if i = 0 then (1 + data.beta s) • u 0 - data.beta s • u 1 - data.alpha s • recovered else
    if i = 1 then u 0 else
    if i = 8 then recovered else
    if s.val + 2 < N ∧ i = averageSlot s.val then
      if s.val < 2 then u 0 else
        data.phi s • u 0 + (1 - data.phi s) • u (averageSlot s.val) +
          (1 - data.phi s) • u (correctionSlot s.val)
    else if s.val + 2 < N ∧ i = correctionSlot s.val then 0 else
    if s.val + 2 < N ∧ i = gradientSlot s.val then
      if s.val < 2 then answer else (1 - data.phi s) • u (gradientSlot s.val) + data.phi s • recovered
    else u i

set_option maxHeartbeats 2000000 in
theorem stage_vectors (data : AveragedParameters N) (s : Fin N)
    (oracle : Fin N → E → E) (u : Fin 9 → E) (calls : ℕ) :
    (data.program.stage oracle s ⟨u, calls⟩).vectors =
      data.nextState s u (oracle s (data.queryValue s u)) := by
  by_cases hs : s.val ≤ 1 <;> by_cases hu : s.val + 2 < N <;> by_cases hp : Even s.val
  all_goals
    ext i
    fin_cases i <;>
      simp [RegisterProgram.stage, program, queryInstructions, recoveryInstructions, averageInstructions,
        executeLinear, LinearInstruction.execute, averageSlot, correctionSlot, gradientSlot,
        queryValue, recoveredValue, nextState, hs, hu, hp, sub_eq_add_neg, Equiv.swap_apply_def, smul_add]
  all_goals module

end AveragedParameters
end
end InexactRealizations.Algorithms
