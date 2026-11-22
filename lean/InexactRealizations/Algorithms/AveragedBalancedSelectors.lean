import InexactRealizations.Algorithms.AveragedBalancedRegisters

/-! Selector identities for the actual parity registers. -/
namespace InexactRealizations.Algorithms.AveragedParameters
noncomputable section
variable {N : ℕ}

theorem query_instructions_value (d : AveragedParameters N) (s : Fin N) (u : Fin 9 → ℝ) :
    executeLinear (d.queryInstructions s) u 8 = d.queryValue s u := by
  by_cases hs : s.val ≤ 1 <;> by_cases hp : Even s.val
  all_goals simp [queryInstructions, queryValue, averageSlot, correctionSlot, hs, hp,
    executeLinear, LinearInstruction.execute]

@[simp] theorem averageSlot_add_two (n : ℕ) : averageSlot (n + 2) = averageSlot n := by
  simp [averageSlot, Nat.even_add]

@[simp] theorem gradientSlot_add_two (n : ℕ) : gradientSlot (n + 2) = gradientSlot n := by
  simp [gradientSlot, Nat.even_add]

theorem correction_value (n : ℕ) (u : Fin 9 → ℝ) (h4 : u 4 = 0) (h5 : u 5 = 0) :
    u (correctionSlot n) = 0 := by
  by_cases hp : Even n <;> simp [correctionSlot, hp, h4, h5]

@[simp] theorem nextState_x (d : AveragedParameters N) (s : Fin N) (u : Fin 9 → ℝ) (answer : ℝ) :
    d.nextState s u answer 0 =
      (1 + d.beta s) * u 0 - d.beta s * u 1 - d.alpha s * d.recoveredValue s u answer := by
  simp [nextState]

@[simp] theorem nextState_previous (d : AveragedParameters N) (s : Fin N) (u : Fin 9 → ℝ) (answer : ℝ) :
    d.nextState s u answer 1 = u 0 := by simp [nextState]

theorem nextState_corrections (d : AveragedParameters N) (s : Fin N) (u : Fin 9 → ℝ) (answer : ℝ)
    (h4 : u 4 = 0) (h5 : u 5 = 0) : d.nextState s u answer 4 = 0 ∧ d.nextState s u answer 5 = 0 := by
  by_cases hp : Even s.val <;> simp [nextState, averageSlot, correctionSlot, gradientSlot, hp, h4, h5]

theorem nextState_other_average (d : AveragedParameters N) (s : Fin N) (u : Fin 9 → ℝ) (answer : ℝ) :
    d.nextState s u answer (averageSlot (s.val + 1)) = u (averageSlot (s.val + 1)) := by
  by_cases hp : Even s.val <;> simp [nextState, averageSlot, correctionSlot, gradientSlot, Nat.even_add, hp]

theorem nextState_other_gradient (d : AveragedParameters N) (s : Fin N) (u : Fin 9 → ℝ) (answer : ℝ) :
    d.nextState s u answer (gradientSlot (s.val + 1)) = u (gradientSlot (s.val + 1)) := by
  by_cases hp : Even s.val <;> simp [nextState, averageSlot, correctionSlot, gradientSlot, Nat.even_add, hp]

theorem nextState_current_average (d : AveragedParameters N) (s : Fin N) (u : Fin 9 → ℝ) (answer : ℝ)
    (hs : s.val + 2 < N) :
    d.nextState s u answer (averageSlot s.val) =
      if s.val < 2 then u 0 else
        d.phi s * u 0 + (1 - d.phi s) * u (averageSlot s.val) +
          (1 - d.phi s) * u (correctionSlot s.val) := by
  by_cases hp : Even s.val <;> simp [nextState, averageSlot, correctionSlot, gradientSlot, hp, hs]

theorem nextState_current_gradient (d : AveragedParameters N) (s : Fin N) (u : Fin 9 → ℝ) (answer : ℝ)
    (hs : s.val + 2 < N) :
    d.nextState s u answer (gradientSlot s.val) =
      if s.val < 2 then answer else
        (1 - d.phi s) * u (gradientSlot s.val) + d.phi s * d.recoveredValue s u answer := by
  by_cases hp : Even s.val <;> simp [nextState, averageSlot, correctionSlot, gradientSlot, hp, hs]

end
end InexactRealizations.Algorithms.AveragedParameters
