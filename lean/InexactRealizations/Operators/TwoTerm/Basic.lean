import InexactRealizations.Operators.Prefix.Exactness
import InexactRealizations.Operators.Chebyshev.Polynomial

/-! A causal two-term one-gradient recurrence; time zero uses only `gamma 0`.
Use: `InexactRealizations.Operators.TwoTerm.transfer_recurrence` feeds `InexactRealizations.Operators.TwoTerm.coefficients_unique`
(, for every used noninitial time).
Proof chain: `InexactRealizations.Operators.TwoTerm.coefficients_unique_explicit` — chebyshev1,;
Local uniqueness of the causal two-term realization.
-/
namespace InexactRealizations.Operators
noncomputable section
open scoped Matrix BigOperators

/-- A causal two-term one-gradient recurrence; time zero uses only `gamma 0`. -/
structure TwoTerm where
  /-- Coefficient multiplying the current error in the two-term recurrence. -/
  a : ℕ → ℝ
  /-- Coefficient multiplying the preceding error, representing momentum/memory. -/
  b : ℕ → ℝ
  /-- Stepsize coefficient multiplying the Hessian action; positivity is imposed by the relevant admissibility hypotheses. -/
  gamma : ℕ → ℝ

namespace TwoTerm

/-- Constructs `realization` of type `Realization (Fin 2)` by the displayed record fields. Data
fields specify the construction; proof fields discharge its required properties.
-/
def realization (S : TwoTerm) : Realization (Fin 2) where
  b := ![1, 0]
  readout := ![1, 0]
  P := fun t => if t = 0 then !![1, 0; 1, 0] else !![S.a t, S.b t; 1, 0]
  g := fun t => ![S.gamma t, 0]
  q := fun _ => ![1, 0]

/-- Exact identity `S.realization.scalarContract M = M 0 0`. -/
@[simp] theorem scalarContract (S : TwoTerm) (M : Matrix (Fin 2) (Fin 2) ℝ) :
    S.realization.scalarContract M = M 0 0 := by simp [Realization.scalarContract, realization, Fin.sum_univ_two]

/-- Exact identity `S.realization.queryFactor t = !![S.gamma t, 0; 0, 0]`. -/
@[simp] theorem queryFactor (S : TwoTerm) (t : ℕ) :
    S.realization.queryFactor t = !![S.gamma t, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Realization.queryFactor, realization, Matrix.vecMulVec]

/-- Exact identity `S.realization.scalarStep 0 lam = !![1 - S.gamma 0 * lam, 0; 1, 0]`. -/
theorem scalarStep_zero (S : TwoTerm) (lam : ℝ) :
    S.realization.scalarStep 0 lam = !![1 - S.gamma 0 * lam, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Realization.scalarStep, Realization.queryFactor, realization, Matrix.vecMulVec, mul_comm]

/-- Exact identity `S.realization.scalarStep (t + 1) lam = !![S.a (t + 1) - S.gamma (t + 1) * lam,
S.b (t + 1); 1, 0]`.
-/
theorem scalarStep_succ (S : TwoTerm) (t : ℕ) (lam : ℝ) :
    S.realization.scalarStep (t + 1) lam =
      !![S.a (t + 1) - S.gamma (t + 1) * lam, S.b (t + 1); 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Realization.scalarStep, Realization.queryFactor, realization, Matrix.vecMulVec, mul_comm]

end TwoTerm
end
end InexactRealizations.Operators
