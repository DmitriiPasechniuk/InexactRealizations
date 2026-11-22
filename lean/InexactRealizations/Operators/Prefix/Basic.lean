import InexactRealizations.Operators.Chebyshev.Normalization
import Mathlib.Algebra.Polynomial.AlgebraMap
import InexactRealizations.Operators.Realization.Expansion

/-! The normalized matrix is precisely the advertised two-term gradient update.
Use: `InexactRealizations.Operators.Prefix.algorithmStep_succ` feeds `InexactRealizations.Operators.Prefix.residual_recurrence`
(residual recurrence).
Proof chain: `InexactRealizations.Operators.Prefix.quadraticError_exact` — chebyshev1,; Prefix-exact
recurrence and quadratic transfer.
-/
namespace InexactRealizations.Operators.Prefix

noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped Matrix BigOperators

variable (I : SpectralInterval)

/-- `beta (t+1)` is the coefficient at time `t+1`. -/
def beta (t : ℕ) : ℝ := I.den (t - 1) / I.den (t + 1)
/-- Defines `gamma` by pattern matching with result type `ℕ → ℝ`. The displayed branches determine
the recursive cases and their returned values.
-/
def gamma : ℕ → ℝ
  | 0 => 2 / (I.L + I.mu)
  | t + 1 => 4 * I.den (t + 1) / (I.delta * I.den (t + 2))

/-- Memory stores the current and previous errors; the initial previous slot is unused. -/
def realization : Realization (Fin 2) where
  b := ![1, 0]
  readout := ![1, 0]
  P := fun t => match t with
    | 0 => !![1, 0; 1, 0]
    | t + 1 => !![2 * I.eta * I.den (t + 1) / I.den (t + 2),
        -(I.den t / I.den (t + 2)); 1, 0]
  g := fun t => ![gamma I t, 0]
  q := fun _ => ![1, 0]

/-- Exact identity `2 * I.eta * I.den (t + 1) / I.den (t + 2) = 1 + beta I (t + 1)`. -/
theorem beta_coefficient (t : ℕ) :
    2 * I.eta * I.den (t + 1) / I.den (t + 2) = 1 + beta I (t + 1) := by
  simp only [beta, Nat.add_sub_cancel]
  have h := I.den_add_two t
  field_simp [I.den_ne (t + 2)]
  linarith

/-- Exact identity `gamma I (t + 1) = (1 + beta I (t + 1)) * (2 / (I.L + I.mu))`. -/
theorem gamma_succ (t : ℕ) :
    gamma I (t + 1) = (1 + beta I (t + 1)) * (2 / (I.L + I.mu)) := by
  rw [← beta_coefficient]
  dsimp [gamma, SpectralInterval.eta]
  field_simp [I.den_ne (t + 2), ne_of_gt I.delta_pos, ne_of_gt I.sum_pos]
  ring

/-- Exact identity `(realization I).scalarContract M = M 0 0`. -/
@[simp] theorem scalarContract (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (realization I).scalarContract M = M 0 0 := by simp [Realization.scalarContract, realization, Fin.sum_univ_two]

/-- Exact identity `(realization I).queryFactor s = !![gamma I s, 0; 0, 0]`. -/
@[simp] theorem queryFactor (s : ℕ) :
    (realization I).queryFactor s = !![gamma I s, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Realization.queryFactor, realization, Matrix.vecMulVec]

/-- Exact identity `(realization I).scalarStep 0 lam = !![I.z lam / I.eta, 0; 1, 0]`. -/
theorem scalarStep_zero (lam : ℝ) :
    (realization I).scalarStep 0 lam = !![I.z lam / I.eta, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Realization.scalarStep, realization, gamma, Realization.queryFactor,
      Matrix.vecMulVec]
  dsimp [SpectralInterval.z, SpectralInterval.eta]
  field_simp [ne_of_gt I.delta_pos, ne_of_gt I.sum_pos]

/-- Exact identity `(realization I).scalarStep (t + 1) lam = !![2 * I.z lam * I.den (t + 1) / I.den
(t + 2), -(I.den t / I.den (t + 2)); 1, 0]`.
-/
theorem scalarStep_succ (t : ℕ) (lam : ℝ) :
    (realization I).scalarStep (t + 1) lam =
      !![2 * I.z lam * I.den (t + 1) / I.den (t + 2),
          -(I.den t / I.den (t + 2)); 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Realization.scalarStep, realization, gamma, Realization.queryFactor,
      Matrix.vecMulVec]
  rw [I.z_eq]
  ring

/-- The normalized matrix is precisely the advertised two-term gradient update.

Exact identity `(realization I).scalarStep (t + 1) lam = !![(1 + beta I (t + 1)) * (1 - (2 /
(I.L + I.mu)) * lam), -beta I (t + 1); 1, 0]`.
-/
theorem algorithmStep_succ (t : ℕ) (lam : ℝ) :
    (realization I).scalarStep (t + 1) lam =
      !![(1 + beta I (t + 1)) * (1 - (2 / (I.L + I.mu)) * lam),
        -beta I (t + 1); 1, 0] := by
  rw [scalarStep_succ]
  have hc : 2 * I.z lam * I.den (t + 1) / I.den (t + 2) =
      2 * I.eta * I.den (t + 1) / I.den (t + 2) - gamma I (t + 1) * lam := by
    rw [I.z_eq]
    dsimp [gamma]
    ring
  rw [hc, beta_coefficient, gamma_succ]
  simp only [beta, Nat.add_sub_cancel]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  ring

end
end InexactRealizations.Operators.Prefix
