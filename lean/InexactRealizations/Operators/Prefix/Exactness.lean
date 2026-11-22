import InexactRealizations.Operators.Prefix.Basic

/-! The independently defined algorithm and the generic realization have the same output.
Result: `InexactRealizations.Operators.Prefix.quadraticError_eq_transfer` supplies the stated article conclusion.
-/
namespace InexactRealizations.Operators.Prefix

noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped Matrix BigOperators

variable (I : SpectralInterval)

/-- The precise assertion is `let M`. -/
theorem prefix_column (n : ℕ) (lam : ℝ) :
    let M := orderedProduct (fun s => (realization I).scalarStep s lam) (n + 1)
    M 0 0 = (T ℝ (n + 1)).eval (I.z lam) / I.den (n + 1) ∧
    M 1 0 = (T ℝ n).eval (I.z lam) / I.den n := by
  induction n with
  | zero => simp [orderedProduct, scalarStep_zero]
  | succ n ih =>
    dsimp only at ih ⊢
    rw [orderedProduct_succ, scalarStep_succ]
    constructor
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ih.1, ih.2]
      have hc : (T ℝ ((n : ℤ) + 2)).eval (I.z lam) =
          2 * I.z lam * (T ℝ ((n : ℤ) + 1)).eval (I.z lam) -
            (T ℝ n).eval (I.z lam) := by simp [T_add_two]
      push_cast
      field_simp [I.den_ne n, I.den_ne (n + 1), I.den_ne (n + 2)]
      convert! hc.symm using 1
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using ih.1

/-- 1 in scalar form, for every prefix, including time zero.

Exact identity `(realization I).scalarTransfer n lam = (I.residual n).eval lam`.
-/
theorem scalar_exact (n : ℕ) (lam : ℝ) :
    (realization I).scalarTransfer n lam = (I.residual n).eval lam := by
  rw [Realization.scalarTransfer, scalarContract, I.residual_eval]
  cases n with
  | zero => simp [orderedProduct]
  | succ n => exact (prefix_column I n lam).1

/-- Exactness is a polynomial identity, not only agreement on the spectrum.

Exact identity `(realization I).residualPolynomial n = I.residual n`.
-/
theorem residualPolynomial_eq (n : ℕ) :
    (realization I).residualPolynomial n = I.residual n := by
  apply Polynomial.funext
  intro lam
  rw [Realization.residualPolynomial_eval, scalar_exact]

/-- Exact identity `I.residual 0 = 1`. -/
@[simp] theorem residual_zero : I.residual 0 = 1 := by simp [SpectralInterval.residual]

/-- Exact identity `I.residual 1 = 1 - Polynomial.C (2 / (I.L + I.mu)) * Polynomial.X`. -/
theorem residual_one : I.residual 1 =
    1 - Polynomial.C (2 / (I.L + I.mu)) * Polynomial.X := by
  apply Polynomial.funext
  intro lam
  rw [I.residual_eval]
  simp only [Nat.cast_one, T_one, Polynomial.eval_X, I.den_one, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C]
  dsimp [SpectralInterval.z, SpectralInterval.eta]
  field_simp [ne_of_gt I.delta_pos, ne_of_gt I.sum_pos]

/-- Exact identity `I.residual (n + 2) = Polynomial.C (1 + beta I (n + 1)) * (1 - Polynomial.C (2 /
(I.L + I.mu)) * Polynomial.X) * I.residual (n + 1) - Polynomial.C (beta I (n + 1)) * I.residual
n`.
-/
theorem residual_recurrence (n : ℕ) :
    I.residual (n + 2) =
      Polynomial.C (1 + beta I (n + 1)) *
        (1 - Polynomial.C (2 / (I.L + I.mu)) * Polynomial.X) * I.residual (n + 1) -
      Polynomial.C (beta I (n + 1)) * I.residual n := by
  apply Polynomial.funext
  intro lam
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_one, Polynomial.eval_X]
  rw [← scalar_exact, Realization.scalarTransfer, scalarContract,
    orderedProduct_succ, algorithmStep_succ]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [(prefix_column I n lam).1, (prefix_column I n lam).2,
    I.residual_eval, I.residual_eval]
  push_cast
  ring

end
end InexactRealizations.Operators.Prefix
