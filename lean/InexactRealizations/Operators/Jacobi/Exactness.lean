import InexactRealizations.Operators.Jacobi.Basic

/-! A nonzero scale of the terminal Chebyshev polynomial suffices.
Use: `InexactRealizations.Operators.JacobiData.terminal_exact` feeds
`InexactRealizations.Operators.SineJacobi.quadraticError_exact` (Terminal exactness for the independently defined
iterates).
-/
namespace InexactRealizations.Operators.JacobiData
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped Matrix

variable (J : JacobiData) (I : SpectralInterval)

/-- The precise assertion is `J.den I n ≠ 0`. -/
theorem den_ne {N n : ℕ} (h : J.Admissible I N) (hn : n ≤ N) :
    J.den I n ≠ 0 := ne_of_gt (h n hn)

/-- Exact identity `(J.realization I).scalarStep (n + 1) lam = !![(I.z lam - J.b (n + 1)) * J.den I
(n + 1) / J.den I (n + 2), -(J.aSq (n + 1) * J.den I n / J.den I (n + 2)); 1, 0]`.
-/
theorem scalarStep_succ (n : ℕ) (lam : ℝ) :
    (J.realization I).scalarStep (n + 1) lam =
      !![(I.z lam - J.b (n + 1)) * J.den I (n + 1) / J.den I (n + 2),
        -(J.aSq (n + 1) * J.den I n / J.den I (n + 2)); 1, 0] := by
  rw [realization, TwoTerm.scalarStep_succ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [method, I.z_eq]
  ring

/-- The precise assertion is `let M`. -/
theorem prefix_column {N : ℕ} (h : J.Admissible I N) (n : ℕ)
    (hn : n + 1 ≤ N) (lam : ℝ) :
    let M := orderedProduct (fun s => (J.realization I).scalarStep s lam) (n + 1)
    M 0 0 = (J.leading (n + 1)).eval (I.z lam) / J.den I (n + 1) ∧
    M 1 0 = (J.leading n).eval (I.z lam) / J.den I n := by
  induction n with
  | zero =>
    simp only [Nat.zero_add, realization, orderedProduct, TwoTerm.scalarStep_zero, Matrix.mul_one]
    constructor
    · simp only [method, den_zero, mul_one, leading_one, eval_sub, eval_X, eval_C,
        Matrix.of_apply, Matrix.cons_val_zero]
      rw [I.z_eq, den_one]
      field_simp [J.den_ne I h hn, show I.eta - J.b 0 ≠ 0 by simpa using J.den_ne I h hn]
      ring
    · simp [leading_zero]
  | succ n ih =>
    have hi := ih (by omega)
    dsimp only at hi ⊢
    rw [orderedProduct_succ, scalarStep_succ]
    constructor
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hi.1, hi.2]
      have hc : (J.leading (n + 2)).eval (I.z lam) =
          (I.z lam - J.b (n + 1)) * (J.leading (n + 1)).eval (I.z lam) -
            J.aSq (n + 1) * (J.leading n).eval (I.z lam) := by
        simp [leading, block]
      field_simp [J.den_ne I h (show n ≤ N by omega),
        J.den_ne I h (show n + 1 ≤ N by omega), J.den_ne I h hn]
      rw [hc]
      ring
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hi.1

/-- The scalar form, including the initial prefix.

Exact identity `(J.realization I).scalarTransfer n lam = (J.residual I n).eval lam`.
-/
theorem scalar_exact {N : ℕ} (h : J.Admissible I N) (n : ℕ) (hn : n ≤ N) (lam : ℝ) :
    (J.realization I).scalarTransfer n lam = (J.residual I n).eval lam := by
  rw [Realization.scalarTransfer, realization, TwoTerm.scalarContract, residual_eval]
  cases n with
  | zero => simp [orderedProduct]
  | succ n => exact (J.prefix_column I h n hn lam).1

/-- Exact identity `(J.realization I).residualPolynomial n = J.residual I n`. -/
theorem residualPolynomial_eq {N : ℕ} (h : J.Admissible I N) (n : ℕ) (hn : n ≤ N) :
    (J.realization I).residualPolynomial n = J.residual I n := by
  apply Polynomial.funext
  intro lam
  rw [Realization.residualPolynomial_eval, J.scalar_exact I h n hn]

/-- A nonzero scale of the terminal Chebyshev polynomial suffices.

Exact identity `J.residual I N = I.residual N`.
-/
theorem terminal_residual {N : ℕ} {c : ℝ} (hc : c ≠ 0)
    (hterminal : J.leading N = C c * T ℝ N) :
    J.residual I N = I.residual N := by
  apply Polynomial.funext
  intro lam
  rw [J.residual_eval, I.residual_eval]
  simp only [den, hterminal, eval_mul, eval_C, SpectralInterval.den]
  field_simp

end
end InexactRealizations.Operators.JacobiData
