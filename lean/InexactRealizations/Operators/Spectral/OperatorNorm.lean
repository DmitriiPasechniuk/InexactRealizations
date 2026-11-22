import InexactRealizations.Operators.Spectral.Basis
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Spectral calculus bound for any polynomial, in the actual Euclidean operator norm.
Use: `InexactRealizations.Operators.opNorm_residual_le` feeds `InexactRealizations.Operators.Nonlinear.MethodFamily.transfer_le`
(The total finite drift bound used for nonlinear objectives).
Proof chain: `InexactRealizations.Operators.Nonlinear.lipschitzHessian_error_le` — chebyshev1,;
Lipschitz-Hessian error bound for both methods.
Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison. The needed form is proved here.
-/
namespace InexactRealizations.Operators
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
open Polynomial
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Exact identity `aeval (Matrix.diagonal v) p = Matrix.diagonal (fun i => p.eval (v i))`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
theorem aeval_diagonal (p : ℝ[X]) (v : d → ℝ) :
    aeval (Matrix.diagonal v) p = Matrix.diagonal (fun i => p.eval (v i)) := by
  have h := Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom (n := d) (α := ℝ) ℝ) v p
  simpa only [Matrix.diagonalAlgHom_apply, Polynomial.aeval_pi_apply,
    Polynomial.coe_aeval_eq_eval] using h

/-- Exact identity `(SpectralBasis.ofHermitian H hH).coordinates (aeval H p) = Matrix.diagonal (fun
i => p.eval (hH.eigenvalues i))`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
theorem aeval_coordinates (p : ℝ[X]) (H : Matrix d d ℝ) (hH : H.IsHermitian) :
    (SpectralBasis.ofHermitian H hH).coordinates (aeval H p) =
      Matrix.diagonal (fun i => p.eval (hH.eigenvalues i)) := by
  have h := Polynomial.aeval_algHom_apply
    (Unitary.conjStarAlgAut ℝ (Matrix d d ℝ) (star hH.eigenvectorUnitary)) H p
  rw [hH.conjStarAlgAut_star_eigenvectorUnitary] at h
  simpa only [SpectralBasis.coordinates, SpectralBasis.ofHermitian,
    Unitary.conjStarAlgAut_star_apply, Function.comp_def, RCLike.ofReal_real_eq_id,
    id_eq, aeval_diagonal, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using h.symm

end
end InexactRealizations.Operators
