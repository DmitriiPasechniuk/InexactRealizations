import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Parseval identity for the spectral change of coordinates.
Use: `InexactRealizations.Operators.hsNorm_orthogonal_conjugation` feeds
`InexactRealizations.Operators.Realization.hsNorm_linearResponse_bound` (The Hilbert–Schmidt upper bound of
3 for every symmetric Hessian).
Proof chain: `InexactRealizations.Operators.Realization.hsNorm_linearResponse_bound` — chebyshev1, Proposition
1.3; Finite expansion, Hilbert–Schmidt bound and sharpness.
Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison. The needed form is proved here.
-/
namespace InexactRealizations.Operators
noncomputable section
open scoped BigOperators Matrix
variable {d : Type*} [Fintype d]

/-- Squared Hilbert–Schmidt norm in orthonormal coordinates.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
def hsSq (M : Matrix d d ℝ) : ℝ := ∑ i, ∑ j, (M i j) ^ 2
/-- Defines `hsNorm` of type `ℝ` by `Real.sqrt (hsSq M)`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
def hsNorm (M : Matrix d d ℝ) : ℝ := Real.sqrt (hsSq M)

/-- The stated quantitative bound `0 ≤ hsSq M`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
theorem hsSq_nonneg (M : Matrix d d ℝ) : 0 ≤ hsSq M :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
/-- The stated quantitative bound `0 ≤ hsNorm M`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
theorem hsNorm_nonneg (M : Matrix d d ℝ) : 0 ≤ hsNorm M := Real.sqrt_nonneg _
/-- Exact identity `hsNorm M ^ 2 = hsSq M`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
theorem hsNorm_sq (M : Matrix d d ℝ) : hsNorm M ^ 2 = hsSq M := Real.sq_sqrt (hsSq_nonneg M)

/-- Exact identity `hsSq M = Matrix.trace (Mᵀ * M)`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
theorem hsSq_eq_trace (M : Matrix d d ℝ) : hsSq M = Matrix.trace (Mᵀ * M) := by
  simp only [hsSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  exact Finset.sum_comm

variable [DecidableEq d]

/-- Exact identity `hsSq (Q * M) = hsSq M`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
theorem hsSq_orthogonal_left (Q M : Matrix d d ℝ) (hQ : Qᵀ * Q = 1) :
    hsSq (Q * M) = hsSq M := by
  rw [hsSq_eq_trace, hsSq_eq_trace, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Qᵀ Q M, hQ, Matrix.one_mul]

/-- Exact identity `hsSq (M * Q) = hsSq M`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
theorem hsSq_orthogonal_right (Q M : Matrix d d ℝ) (hQ : Q * Qᵀ = 1) :
    hsSq (M * Q) = hsSq M := by
  rw [hsSq_eq_trace, hsSq_eq_trace, Matrix.transpose_mul,
    ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Q Qᵀ (Mᵀ * M), hQ, Matrix.one_mul]

/-- Parseval identity for the spectral change of coordinates.

Exact identity `hsNorm (Qᵀ * M * Q) = hsNorm M`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
theorem hsNorm_orthogonal_conjugation (Q M : Matrix d d ℝ)
    (_hleft : Qᵀ * Q = 1) (hright : Q * Qᵀ = 1) :
    hsNorm (Qᵀ * M * Q) = hsNorm M := by
  unfold hsNorm
  rw [hsSq_orthogonal_right Q _ hright, hsSq_orthogonal_left Qᵀ M]
  simpa using hright

end
end InexactRealizations.Operators
