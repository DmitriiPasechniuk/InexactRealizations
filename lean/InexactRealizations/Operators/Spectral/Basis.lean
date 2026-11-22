import InexactRealizations.Operators.Spectral.HilbertSchmidt
import InexactRealizations.Operators.Chebyshev.Normalization
import Mathlib.Analysis.Matrix.Spectrum

/-! Existence uses the community library's finite-dimensional spectral theorem.
Use: `InexactRealizations.Operators.SpectralBasis.eigenvalues_mem_interval` feeds
`InexactRealizations.Operators.Realization.hsNorm_linearResponse_bound` (The Hilbert–Schmidt upper bound of
3 for every symmetric Hessian).
Proof chain: `InexactRealizations.Operators.Realization.hsNorm_linearResponse_bound` — chebyshev1, Proposition
1.3; Finite expansion, Hilbert–Schmidt bound and sharpness.
Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison. The needed form is proved here.
-/
namespace InexactRealizations.Operators
noncomputable section
open scoped Matrix
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- An orthogonal diagonalization, with repeated eigenvalues kept as separate coordinates.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
structure SpectralBasis (H : Matrix d d ℝ) where
  /-- Orthogonal change-of-basis matrix whose columns are eigenvectors. -/
  Q : Matrix d d ℝ
  /-- Eigenvalue attached to each basis vector. -/
  eigenvalues : d → ℝ
  /-- The columns of Q are orthonormal. -/
  transpose_mul : Qᵀ * Q = 1
  /-- The eigenbasis is complete, so Q is also a right inverse to its transpose. -/
  mul_transpose : Q * Qᵀ = 1
  /-- The chosen basis turns H into the stated diagonal matrix. -/
  diagonalize : Qᵀ * H * Q = Matrix.diagonal eigenvalues

namespace SpectralBasis

/-- Existence uses the community library's finite-dimensional spectral theorem.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
def ofHermitian (H : Matrix d d ℝ) (hH : H.IsHermitian) : SpectralBasis H where
  Q := hH.eigenvectorUnitary
  eigenvalues := hH.eigenvalues
  transpose_mul := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hH.eigenvectorUnitary
  mul_transpose := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_mul_star_self hH.eigenvectorUnitary
  diagonalize := by
    have h := hH.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using h

/-- Defines `coordinates` of type `Matrix d d ℝ` by `B.Qᵀ * E * B.Q`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
def coordinates {H : Matrix d d ℝ} (B : SpectralBasis H) (E : Matrix d d ℝ) : Matrix d d ℝ :=
  B.Qᵀ * E * B.Q

/-- Exact identity `B.coordinates (A * C) = B.coordinates A * B.coordinates C`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
theorem coordinates_mul {H : Matrix d d ℝ} (B : SpectralBasis H) (A C : Matrix d d ℝ) :
    B.coordinates (A * C) = B.coordinates A * B.coordinates C := by
  dsimp [coordinates]
  calc B.Qᵀ * (A * C) * B.Q = B.Qᵀ * A * (B.Q * B.Qᵀ) * C * B.Q := by
        rw [B.mul_transpose]; simp [Matrix.mul_assoc]
    _ = (B.Qᵀ * A * B.Q) * (B.Qᵀ * C * B.Q) := by simp [Matrix.mul_assoc]

/-- The precise assertion is `Function.Injective B.coordinates`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
theorem coordinates_injective {H : Matrix d d ℝ} (B : SpectralBasis H) :
    Function.Injective B.coordinates := by
  intro A C h
  have hr (M : Matrix d d ℝ) : B.Q * B.coordinates M * B.Qᵀ = M := by
    dsimp [coordinates]
    calc B.Q * (B.Qᵀ * M * B.Q) * B.Qᵀ = (B.Q * B.Qᵀ) * M * (B.Q * B.Qᵀ) := by
          simp [Matrix.mul_assoc]
      _ = M := by rw [B.mul_transpose]; simp
  have he := congrArg (fun M => B.Q * M * B.Qᵀ) h
  simpa only [hr] using he

/-- Membership in the specified domain/enclosure: `(ofHermitian H hH).eigenvalues i ∈ Set.Icc I.mu
I.L`.

Source: mathlib, Mathlib.LinearAlgebra.Matrix.Hermitian and matrix norm theory — finite real
spectral theorem and Euclidean/Frobenius norm comparison.
-/
theorem eigenvalues_mem_interval (I : SpectralInterval) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (h : spectrum ℝ H ⊆ Set.Icc I.mu I.L) (i : d) :
    (ofHermitian H hH).eigenvalues i ∈ Set.Icc I.mu I.L :=
  h (hH.eigenvalues_mem_spectrum_real i)

end SpectralBasis
end
end InexactRealizations.Operators
