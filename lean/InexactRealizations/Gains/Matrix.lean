import InexactRealizations.Gains.Variation
import InexactRealizations.Gains.Spectral
import InexactRealizations.Operators.Spectral.OperatorNorm

namespace InexactRealizations.History
noncomputable section
open Polynomial
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {d : Type*} [Fintype d] [DecidableEq d]

/-- A matrix acts on the actual Euclidean Hilbert space as a linear endomorphism. -/
def matrixEnd : Matrix d d ℝ →ₐ[ℝ] Module.End ℝ (EuclideanSpace ℝ d) where
  toRingHom := ContinuousLinearMap.toLinearMapRingHom.comp Matrix.toEuclideanCLM.toRingHom
  commutes' r := by
    change ((Matrix.toEuclideanCLM (n := d) (𝕜 := ℝ)) (algebraMap ℝ (Matrix d d ℝ) r)).toLinearMap = _
    rw [AlgHomClass.commutes]
    rfl

/-- Physical first variation written as the finite matrix insertion sum. -/
def matrixResponse (h : InexactRealizations.History N) (H : Matrix d d ℝ)
    (D : Fin N → Matrix d d ℝ) : Matrix d d ℝ :=
  ∑ s, aeval H (h.response s) * D s * aeval H (h.query s)

/-- Extend a finite perturbation stream by zero after the last actual call. -/
def matrixDriftExtension (D : Fin N → Matrix d d ℝ) (s : ℕ) : Matrix d d ℝ :=
  if hs : s < N then D ⟨s, hs⟩ else 0

/-- In an eigenbasis each physical insertion acts entrywise by the separated kernel. -/
theorem diagonal_matrixResponse_entry (h : InexactRealizations.History N) (eig : d → ℝ)
    (D : Fin N → Matrix d d ℝ) (i j : d) :
    h.matrixResponse (Matrix.diagonal eig) D i j =
      ∑ s, Lower.physicalKernel h s (eig i) (eig j) * D s i j := by
  simp only [matrixResponse, Matrix.sum_apply, InexactRealizations.Operators.aeval_diagonal,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Lower.physicalKernel]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Spectral coordinates of physical first variation agree with its diagonal formula. -/
theorem matrixResponse_coordinates (h : InexactRealizations.History N) (H : Matrix d d ℝ)
    (hH : H.IsHermitian) (D : Fin N → Matrix d d ℝ) :
    (InexactRealizations.Operators.SpectralBasis.ofHermitian H hH).coordinates (h.matrixResponse H D) =
      h.matrixResponse (Matrix.diagonal (InexactRealizations.Operators.SpectralBasis.ofHermitian H hH).eigenvalues)
        (fun s => (InexactRealizations.Operators.SpectralBasis.ofHermitian H hH).coordinates (D s)) := by
  let B := InexactRealizations.Operators.SpectralBasis.ofHermitian H hH
  have hsum (A : Fin N → Matrix d d ℝ) : B.coordinates (∑ s, A s) = ∑ s, B.coordinates (A s) := by
    simp only [InexactRealizations.Operators.SpectralBasis.coordinates, Matrix.mul_sum, Matrix.sum_mul]
  rw [matrixResponse, hsum]
  unfold matrixResponse
  apply Finset.sum_congr rfl
  intro s _
  rw [B.coordinates_mul, B.coordinates_mul, InexactRealizations.Operators.aeval_coordinates,
    InexactRealizations.Operators.aeval_coordinates, InexactRealizations.Operators.aeval_diagonal, InexactRealizations.Operators.aeval_diagonal]
  rfl

/-- The physical matrix derivative is the insertion operator of the existing
realization theory. This equality holds for every symmetric admissible Hessian. 
-/
theorem matrixResponse_eq_realization (h : InexactRealizations.History N) (H : Matrix d d ℝ)
    (hH : H.IsHermitian) (D : Fin N → Matrix d d ℝ) :
    h.matrixResponse H D = h.realization.linearResponse N H (matrixDriftExtension D) := by
  let B := InexactRealizations.Operators.SpectralBasis.ofHermitian H hH
  apply B.coordinates_injective
  rw [h.matrixResponse_coordinates]
  have hr := h.realization.linearResponse_coordinates B.Q H B.transpose_mul B.mul_transpose
    N (matrixDriftExtension D)
  rw [B.diagonalize] at hr
  change _ = B.Qᵀ * _ * B.Q
  rw [← hr]
  ext i j
  rw [h.diagonal_matrixResponse_entry, InexactRealizations.Operators.Realization.diagonal_linearResponse_entry,
    Finset.sum_range]
  apply Finset.sum_congr rfl
  intro s _
  rw [h.realization_kernel]
  simp only [matrixDriftExtension, s.isLt, dite_true, Lower.physicalKernel,
    InexactRealizations.Operators.SpectralBasis.coordinates]
  rfl

/-- The actual derivative obeys the sharp dimension-uniform Hilbert--Schmidt bound. -/
theorem hs_matrixResponse_bound (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hs : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (D : Fin N → Matrix d d ℝ) :
    InexactRealizations.Operators.hsNorm (h.matrixResponse H D) ≤
      h.spectralGain I * Real.sqrt (∑ s, InexactRealizations.Operators.hsNorm (D s) ^ 2) := by
  rw [h.matrixResponse_eq_realization H hH D]
  simpa only [Finset.sum_range, matrixDriftExtension, Fin.isLt, dite_true, spectralGain] using
    h.realization.hsNorm_linearResponse_bound I N H hH hs (matrixDriftExtension D)

end
end InexactRealizations.History
