import InexactRealizations.Budgets.FiniteSpectrum

/-! Two arbitrary finite spectral probability distributions are realized by
unit vectors of one actual admissible Hessian. 
-/
namespace InexactRealizations.Budgets.FiniteSpectrum
noncomputable section
open Polynomial
open scoped BigOperators
variable {I : InexactRealizations.Operators.SpectralInterval}

theorem polynomialNorm_one (alpha : FiniteSpectrum I) : alpha.polynomialNorm 1 = 1 := by
  simp only [polynomialNorm, moment, eval_one, one_pow, mul_one, alpha.total, Real.sqrt_one]

def jointPoints (alpha beta : FiniteSpectrum I) : Fin (alpha.size + beta.size) → ℝ :=
  Fin.append alpha.point beta.point

def leftVector (alpha beta : FiniteSpectrum I) : EuclideanSpace ℝ (Fin (alpha.size + beta.size)) :=
  WithLp.toLp 2 (Fin.append (fun i ↦ Real.sqrt (alpha.weight i)) (fun _ ↦ 0))

def rightVector (alpha beta : FiniteSpectrum I) : EuclideanSpace ℝ (Fin (alpha.size + beta.size)) :=
  WithLp.toLp 2 (Fin.append (fun _ ↦ 0) (fun i ↦ Real.sqrt (beta.weight i)))

theorem joint_admissible (alpha beta : FiniteSpectrum I) :
    InexactRealizations.Analysis.Admissible I (diagonal (jointPoints alpha beta)) := by
  apply diagonal_admissible
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa only [jointPoints, Fin.append_left] using alpha.point_mem j
  · intro j
    simpa only [jointPoints, Fin.append_right] using beta.point_mem j

theorem joint_left (alpha beta : FiniteSpectrum I) (p : ℝ[X]) :
    ‖(aeval (diagonal (jointPoints alpha beta)) p) (leftVector alpha beta)‖ =
      alpha.polynomialNorm p := by
  apply (sq_eq_sq₀ (norm_nonneg _) (alpha.polynomialNorm_nonneg p)).mp
  rw [polynomialNorm, Real.sq_sqrt (alpha.moment_nonneg p), EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_add]
  simp only [diagonal_polynomial, jointPoints, leftVector,
    Fin.append_left, Fin.append_right, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (alpha.nonneg _), mul_zero, zero_pow (by norm_num : 2 ≠ 0),
    Finset.sum_const_zero, add_zero, moment]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem joint_right (alpha beta : FiniteSpectrum I) (p : ℝ[X]) :
    ‖(aeval (diagonal (jointPoints alpha beta)) p) (rightVector alpha beta)‖ =
      beta.polynomialNorm p := by
  apply (sq_eq_sq₀ (norm_nonneg _) (beta.polynomialNorm_nonneg p)).mp
  rw [polynomialNorm, Real.sq_sqrt (beta.moment_nonneg p), EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_add]
  simp only [diagonal_polynomial, jointPoints, rightVector,
    Fin.append_left, Fin.append_right, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (beta.nonneg _), mul_zero, zero_pow (by norm_num : 2 ≠ 0),
    Finset.sum_const_zero, zero_add, moment]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem leftVector_norm (alpha beta : FiniteSpectrum I) : ‖leftVector alpha beta‖ = 1 := by
  have hh := joint_left alpha beta 1
  simpa only [map_one, Module.End.one_apply, polynomialNorm_one] using hh

theorem rightVector_norm (alpha beta : FiniteSpectrum I) : ‖rightVector alpha beta‖ = 1 := by
  have hh := joint_right alpha beta 1
  simpa only [map_one, Module.End.one_apply, polynomialNorm_one] using hh

end
end InexactRealizations.Budgets.FiniteSpectrum
