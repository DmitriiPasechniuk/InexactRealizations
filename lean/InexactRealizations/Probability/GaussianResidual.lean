import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.CovarianceBilin

/-! Gaussian residual orthogonality used for the adaptive part.
The estimator is a function of the observation only; the hidden Gaussian
sample is not supplied to it. 
-/
namespace InexactRealizations.Probability.Gaussian
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem linear_memLp (u : E) :
    MemLp (fun x : E ↦ inner ℝ u x) 2 (stdGaussian E) :=
  (IsGaussian.hasGaussianLaw_id.map_fun (innerSL ℝ u)).memLp_two

theorem linear_mean (u : E) : (∫ x, inner ℝ u x ∂stdGaussian E) = 0 :=
  integral_strongDual_stdGaussian (innerSL ℝ u)

theorem linear_second_moment (u : E) :
    (∫ x, (inner ℝ u x) ^ 2 ∂stdGaussian E) = ‖u‖ ^ 2 := by
  have h := covarianceBilin_apply (μ := stdGaussian E) IsGaussian.memLp_two_id u u
  rw [covarianceBilin_stdGaussian] at h
  change inner ℝ u u = _ at h
  simpa [← sq] using h.symm

theorem residual_indep_observation (L : E →L[ℝ] F) (u : E) (hu : L u = 0) :
    IndepFun (fun x : E ↦ inner ℝ u x) L (stdGaussian E) := by
  have hj := (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun ((innerSL ℝ u).prod L)
  apply hj.indepFun_of_covariance_inner
  intro a b
  change cov[fun x : E ↦ inner ℝ a (inner ℝ u x),
    fun x : E ↦ inner ℝ b (L x); stdGaussian E] = 0
  have hc : cov[fun x : E ↦ inner ℝ u x, fun x : E ↦ inner ℝ b (L x); stdGaussian E] = 0 := by
    simp_rw [← L.adjoint_inner_left]
    rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian, innerSL_apply_apply, L.adjoint_inner_right, hu]
    simp
  simp only [Real.inner_apply, covariance_const_mul_left, hc, mul_zero]

end
end InexactRealizations.Probability.Gaussian
