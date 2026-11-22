import InexactRealizations.Probability.GaussianResidual
import InexactRealizations.Probability.Martingale
import Mathlib.MeasureTheory.Function.L2Space

/-! The Gaussian mean-square lower bound, with no posterior-risk hypothesis.
The estimator sees only `L x`. Infinite mean-square errors are included by
using the nonnegative extended integral in the unconditional statement. 
-/
namespace InexactRealizations.Probability.Gaussian
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem estimator_mse_decomposition (L : E →L[ℝ] F) (v : E) (m : F)
    (hker : L (v - L.adjoint m) = 0) (f : F → ℝ) (hf : Measurable f)
    (h₂ : MemLp (fun x : E ↦ inner ℝ v x - f (L x)) 2 (stdGaussian E)) :
    (∫ x, (inner ℝ v x - f (L x)) ^ 2 ∂stdGaussian E) =
      ‖v - L.adjoint m‖ ^ 2 +
        ∫ x, (inner ℝ m (L x) - f (L x)) ^ 2 ∂stdGaussian E := by
  let u := v - L.adjoint m
  let d : F → ℝ := fun y ↦ inner ℝ m y - f y
  have hd : Measurable d := (innerSL ℝ m).continuous.measurable.sub hf
  have he (x : E) : inner ℝ v x - f (L x) = inner ℝ u x + d (L x) := by
    dsimp [u, d]
    rw [inner_sub_left, L.adjoint_inner_left]
    ring
  have hd₂ : MemLp (fun x : E ↦ d (L x)) 2 (stdGaussian E) := by
    convert h₂.sub (linear_memLp u) using 1
    funext x
    dsimp only [Pi.sub_apply]
    rw [he]
    ring
  have hind : IndepFun (fun x : E ↦ inner ℝ u x) (fun x : E ↦ d (L x)) (stdGaussian E) :=
    (residual_indep_observation L u hker).comp measurable_id hd
  have hcross : (∫ x, inner ℝ u x * d (L x) ∂stdGaussian E) = 0 := by
    have hh := hind.integral_mul_eq_mul_integral
      (linear_memLp u).aestronglyMeasurable hd₂.aestronglyMeasurable
    simpa only [Pi.mul_apply, linear_mean, zero_mul] using hh
  have hi₁ := (memLp_two_iff_integrable_sq (linear_memLp u).aestronglyMeasurable).mp (linear_memLp u)
  have hi₂ := (memLp_two_iff_integrable_sq hd₂.aestronglyMeasurable).mp hd₂
  have hic : Integrable (fun x : E ↦ inner ℝ u x * d (L x)) (stdGaussian E) := by
    simpa only [Real.inner_apply] using integrable_inner_of_memLp (linear_memLp u) hd₂
  have hs : (fun x : E ↦ (inner ℝ v x - f (L x)) ^ 2) =
      fun x ↦ (inner ℝ u x) ^ 2 + 2 * (inner ℝ u x * d (L x)) + d (L x) ^ 2 := by
    funext x
    rw [he]
    ring
  rw [hs]
  have hi := integral_add (hi₁.add (hic.const_mul 2)) hi₂
  dsimp only [Pi.add_apply] at hi
  rw [hi]
  have hi' := integral_add hi₁ (hic.const_mul 2)
  rw [hi', integral_const_mul, hcross, linear_second_moment]
  simp only [mul_zero, add_zero]
  rfl

theorem estimator_mse_lower (L : E →L[ℝ] F) (v : E) (m : F)
    (hker : L (v - L.adjoint m) = 0) (f : F → ℝ) (hf : Measurable f)
    (h₂ : MemLp (fun x : E ↦ inner ℝ v x - f (L x)) 2 (stdGaussian E)) :
    ‖v - L.adjoint m‖ ^ 2 ≤ ∫ x, (inner ℝ v x - f (L x)) ^ 2 ∂stdGaussian E := by
  rw [estimator_mse_decomposition L v m hker f hf h₂]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ ↦ sq_nonneg _))

theorem estimator_extended_mse_lower (L : E →L[ℝ] F) (v : E) (m : F)
    (hker : L (v - L.adjoint m) = 0) (f : F → ℝ) (hf : Measurable f) :
    ENNReal.ofReal (‖v - L.adjoint m‖ ^ 2) ≤
      ∫⁻ x, ENNReal.ofReal ((inner ℝ v x - f (L x)) ^ 2) ∂stdGaussian E := by
  let err : E → ℝ := fun x ↦ inner ℝ v x - f (L x)
  have herr : Measurable err := (innerSL ℝ v).continuous.measurable.sub (hf.comp L.continuous.measurable)
  by_cases hfin : (∫⁻ x, ENNReal.ofReal (err x ^ 2) ∂stdGaussian E) < ⊤
  · have hi : Integrable (fun x ↦ err x ^ 2) (stdGaussian E) :=
      ⟨(herr.pow_const 2).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ ↦ sq_nonneg _))).mpr hfin⟩
    have h₂ : MemLp err 2 (stdGaussian E) :=
      (memLp_two_iff_integrable_sq herr.aestronglyMeasurable).mpr hi
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ ↦ sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (estimator_mse_lower L v m hker f hf h₂)
  · have ht : (∫⁻ x, ENNReal.ofReal (err x ^ 2) ∂stdGaussian E) = ⊤ :=
      top_unique (not_lt.mp hfin)
    change _ ≤ ∫⁻ x, ENNReal.ofReal (err x ^ 2) ∂stdGaussian E
    rw [ht]
    exact le_top

end
end InexactRealizations.Probability.Gaussian
