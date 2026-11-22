import InexactRealizations.Probability.GaussianBayes
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The literal one-dimensional Gaussian instance:
the hidden minimizer is `r * x none`, and observation `s` is
`mu * r * x none - sigma * x (some s)`. Only the observation vector is
an argument of the estimator. 
-/
namespace InexactRealizations.Probability.Gaussian
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

abbrev Sample (N : ℕ) := EuclideanSpace ℝ (Option (Fin N))
abbrev Observations (N : ℕ) := EuclideanSpace ℝ (Fin N)

def observationLinear (N : ℕ) (mu r sigma : ℝ) : Sample N →ₗ[ℝ] Observations N where
  toFun x := WithLp.toLp 2 (fun s ↦ mu * r * x none - sigma * x (some s))
  map_add' x y := by ext s; simp; ring
  map_smul' a x := by ext s; simp; ring

def observation (N : ℕ) (mu r sigma : ℝ) : Sample N →L[ℝ] Observations N :=
  (observationLinear N mu r sigma).toContinuousLinearMap

@[simp] theorem observation_apply (N : ℕ) (mu r sigma : ℝ) (x : Sample N) (s : Fin N) :
    observation N mu r sigma x s = mu * r * x none - sigma * x (some s) := rfl

def hiddenVector (N : ℕ) (r : ℝ) : Sample N := EuclideanSpace.single none r

@[simp] theorem hidden_inner (N : ℕ) (r : ℝ) (x : Sample N) :
    inner ℝ (hiddenVector N r) x = r * x none := by
  simp [hiddenVector, EuclideanSpace.inner_single_left]

def denominator (N : ℕ) (mu r sigma : ℝ) : ℝ := sigma ^ 2 + N * mu ^ 2 * r ^ 2

def posteriorCoefficient (N : ℕ) (mu r sigma : ℝ) : ℝ := mu * r ^ 2 / denominator N mu r sigma

def posteriorVector (N : ℕ) (mu r sigma : ℝ) : Observations N :=
  WithLp.toLp 2 (fun _ ↦ posteriorCoefficient N mu r sigma)

theorem observation_adjoint_none (N : ℕ) (mu r sigma : ℝ) (m : Observations N) :
    (observation N mu r sigma).adjoint m none = mu * r * ∑ s, m s := by
  have hh := (observation N mu r sigma).adjoint_inner_right
    (EuclideanSpace.single none 1) m
  rw [EuclideanSpace.inner_single_left] at hh
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.mul_sum,
    Finset.sum_mul, mul_comm] using hh

theorem observation_adjoint_some (N : ℕ) (mu r sigma : ℝ) (m : Observations N) (s : Fin N) :
    (observation N mu r sigma).adjoint m (some s) = -sigma * m s := by
  have hh := (observation N mu r sigma).adjoint_inner_right
    (EuclideanSpace.single (some s) 1) m
  rw [EuclideanSpace.inner_single_left] at hh
  simpa [EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, mul_ite, ite_mul, mul_comm] using hh

theorem residual_none (N : ℕ) (mu r sigma : ℝ) (hD : denominator N mu r sigma ≠ 0) :
    (hiddenVector N r - (observation N mu r sigma).adjoint (posteriorVector N mu r sigma)) none =
      r * sigma ^ 2 / denominator N mu r sigma := by
  rw [PiLp.sub_apply, observation_adjoint_none]
  change r - mu * r * ∑ _ : Fin N, posteriorCoefficient N mu r sigma = _
  simp only [posteriorCoefficient, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hi := mul_inv_cancel₀ hD
  unfold denominator at *
  simp only [div_eq_mul_inv]
  linear_combination -r * hi

theorem residual_some (N : ℕ) (mu r sigma : ℝ) (s : Fin N) :
    (hiddenVector N r - (observation N mu r sigma).adjoint (posteriorVector N mu r sigma)) (some s) =
      sigma * posteriorCoefficient N mu r sigma := by
  simp [hiddenVector, observation_adjoint_some, posteriorVector]

theorem posterior_residual_kernel (N : ℕ) (mu r sigma : ℝ) (hD : denominator N mu r sigma ≠ 0) :
    observation N mu r sigma
      (hiddenVector N r - (observation N mu r sigma).adjoint (posteriorVector N mu r sigma)) = 0 := by
  ext s
  rw [observation_apply, residual_none N mu r sigma hD, residual_some]
  simp only [posteriorCoefficient, PiLp.zero_apply]
  ring

theorem posterior_residual_norm (N : ℕ) (mu r sigma : ℝ) (hD : denominator N mu r sigma ≠ 0) :
    ‖hiddenVector N r - (observation N mu r sigma).adjoint (posteriorVector N mu r sigma)‖ ^ 2 =
      r ^ 2 * sigma ^ 2 / denominator N mu r sigma := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_option]
  simp_rw [residual_none N mu r sigma hD, residual_some]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    posteriorCoefficient]
  unfold denominator at *
  field_simp [hD]

theorem gaussian_mean_lower (N : ℕ) (mu r sigma : ℝ) (hD : denominator N mu r sigma ≠ 0)
    (f : Observations N → ℝ) (hf : Measurable f) :
    ENNReal.ofReal (r ^ 2 * sigma ^ 2 / denominator N mu r sigma) ≤
      ∫⁻ x : Sample N, ENNReal.ofReal ((r * x none - f (observation N mu r sigma x)) ^ 2)
        ∂stdGaussian (Sample N) := by
  have hh := estimator_extended_mse_lower (observation N mu r sigma) (hiddenVector N r)
    (posteriorVector N mu r sigma) (posterior_residual_kernel N mu r sigma hD) f hf
  simpa only [posterior_residual_norm N mu r sigma hD, hidden_inner] using hh

theorem hidden_mean_budget (N : ℕ) (r : ℝ) :
    (∫ x : Sample N, (r * x none) ^ 2 ∂stdGaussian (Sample N)) = r ^ 2 := by
  have hh := linear_second_moment (hiddenVector N r)
  simp_rw [hidden_inner] at hh
  simpa [hiddenVector] using hh

end
end InexactRealizations.Probability.Gaussian
