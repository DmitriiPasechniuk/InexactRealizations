import InexactRealizations.Probability.GaussianMean
import InexactRealizations.Probability.AdaptiveOracle
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual adaptive Gaussian oracle executions, including independent
randomization. The product law supplies independence of the seed, and the
query/output interface exposes only the observable transcript. 
-/
namespace InexactRealizations.Probability.Gaussian
noncomputable section
open MeasureTheory ProbabilityTheory
variable {N : ℕ} {U : Type*} [MeasurableSpace U]

def physicalOracle (mu r sigma : ℝ) (x : Sample N) : Fin N → ℝ → ℝ :=
  fun s q ↦ mu * (q - r * x none) + sigma * x (some s)

theorem physicalOracle_eq_observation (mu r sigma : ℝ) (x : Sample N) :
    physicalOracle mu r sigma x = fun s q ↦ mu * q - observation N mu r sigma x s := by
  funext s q
  simp only [physicalOracle, observation_apply]
  ring

def gaussianOutput (M : AdaptiveMethod N ℝ U) (mu r sigma : ℝ) (p : U × Sample N) : ℝ :=
  M.oracleOutput (physicalOracle mu r sigma p.2) p.1

theorem output_observable (M : AdaptiveMethod N ℝ U) (mu r sigma : ℝ) (u : U) (x : Sample N) :
    gaussianOutput M mu r sigma (u, x) =
      M.observableOutput mu (u, fun s ↦ observation N mu r sigma x s) := by
  unfold gaussianOutput
  rw [physicalOracle_eq_observation]
  rfl

theorem measurable_gaussianOutput (M : AdaptiveMethod N ℝ U) (mu r sigma : ℝ) :
    Measurable (gaussianOutput M mu r sigma) := by
  have he : gaussianOutput M mu r sigma = fun p : U × Sample N ↦
      M.observableOutput mu (p.1, fun s ↦ observation N mu r sigma p.2 s) := by
    funext p
    exact output_observable M mu r sigma p.1 p.2
  rw [he]
  apply (M.measurable_observableOutput mu).comp
  apply measurable_fst.prodMk
  exact Measurable.of_eval fun s ↦ by fun_prop

theorem gaussian_adaptive_mse_lower (M : AdaptiveMethod N ℝ U) (mu r sigma : ℝ)
    (hD : denominator N mu r sigma ≠ 0) (u : U) :
    ENNReal.ofReal (r ^ 2 * sigma ^ 2 / denominator N mu r sigma) ≤
      ∫⁻ x : Sample N, ENNReal.ofReal
        ((r * x none - gaussianOutput M mu r sigma (u, x)) ^ 2) ∂stdGaussian (Sample N) := by
  let f : Observations N → ℝ := fun z ↦ M.observableOutput mu (u, fun s ↦ z s)
  have hf : Measurable f := by
    apply (M.measurable_observableOutput mu).comp
    exact measurable_const.prodMk (Measurable.of_eval fun s ↦ by fun_prop)
  have hh := gaussian_mean_lower N mu r sigma hD f hf
  simpa only [output_observable] using hh

theorem gaussian_randomized_mse_lower (M : AdaptiveMethod N ℝ U) (mu r sigma : ℝ)
    (hD : denominator N mu r sigma ≠ 0) (P : Measure U) [IsProbabilityMeasure P] :
    ENNReal.ofReal (r ^ 2 * sigma ^ 2 / denominator N mu r sigma) ≤
      ∫⁻ p : U × Sample N, ENNReal.ofReal
        ((r * p.2 none - gaussianOutput M mu r sigma p) ^ 2) ∂P.prod (stdGaussian (Sample N)) := by
  rw [lintegral_prod _ (by
    apply Measurable.aemeasurable
    apply Measurable.ennreal_ofReal
    exact ((measurable_const.mul (by fun_prop)).sub (measurable_gaussianOutput M mu r sigma)).pow_const 2)]
  calc
    _ = ∫⁻ _ : U, ENNReal.ofReal (r ^ 2 * sigma ^ 2 / denominator N mu r sigma) ∂P := by simp
    _ ≤ _ := lintegral_mono fun u ↦ gaussian_adaptive_mse_lower M mu r sigma hD u

end
end InexactRealizations.Probability.Gaussian
