import InexactRealizations.Averages.Kernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The actual uniform and arcsine spectral probability measures. The latter
is the affine image of the literal density dx/(pi*sqrt(1-x^2)). 
-/
namespace InexactRealizations.Averages
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Polynomial.Chebyshev MeasureTheory Set Real

def unitLaw : Measure ℝ := volume.restrict (Ioc 0 1)

instance unitLaw_probability : IsProbabilityMeasure unitLaw :=
  ⟨by simp [unitLaw]⟩

theorem unitLaw_spectral : ∀ᵐ x ∂unitLaw, x ∈ Icc 0 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact ⟨hx.1.le, hx.2⟩

def uniform (I : InexactRealizations.Operators.SpectralInterval) : SpectralLaw I where
  measure := unitLaw.map (fun u ↦ I.mu + I.delta * u)
  probability := inferInstance
  spectral := by
    apply (ae_map_iff (by fun_prop) (by measurability)).mpr
    filter_upwards [unitLaw_spectral] with u hu
    have hd := I.delta_pos
    change I.mu ≤ I.mu + I.delta * u ∧ I.mu + I.delta * u ≤ I.L
    dsimp only [InexactRealizations.Operators.SpectralInterval.delta] at *
    constructor <;> nlinarith [hu.1, hu.2]

theorem integral_uniform (I : InexactRealizations.Operators.SpectralInterval) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂(uniform I).measure) = ∫ u in (0 : ℝ)..1, f (I.mu + I.delta * u) := by
  change (∫ x, f x ∂unitLaw.map (fun u ↦ I.mu + I.delta * u)) = _
  rw [integral_map_of_stronglyMeasurable (by fun_prop) hf.stronglyMeasurable,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rfl

instance measureT_finite : IsFiniteMeasure measureT :=
  (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp (integrable_measureT (by fun_prop))

theorem measureT_mass : (measureT univ).toReal = π := by
  have hh := integral_eval_T_real_measureT_zero
  simpa only [T_zero, eval_one, integral_const, smul_eq_mul, mul_one, measureReal_def] using hh

def arcsineBase : Measure ℝ := ENNReal.ofReal π⁻¹ • measureT

instance arcsineBase_probability : IsProbabilityMeasure arcsineBase := by
  apply isProbabilityMeasure_iff_real.mpr
  change (arcsineBase univ).toReal = 1
  rw [arcsineBase, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr pi_pos.le), measureT_mass, inv_mul_cancel₀ pi_ne_zero]

theorem arcsineBase_spectral : ∀ᵐ x ∂arcsineBase, x ∈ Icc (-1) 1 := by
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact ⟨hx.1.le, hx.2⟩

def arcsine (I : InexactRealizations.Operators.SpectralInterval) : SpectralLaw I where
  measure := arcsineBase.map (fun z ↦ (I.L + I.mu - I.delta * z) / 2)
  probability := inferInstance
  spectral := by
    apply (ae_map_iff (by fun_prop) (by measurability)).mpr
    filter_upwards [arcsineBase_spectral] with z hz
    have hd := I.delta_pos
    change I.mu ≤ (I.L + I.mu - I.delta * z) / 2 ∧ (I.L + I.mu - I.delta * z) / 2 ≤ I.L
    dsimp only [InexactRealizations.Operators.SpectralInterval.delta] at *
    constructor <;> nlinarith [hz.1, hz.2]

theorem integral_arcsine (I : InexactRealizations.Operators.SpectralInterval) {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂(arcsine I).measure) =
      π⁻¹ * ∫ z, f ((I.L + I.mu - I.delta * z) / 2) ∂measureT := by
  change (∫ x, f x ∂arcsineBase.map (fun z ↦ (I.L + I.mu - I.delta * z) / 2)) = _
  rw [integral_map_of_stronglyMeasurable (by fun_prop) hf.stronglyMeasurable,
    arcsineBase, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr pi_pos.le), smul_eq_mul]

theorem uniform_coordinate (I : InexactRealizations.Operators.SpectralInterval) (u : ℝ) :
    (I.mu + I.delta * u - I.mu) / I.delta = u := by field_simp [I.delta_pos.ne']; ring

theorem arcsine_coordinate (I : InexactRealizations.Operators.SpectralInterval) (z : ℝ) :
    I.z ((I.L + I.mu - I.delta * z) / 2) = z := by
  unfold InexactRealizations.Operators.SpectralInterval.z
  field_simp [I.delta_pos.ne']
  ring

end
end InexactRealizations.Averages
