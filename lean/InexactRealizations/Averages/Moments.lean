import InexactRealizations.Averages.EvenMoments
import InexactRealizations.Averages.MomentPolynomials

/-! The exact squared-U moments, for the actual
uniform and arcsine spectral probability measures. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Polynomial Polynomial.Chebyshev MeasureTheory
open scoped BigOperators

def oddHarmonic (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, (2 * (j : ℝ) + 1)⁻¹

theorem moment_succ {I : InexactRealizations.Operators.SpectralInterval} (ρ : SpectralLaw I) (k : ℕ) :
    moment ρ (k + 1) = moment ρ k + ∫ x, (U ℝ (2 * (k : ℤ))).eval (I.z x) ∂ρ.measure := by
  have hi0 : Integrable (fun x ↦ (U ℝ (k : ℤ)).eval (I.z x) ^ 2) ρ.measure :=
    ρ.continuous_integrable (by unfold InexactRealizations.Operators.SpectralInterval.z; fun_prop)
  have hi1 : Integrable (fun x ↦ (U ℝ ((k : ℤ) - 1)).eval (I.z x) ^ 2) ρ.measure :=
    ρ.continuous_integrable (by unfold InexactRealizations.Operators.SpectralInterval.z; fun_prop)
  have hd : moment ρ (k + 1) - moment ρ k =
      ∫ x, (U ℝ (2 * (k : ℤ))).eval (I.z x) ∂ρ.measure := by
    unfold moment
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [← integral_sub hi0 hi1]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      have he := congrArg (fun p : ℝ[X] ↦ p.eval (I.z x)) (secondKind_square_difference k)
      simpa only [eval_sub, eval_pow] using he
  linarith

theorem arcsine_moment (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) : moment (arcsine I) k = (k : ℝ) := by
  induction k with
  | zero => exact (moment_zero _).trans (by norm_num)
  | succ k ih => rw [moment_succ, even_second_arcsine_physical, ih, Nat.cast_add, Nat.cast_one]

theorem uniform_moment (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) : moment (uniform I) k = oddHarmonic k := by
  induction k with
  | zero => exact (moment_zero _).trans (by simp [oddHarmonic])
  | succ k ih =>
    rw [moment_succ, even_second_uniform_physical, ih]
    simp only [oddHarmonic, Finset.sum_range_succ, one_div]

theorem oddHarmonic_nonneg (k : ℕ) : 0 ≤ oddHarmonic k :=
  Finset.sum_nonneg fun j _ ↦ by positivity

end
end InexactRealizations.Averages
