import InexactRealizations.Averages.Measure
import InexactRealizations.Budgets.SpectralMeasure
import InexactRealizations.Prose.RawMoments

/-! The unnumbered isotropic-noise identity before, with the
actual empirical eigenvalue probability measure of the actual Hessian. 
-/
namespace InexactRealizations.Prose
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Filter
open scoped BigOperators
variable {N : ℕ} {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def eigenArray (I : InexactRealizations.Operators.SpectralInterval) (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) :
    InexactRealizations.Budgets.FiniteSpectrum I where
  size := Module.finrank ℝ E
  point := hH.1.eigenvalues rfl
  point_mem i := hH.2 _ (hH.1.hasEigenvalue_eigenvalues rfl i)
  weight _ := (Module.finrank ℝ E : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hd : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
    exact mul_inv_cancel₀ hd.ne'

def eigenLaw (I : InexactRealizations.Operators.SpectralInterval) (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) :
    InexactRealizations.Averages.SpectralLaw I where
  measure := (eigenArray I H hH).toMeasure
  probability := inferInstance
  spectral := by
    filter_upwards [(eigenArray I H hH).asSpectralMeasure.ae_support] with x hx
    exact (eigenArray I H hH).asSpectralMeasure.support_mem x hx

omit [CompleteSpace E] in
theorem eigenLaw_energy (I : InexactRealizations.Operators.SpectralInterval) (H : E →ₗ[ℝ] E)
    (hH : InexactRealizations.Analysis.Admissible I H) (p : ℝ[X]) :
    (eigenLaw I H hH).energy p = (Module.finrank ℝ E : ℝ)⁻¹ *
      ∑ i : Fin (Module.finrank ℝ E), p.eval (hH.1.eigenvalues rfl i) ^ 2 := by
  change (∫ x, p.eval x ^ 2 ∂(eigenArray I H hH).toMeasure) = _
  rw [InexactRealizations.Budgets.FiniteSpectrum.toMeasure_integral, Finset.mul_sum]
  rfl

omit [CompleteSpace E] [IsProbabilityMeasure μ] in
theorem isotropic_polynomial_energy (I : InexactRealizations.Operators.SpectralInterval) (H : E →ₗ[ℝ] E)
    (hH : InexactRealizations.Analysis.Admissible I H) (p : ℝ[X]) (X : Ω → E) (hX : MemLp X 2 μ) (σ : ℝ)
    (hiso : ∀ v : E, (∫ ω, (inner ℝ v (X ω)) ^ 2 ∂μ) = σ ^ 2 / Module.finrank ℝ E * ‖v‖ ^ 2) :
    (∫ ω, ‖(aeval H p) (X ω)‖ ^ 2 ∂μ) = σ ^ 2 * (eigenLaw I H hH).energy p := by
  let b := hH.1.eigenvectorBasis rfl
  have he (ω : Ω) : ‖(aeval H p) (X ω)‖ ^ 2 = ∑ i : Fin (Module.finrank ℝ E),
      p.eval (hH.1.eigenvalues rfl i) ^ 2 * (inner ℝ (b i) (X ω)) ^ 2 := by
    rw [← b.repr.norm_map, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [InexactRealizations.Analysis.polynomial_spectral_coordinates]
    simp only [mul_pow, Real.norm_eq_abs, sq_abs]
    change p.eval (hH.1.eigenvalues rfl i) ^ 2 * (b.repr (X ω) i) ^ 2 = _
    rw [b.repr_apply_apply]
  have hi (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun ω ↦ p.eval (hH.1.eigenvalues rfl i) ^ 2 * (inner ℝ (b i) (X ω)) ^ 2) μ := by
    have hh := (hX.continuousLinearMap_comp (innerSL ℝ (b i))).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have hi0 : Integrable (fun ω ↦ (inner ℝ (b i) (X ω)) ^ 2) μ := by
      simpa only [Real.norm_eq_abs, sq_abs, innerSL_apply_apply] using hh
    exact hi0.const_mul _
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hi i)]
  simp_rw [integral_const_mul, hiso, b.orthonormal.norm_eq_one, one_pow, mul_one]
  rw [eigenLaw_energy]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem isotropic_mse_average (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (initial : E)
    (𝓕 : Filtration ℕ mΩ) (w : ℕ → Ω → E) (σ : ℝ) (hw : RawAdditiveLaw N 𝓕 w μ σ)
    (hiso : ∀ s, s < N → ∀ v : E,
      μ[fun ω ↦ (inner ℝ v (w s ω)) ^ 2 | 𝓕 s] =ᵐ[μ]
        fun _ ↦ σ ^ 2 / Module.finrank ℝ E * ‖v‖ ^ 2) :
    (∫ ω, ‖h.stochasticOutput H initial w ω‖ ^ 2 ∂μ) =
      ‖(aeval H h.terminal) initial‖ ^ 2 + σ ^ 2 * (eigenLaw I H hH).variance h := by
  rw [h.integral_stochasticOutput_norm_sq H initial hw.martingale]
  congr 1
  rw [InexactRealizations.Averages.SpectralLaw.variance, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply isotropic_polynomial_energy I H hH _ _ (hw.squareIntegrable s.val s.isLt) σ
  intro v
  rw [← integral_condExp (𝓕.le s.val), integral_congr_ae (hiso s.val s.isLt v)]
  simp

end
end InexactRealizations.Prose
