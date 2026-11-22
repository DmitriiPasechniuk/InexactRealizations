import InexactRealizations.Budgets.FiniteSpectrum
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! The finite arrays in the spectral dualities are exactly the finitely
supported probability measures on spectral interval. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators ENNReal
variable {I : InexactRealizations.Operators.SpectralInterval}

def FiniteSpectrum.toMeasure (alpha : FiniteSpectrum I) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (alpha.weight i) • Measure.dirac (alpha.point i)

instance FiniteSpectrum.toMeasure_probability (alpha : FiniteSpectrum I) :
    IsProbabilityMeasure alpha.toMeasure where
  measure_univ := by
    simp only [FiniteSpectrum.toMeasure, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ alpha.nonneg i), alpha.total]
    norm_num

theorem FiniteSpectrum.toMeasure_integral (alpha : FiniteSpectrum I) (f : ℝ → ℝ) :
    ∫ x, f x ∂alpha.toMeasure = ∑ i, alpha.weight i * f (alpha.point i) := by
  rw [FiniteSpectrum.toMeasure, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (alpha.nonneg _), smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

theorem FiniteSpectrum.polynomialNorm_eq_integral (alpha : FiniteSpectrum I) (p : ℝ[X]) :
    alpha.polynomialNorm p = Real.sqrt (∫ x, p.eval x ^ 2 ∂alpha.toMeasure) := by
  rw [alpha.toMeasure_integral]
  rfl

structure FiniteSpectralMeasure (I : InexactRealizations.Operators.SpectralInterval) where
  measure : Measure ℝ
  probability : IsProbabilityMeasure measure
  support : Finset ℝ
  support_mem : ∀ x ∈ support, x ∈ Set.Icc I.mu I.L
  ae_support : ∀ᵐ x ∂measure, x ∈ support

instance (alpha : FiniteSpectralMeasure I) : IsProbabilityMeasure alpha.measure := alpha.probability

def FiniteSpectrum.asSpectralMeasure (alpha : FiniteSpectrum I) : FiniteSpectralMeasure I where
  measure := alpha.toMeasure
  probability := inferInstance
  support := Finset.univ.image alpha.point
  support_mem x hx := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact alpha.point_mem i
  ae_support := by
    rw [FiniteSpectrum.toMeasure, ae_finsetSum_measure_iff]
    intro i _
    apply Measure.ae_smul_measure
    rw [ae_dirac_iff]
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · exact (Finset.univ.image alpha.point).measurableSet

namespace FiniteSpectralMeasure

theorem atom_sum (alpha : FiniteSpectralMeasure I) :
    ∑ x ∈ alpha.support, alpha.measure {x} = 1 := by
  have hh := congrArg (fun m : Measure ℝ ↦ m Set.univ)
    (Measure.ae_mem_finset_iff.mp alpha.ae_support)
  simpa only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one, measure_univ] using hh.symm

def toSpectrum (alpha : FiniteSpectralMeasure I) : FiniteSpectrum I where
  size := Fintype.card alpha.support
  point i := ((Fintype.equivFin alpha.support).symm i : ℝ)
  point_mem i := alpha.support_mem _ ((Fintype.equivFin alpha.support).symm i).property
  weight i := (alpha.measure {((Fintype.equivFin alpha.support).symm i : ℝ)}).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    calc
      _ = ∑ x : alpha.support, (alpha.measure {(x : ℝ)}).toReal :=
        Equiv.sum_comp (Fintype.equivFin alpha.support).symm _
      _ = ∑ x ∈ alpha.support, (alpha.measure {x}).toReal := by
        simpa only [Finset.univ_eq_attach] using Finset.sum_attach alpha.support
          (fun x ↦ (alpha.measure {x}).toReal)
      _ = (∑ x ∈ alpha.support, alpha.measure {x}).toReal :=
        (ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)).symm
      _ = 1 := by rw [alpha.atom_sum]; norm_num

theorem toSpectrum_measure (alpha : FiniteSpectralMeasure I) :
    alpha.toSpectrum.toMeasure = alpha.measure := by
  calc
    _ = ∑ x : alpha.support, alpha.measure {(x : ℝ)} • Measure.dirac (x : ℝ) := by
      simp only [FiniteSpectrum.toMeasure, toSpectrum, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact Equiv.sum_comp (Fintype.equivFin alpha.support).symm
        (fun x : alpha.support ↦ alpha.measure {(x : ℝ)} • Measure.dirac (x : ℝ))
    _ = ∑ x ∈ alpha.support, alpha.measure {x} • Measure.dirac x := by
      simpa only [Finset.univ_eq_attach] using Finset.sum_attach alpha.support
        (fun x ↦ alpha.measure {x} • Measure.dirac x)
    _ = alpha.measure := (Measure.ae_mem_finset_iff.mp alpha.ae_support).symm

def polynomialNorm (alpha : FiniteSpectralMeasure I) (p : ℝ[X]) : ℝ :=
  Real.sqrt (∫ x, p.eval x ^ 2 ∂alpha.measure)

theorem toSpectrum_polynomialNorm (alpha : FiniteSpectralMeasure I) (p : ℝ[X]) :
    alpha.toSpectrum.polynomialNorm p = alpha.polynomialNorm p := by
  rw [alpha.toSpectrum.polynomialNorm_eq_integral, alpha.toSpectrum_measure]
  rfl

end FiniteSpectralMeasure
end
end InexactRealizations.Budgets
