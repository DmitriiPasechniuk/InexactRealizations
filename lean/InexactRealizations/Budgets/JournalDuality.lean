import InexactRealizations.Budgets.SpectralOperator
import InexactRealizations.Budgets.SpectralMeasure
import InexactRealizations.Budgets.Corner
import InexactRealizations.Budgets.OperatorNorm

/-! AppendixA.1 in the journal's probability-measure signature. -/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial
open scoped ENNReal NNReal
variable {N : ℕ}

def additiveMeasureValue (q : ℝ≥0∞) (h : InexactRealizations.History N) (r t : ℝ)
    {I : InexactRealizations.Operators.SpectralInterval} (alpha : FiniteSpectralMeasure I) : ℝ :=
  r * alpha.polynomialNorm h.terminal +
    t * callNorm q (fun s ↦ alpha.polynomialNorm (h.response s))

def additiveMeasureValues (q : ℝ≥0∞) (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (r t : ℝ) : Set ℝ :=
  Set.range (additiveMeasureValue q h r t (I := I))

def operatorMeasureValue (q : ℝ≥0∞) (h : InexactRealizations.History N)
    {I : InexactRealizations.Operators.SpectralInterval} (alpha beta : FiniteSpectralMeasure I) : ℝ :=
  callNorm q (fun s ↦ alpha.polynomialNorm (h.response s) * beta.polynomialNorm (h.query s))

def operatorMeasureValues (q : ℝ≥0∞) (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) : Set ℝ :=
  {v | ∃ alpha beta : FiniteSpectralMeasure I, v = operatorMeasureValue q h alpha beta}

theorem FiniteSpectrum.asSpectralMeasure_polynomialNorm {I : InexactRealizations.Operators.SpectralInterval}
    (alpha : FiniteSpectrum I) (p : ℝ[X]) :
    alpha.asSpectralMeasure.polynomialNorm p = alpha.polynomialNorm p := by
  exact (alpha.polynomialNorm_eq_integral p).symm

theorem additiveMeasureValues_eq (q : ℝ≥0∞) (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (r t : ℝ) :
    additiveMeasureValues q h I r t = additiveSpectralValues q h I r t := by
  ext z
  constructor
  · rintro ⟨alpha, rfl⟩
    refine ⟨alpha.toSpectrum, ?_⟩
    simp only [additiveSpectralValue, additiveMeasureValue, FiniteSpectralMeasure.toSpectrum_polynomialNorm]
  · rintro ⟨alpha, rfl⟩
    refine ⟨alpha.asSpectralMeasure, ?_⟩
    simp only [additiveSpectralValue, additiveMeasureValue, FiniteSpectrum.asSpectralMeasure_polynomialNorm]

theorem operatorMeasureValues_eq (q : ℝ≥0∞) (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) : operatorMeasureValues q h I = operatorSpectralValues q h I := by
  ext z
  constructor
  · rintro ⟨alpha, beta, rfl⟩
    refine ⟨alpha.toSpectrum, beta.toSpectrum, ?_⟩
    simp only [operatorSpectralValue, operatorMeasureValue, FiniteSpectralMeasure.toSpectrum_polynomialNorm]
  · rintro ⟨alpha, beta, rfl⟩
    refine ⟨alpha.asSpectralMeasure, beta.asSpectralMeasure, ?_⟩
    simp only [operatorSpectralValue, operatorMeasureValue, FiniteSpectrum.asSpectralMeasure_polynomialNorm]

theorem journal_additive_duality (p : ℝ≥0∞) (hp : 1 ≤ p) (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (he : h.ChebyshevExact I) (hN : 0 < N)
    (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    additiveRisk p h I r t = sSup (additiveMeasureValues (dualExponent p) h I r t) := by
  let : p.HolderConjugate (dualExponent p) := holder_dualExponent p hp
  rw [additiveMeasureValues_eq]
  exact additive_spectral_duality (p := p) (q := dualExponent p) h I he hN r t hr ht

theorem journal_relative_duality (p : ℝ≥0∞) (hp : 1 ≤ p) (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (hN : 0 < N) (r : ℝ) (hr : 0 < r) (symmetric : Bool) :
    localRelativeGain p h I r = operatorGain p h I symmetric ∧
      operatorGain p h I symmetric = sSup (operatorMeasureValues (dualExponent p) h I) := by
  let : p.HolderConjugate (dualExponent p) := holder_dualExponent p hp
  constructor
  · rw [localRelativeGain_eq_operatorGain p hp h I r hr]
    cases symmetric with
    | false => rfl
    | true => exact (operatorGain_symmetric (p := p) (q := dualExponent p) h I).symm
  · rw [operatorMeasureValues_eq]
    exact operator_spectral_duality (p := p) (q := dualExponent p) h I hN symmetric

theorem journal_relative_operatorNorm_duality (p : ℝ≥0∞) (hp : 1 ≤ p)
    (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (hN : 0 < N)
    (r : ℝ) (hr : 0 < r) (symmetric : Bool) :
    localRelativeGain p h I r = operatorNormGain p h I symmetric ∧
      operatorNormGain p h I symmetric = sSup (operatorMeasureValues (dualExponent p) h I) := by
  let : p.HolderConjugate (dualExponent p) := holder_dualExponent p hp
  rw [operatorNormGain_eq (p := p) (q := dualExponent p) h I symmetric]
  exact journal_relative_duality p hp h I hN r hr symmetric

end
end InexactRealizations.Budgets
