import InexactRealizations.Centered.Spectral
import InexactRealizations.Budgets.Corner

/-! The unnumbered gamma=1 identity following:
the literal relative and operator gains equal max_s barPhi_s*barPi_s. 
-/
namespace InexactRealizations.Prose
noncomputable section
open InexactRealizations.Budgets InexactRealizations.Centered
open scoped BigOperators ENNReal NNReal
variable {N : ℕ}

def queryPeak (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (s : Fin N) : ℝ :=
  polynomialPeak I (h.query s)

theorem singleCall_operatorGain (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (hN : 0 < N) (symmetric : Bool) :
    operatorGain 1 h I symmetric = callNorm ∞ (fun s ↦ responsePeak h I s * queryPeak h I s) := by
  let : (1 : ℝ≥0∞).HolderConjugate ∞ := ENNReal.HolderConjugate.one_top
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  apply le_antisymm
  · exact operatorGain_upper h I symmetric _ _ (responsePeak_bounds h I)
      (fun s ↦ polynomialPeak_nonneg I (h.query s))
      (fun s x hx ↦ polynomialPeak_bound I (h.query s) x hx)
  · rw [callNorm_top]
    apply ciSup_le
    intro s
    obtain ⟨x, hx, hpx⟩ := responsePeak_attained h I s
    obtain ⟨y, hy, hqy⟩ := polynomialPeak_attained I (h.query s)
    have hh := operator_kernel_lower (p := 1) (q := ∞) h I symmetric x y hx hy
    have hc := coordinate_le_norm (p := ∞) (fun j ↦ InexactRealizations.Lower.physicalKernel h j x y) s
    have he : |responsePeak h I s * queryPeak h I s| = |InexactRealizations.Lower.physicalKernel h s x y| := by
      rw [hpx]
      change abs (abs ((h.response s).eval x) * polynomialPeak I (h.query s)) = _
      rw [hqy, abs_mul, abs_abs, abs_abs]
      exact (abs_mul _ _).symm
    exact he.trans_le (hc.trans hh)

theorem singleCall_relativeGain (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (hN : 0 < N) (r : ℝ) (hr : 0 < r) :
    localRelativeGain 1 h I r = callNorm ∞ (fun s ↦ responsePeak h I s * queryPeak h I s) := by
  rw [localRelativeGain_eq_operatorGain 1 le_rfl h I r hr]
  exact singleCall_operatorGain h I hN false

end
end InexactRealizations.Prose
