import InexactRealizations.Budgets.RelativeIdentity
import InexactRealizations.Budgets.Radius
import InexactRealizations.Budgets.Equality

/-! All-gamma relative corner chain, with the literal radius-normalized
positive-scale limsup in the journal definition. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open scoped ENNReal NNReal
variable {N : ℕ}

theorem localRelativeGain_eq_operatorGain (p : ℝ≥0∞) (hp : 1 ≤ p)
    (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r : ℝ) (hr : 0 < r) :
    localRelativeGain p h I r = operatorGain p h I false := by
  let : p.HolderConjugate (dualExponent p) := holder_dualExponent p hp
  rw [localRelativeGain_radius (p := p) (q := dualExponent p) h I r hr]
  exact localRelativeGain_one_eq_operatorGain (p := p) (q := dualExponent p) h I

theorem relative_corner_chain (p : ℝ≥0∞) (hp : 1 ≤ p) (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (he : h.ChebyshevExact I) (hN : 0 < N)
    (r : ℝ) (hr : 0 < r) :
    localRelativeGain p h I r = operatorGain p h I false ∧
      callNorm (dualExponent p) (fun s : Fin N ↦
        (h.response s).eval I.mu * (h.query s).eval I.mu) ≤ localRelativeGain p h I r ∧
      (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.derivativeScale I N ≤
        callNorm (dualExponent p) (fun s : Fin N ↦
          (h.response s).eval I.mu * (h.query s).eval I.mu) := by
  let : p.HolderConjugate (dualExponent p) := holder_dualExponent p hp
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine ⟨localRelativeGain_eq_operatorGain p hp h I r hr, ?_,
    relative_endpoint_lower (p := p) (q := dualExponent p) h I he hN⟩
  rw [localRelativeGain_eq_operatorGain p hp h I r hr]
  exact operator_kernel_lower (p := p) (q := dualExponent p) h I false I.mu I.mu
    ⟨le_rfl, I.mu_lt_L.le⟩ ⟨le_rfl, I.mu_lt_L.le⟩

end
end InexactRealizations.Budgets
