import InexactRealizations.Budgets.CommonSpectrum
import InexactRealizations.Budgets.OperatorSupport
import InexactRealizations.Budgets.SpectralAdditive

/-! The full two-measure operator duality of AppendixA, for every call
exponent and both unrestricted and symmetric physical perturbations. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial
open scoped BigOperators ENNReal NNReal
variable {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]

def operatorSpectralValue (q : ℝ≥0∞) (h : InexactRealizations.History N)
    {I : InexactRealizations.Operators.SpectralInterval} (alpha beta : FiniteSpectrum I) : ℝ :=
  callNorm q (fun s ↦ alpha.polynomialNorm (h.response s) * beta.polynomialNorm (h.query s))

def operatorSpectralValues (q : ℝ≥0∞) (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) : Set ℝ :=
  {v | ∃ alpha beta : FiniteSpectrum I, v = operatorSpectralValue q h alpha beta}

theorem operatorSpectralValue_le_gain (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (hN : 0 < N) (symmetric : Bool) (alpha beta : FiniteSpectrum I) :
    operatorSpectralValue q h alpha beta ≤ operatorGain p h I symmetric := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let H := FiniteSpectrum.diagonal (FiniteSpectrum.jointPoints alpha beta)
  let e := FiniteSpectrum.leftVector alpha beta
  let v := FiniteSpectrum.rightVector alpha beta
  have hH := FiniteSpectrum.joint_admissible alpha beta
  have he := FiniteSpectrum.leftVector_norm alpha beta
  have hv := FiniteSpectrum.rightVector_norm alpha beta
  obtain ⟨D, delta, hd, hsym, hD, hs⟩ :=
    operator_support_attained (p := p) (q := q) h H hH.1 e v he
  have hh := real_inner_le_norm e (h.firstVariation H D v)
  rw [hs, he, one_mul] at hh
  dsimp only [H, e, v] at hh
  simp_rw [FiniteSpectrum.joint_left, FiniteSpectrum.joint_right] at hh
  exact hh.trans (le_csSup (operatorValues_bddAbove (p := p) (q := q) h I symmetric)
    (OperatorValue.execution _ H hH D delta hd hD (fun _ ↦ hsym) v hv.le))

include p in
theorem operatorSpectralValues_bddAbove (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (hN : 0 < N) : BddAbove (operatorSpectralValues q h I) := by
  refine ⟨operatorGain p h I false, ?_⟩
  rintro z ⟨alpha, beta, rfl⟩
  exact operatorSpectralValue_le_gain (p := p) h I hN false alpha beta

theorem operator_spectral_duality (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (hN : 0 < N) (symmetric : Bool) :
    operatorGain p h I symmetric = sSup (operatorSpectralValues q h I) := by
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hbd := operatorSpectralValues_bddAbove (p := p) (q := q) h I hN
  have hmem : operatorSpectralValue q h (FiniteSpectrum.pointMass I) (FiniteSpectrum.pointMass I) ∈
      operatorSpectralValues q h I := ⟨_, _, rfl⟩
  have hnonneg : 0 ≤ sSup (operatorSpectralValues q h I) :=
    (callNorm_nonneg _).trans (le_csSup hbd hmem)
  apply le_antisymm
  · apply csSup_le (operatorValues_nonempty (p := p) (q := q) h I symmetric)
    intro z hz
    cases hz with
    | execution E H hH D delta hd hD hsym initial hi =>
      by_cases hz : h.firstVariation H D initial = 0
      · simpa only [hz, norm_zero] using hnonneg
      have hni : initial ≠ 0 := by
        intro hi0
        apply hz
        simp only [hi0, InexactRealizations.History.firstVariation, InexactRealizations.History.variationNoise,
          map_zero, Finset.sum_const_zero]
      have hnv : 0 < ‖initial‖ := norm_pos_iff.mpr hni
      have hne : 0 < ‖h.firstVariation H D initial‖ := norm_pos_iff.mpr hz
      let e := ‖h.firstVariation H D initial‖⁻¹ • h.firstVariation H D initial
      let v := ‖initial‖⁻¹ • initial
      have he : ‖e‖ = 1 := by
        simp only [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hne)]
        exact inv_mul_cancel₀ hne.ne'
      have hv : ‖v‖ = 1 := by
        simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnv)]
        exact inv_mul_cancel₀ hnv.ne'
      have hei : inner ℝ e (h.firstVariation H D v) =
          ‖initial‖⁻¹ * ‖h.firstVariation H D initial‖ := by
        simp only [v, firstVariation_smul, inner_smul_right, e, real_inner_smul_left,
          real_inner_self_eq_norm_sq]
        field_simp
      have hh := operator_support_upper (p := p) (q := q) h H hH.1 D delta hd hD e v
      rw [hei] at hh
      let alpha := FiniteSpectrum.ofVector H hH e he
      let beta := FiniteSpectrum.ofVector H hH v hv
      have ha : operatorSpectralValue q h alpha beta =
          callNorm q (fun s ↦ ‖(aeval H (h.response s)) e‖ * ‖(aeval H (h.query s)) v‖) := by
        simp only [operatorSpectralValue, alpha, beta, FiniteSpectrum.ofVector_polynomialNorm]
      rw [← ha] at hh
      have hsup := le_csSup hbd (show operatorSpectralValue q h alpha beta ∈
        operatorSpectralValues q h I from ⟨alpha, beta, rfl⟩)
      have hdiv : ‖h.firstVariation H D initial‖ / ‖initial‖ ≤ sSup (operatorSpectralValues q h I) := by
        simpa only [div_eq_mul_inv, mul_comm] using hh.trans hsup
      have hmul := (div_le_iff₀ hnv).mp hdiv
      exact hmul.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hi hnonneg)
  · apply csSup_le (s := operatorSpectralValues q h I) ⟨_, hmem⟩
    rintro z ⟨alpha, beta, rfl⟩
    exact operatorSpectralValue_le_gain h I hN symmetric alpha beta

end
end InexactRealizations.Budgets
