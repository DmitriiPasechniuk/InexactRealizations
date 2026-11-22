import InexactRealizations.Budgets.FiniteSpectrum
import InexactRealizations.Budgets.Additive

/-! AppendixA's additive duality, over every finite spectral probability
distribution, with actual executions attaining each directional support. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial
open scoped BigOperators ENNReal NNReal
variable {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]

def FiniteSpectrum.pointMass (I : InexactRealizations.Operators.SpectralInterval) : FiniteSpectrum I where
  size := 1
  point _ := I.mu
  point_mem _ := ⟨le_rfl, I.mu_lt_L.le⟩
  weight _ := 1
  nonneg _ := zero_le_one
  total := by simp

def additiveSpectralValue (q : ℝ≥0∞) (h : InexactRealizations.History N)
    (r t : ℝ) {I : InexactRealizations.Operators.SpectralInterval} (alpha : FiniteSpectrum I) : ℝ :=
  r * alpha.polynomialNorm h.terminal +
    t * callNorm q (fun s ↦ alpha.polynomialNorm (h.response s))

def additiveSpectralValues (q : ℝ≥0∞) (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (r t : ℝ) : Set ℝ :=
  Set.range (additiveSpectralValue q h r t (I := I))

theorem additiveSpectralValue_le_risk (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (alpha : FiniteSpectrum I) : additiveSpectralValue q h r t alpha ≤ additiveRisk p h I r t := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let H := FiniteSpectrum.diagonal alpha.point
  have hH := FiniteSpectrum.diagonal_admissible alpha.point alpha.point_mem
  obtain ⟨initial, noise, delta, hi, hd, hw, hs⟩ :=
    additive_support_attained (p := p) (q := q) h H hH.1 alpha.vector alpha.vector_norm hr ht
  have hp := real_inner_le_norm alpha.vector (h.run H initial noise).output
  rw [hs, alpha.vector_norm, one_mul] at hp
  dsimp only [H] at hp
  simp_rw [← alpha.polynomialNorm_eq_action] at hp
  exact hp.trans (le_csSup (additiveValues_bddAbove (p := p) (q := q) h I he ht)
    (AdditiveValue.execution _ H hH initial noise (h.run H initial noise) delta hi hd hw))

include p in
theorem additiveSpectralValues_bddAbove (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    BddAbove (additiveSpectralValues q h I r t) := by
  refine ⟨additiveRisk p h I r t, ?_⟩
  rintro v ⟨alpha, rfl⟩
  exact additiveSpectralValue_le_risk h I he hN r t hr ht alpha

theorem additive_spectral_duality (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    additiveRisk p h I r t = sSup (additiveSpectralValues q h I r t) := by
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hbd := additiveSpectralValues_bddAbove (p := p) (q := q) h I he hN r t hr ht
  have hnonneg : 0 ≤ sSup (additiveSpectralValues q h I r t) := by
    have ha : 0 ≤ additiveSpectralValue q h r t (FiniteSpectrum.pointMass I) :=
      add_nonneg (mul_nonneg hr (FiniteSpectrum.polynomialNorm_nonneg _ _))
        (mul_nonneg ht (callNorm_nonneg _))
    exact ha.trans (le_csSup hbd ⟨FiniteSpectrum.pointMass I, rfl⟩)
  apply le_antisymm
  · apply csSup_le (additiveValues_nonempty (p := p) (q := q) h I hr)
    intro v hv
    cases hv with
    | execution E H hH initial noise u delta hi hd hw =>
      by_cases hz : u.output = 0
      · simpa only [hz, norm_zero] using hnonneg
      have hn : 0 < ‖u.output‖ := norm_pos_iff.mpr hz
      let e := ‖u.output‖⁻¹ • u.output
      have he : ‖e‖ = 1 := by
        simp only [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
        exact inv_mul_cancel₀ hn.ne'
      have hei : inner ℝ e u.output = ‖u.output‖ := by
        simp only [e, real_inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp
      have hh := additive_support_upper (p := p) (q := q)
        h H hH.1 initial noise u e ht hi delta hd hw
      rw [hei] at hh
      let alpha := FiniteSpectrum.ofVector H hH e he
      have ha : additiveSpectralValue q h r t alpha =
          r * ‖(aeval H h.terminal) e‖ + t * callNorm q (fun s ↦ ‖(aeval H (h.response s)) e‖) := by
        simp only [additiveSpectralValue, alpha, FiniteSpectrum.ofVector_polynomialNorm]
      exact hh.trans (ha ▸ le_csSup hbd ⟨alpha, rfl⟩)
  · apply csSup_le (s := additiveSpectralValues q h I r t)
      ⟨additiveSpectralValue q h r t (FiniteSpectrum.pointMass I),
      ⟨FiniteSpectrum.pointMass I, rfl⟩⟩
    rintro v ⟨alpha, rfl⟩
    exact additiveSpectralValue_le_risk h I he hN r t hr ht alpha

end
end InexactRealizations.Budgets
