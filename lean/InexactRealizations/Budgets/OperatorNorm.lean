import InexactRealizations.Budgets.Operator

/-! The supremum of first variations on the unit ball is exactly the
journal's supremum of continuous operator norms. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial
open scoped BigOperators ENNReal NNReal
variable {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def variationMap (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (D : Fin N → E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  ∑ s, aeval H (h.response s) * D s * aeval H (h.query s)

omit [FiniteDimensional ℝ E] in
theorem variationMap_apply (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (D : Fin N → E →ₗ[ℝ] E) (v : E) : variationMap h H D v = h.firstVariation H D v := by
  simp only [variationMap, LinearMap.sum_apply, Module.End.mul_apply,
    InexactRealizations.History.firstVariation, InexactRealizations.History.variationNoise]

include q in
theorem operatorGain_nonneg (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (sym : Bool) :
    0 ≤ operatorGain p h I sym := by
  obtain ⟨v, hv⟩ := operatorValues_nonempty (p := p) (q := q) h I sym
  have h0 : 0 ≤ v := by cases hv; exact norm_nonneg _
  exact h0.trans (le_csSup (operatorValues_bddAbove (p := p) (q := q) h I sym) hv)

include q in
theorem variation_operatorNorm_le_gain (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (sym : Bool) (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H)
    (D : Fin N → E →ₗ[ℝ] E) (delta : Fin N → ℝ) (hd : Budget p delta)
    (hD : ∀ s, ‖(D s).toContinuousLinearMap‖ ≤ delta s)
    (hsym : sym = true → ∀ s, (D s).IsSymmetric) :
    ‖(variationMap h H D).toContinuousLinearMap‖ ≤ operatorGain p h I sym := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (operatorGain_nonneg (p := p) (q := q) h I sym)
  intro v hv
  change ‖variationMap h H D v‖ ≤ _
  rw [variationMap_apply]
  exact le_csSup (operatorValues_bddAbove (p := p) (q := q) h I sym)
    (OperatorValue.execution E H hH D delta hd hD hsym v hv.le)

inductive OperatorNormValue (p : ℝ≥0∞) (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (symmetric : Bool) : ℝ → Prop where
  | execution (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (D : Fin N → E →ₗ[ℝ] E)
      (delta : Fin N → ℝ) (hd : Budget p delta) (hD : ∀ s, ‖(D s).toContinuousLinearMap‖ ≤ delta s)
      (hsym : symmetric = true → ∀ s, (D s).IsSymmetric) :
      OperatorNormValue p h I symmetric ‖(variationMap h H D).toContinuousLinearMap‖

def operatorNormValues (p : ℝ≥0∞) (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (sym : Bool) : Set ℝ := {v | OperatorNormValue p h I sym v}

def operatorNormGain (p : ℝ≥0∞) (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (sym : Bool) : ℝ := sSup (operatorNormValues p h I sym)

include q in
theorem operatorNormValues_bddAbove (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (sym : Bool) :
    BddAbove (operatorNormValues p h I sym) := by
  refine ⟨operatorGain p h I sym, ?_⟩
  intro v hv
  cases hv with
  | execution E H hH D delta hd hD hsym =>
    exact variation_operatorNorm_le_gain (p := p) (q := q) h I sym H hH D delta hd hD hsym

include q in
theorem operatorNormGain_eq (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (sym : Bool) :
    operatorNormGain p h I sym = operatorGain p h I sym := by
  have hne : (operatorNormValues p h I sym).Nonempty := by
    obtain ⟨_, hv⟩ := operatorValues_nonempty (p := p) (q := q) h I sym
    cases hv with
    | execution E H hH D delta hd hD hsym initial hi =>
      exact ⟨_, OperatorNormValue.execution E H hH D delta hd hD hsym⟩
  apply le_antisymm
  · apply csSup_le hne
    intro v hv
    cases hv with
    | execution E H hH D delta hd hD hsym =>
      exact variation_operatorNorm_le_gain (p := p) (q := q) h I sym H hH D delta hd hD hsym
  · apply csSup_le (operatorValues_nonempty (p := p) (q := q) h I sym)
    intro v hv
    cases hv with
    | execution E H hH D delta hd hD hsym initial hi =>
      have hb := (variationMap h H D).toContinuousLinearMap.le_opNorm initial
      have hh : ‖(variationMap h H D).toContinuousLinearMap‖ ≤ operatorNormGain p h I sym :=
        le_csSup (operatorNormValues_bddAbove (p := p) (q := q) h I sym)
          (OperatorNormValue.execution E H hH D delta hd hD hsym)
      change ‖variationMap h H D initial‖ ≤ _ at hb
      rw [variationMap_apply] at hb
      exact (hb.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hi (norm_nonneg _))).trans hh

end
end InexactRealizations.Budgets
