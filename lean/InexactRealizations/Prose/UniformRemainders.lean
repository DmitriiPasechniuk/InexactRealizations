import InexactRealizations.Centered.Journal
import InexactRealizations.Budgets.Interpolation

/-! The remainder constants and the centered proof can be
chosen from the history, L and t0 alone, before the lower endpoint, dimension,
Hessian, initial point and adaptive errors are chosen. 
-/
namespace InexactRealizations.Prose
noncomputable section
open MeasureTheory Polynomial InexactRealizations.Analysis InexactRealizations.Budgets InexactRealizations.Centered
open scoped BigOperators ENNReal NNReal
variable {N : ℕ}

def uniformPolynomialBound (p : ℝ[X]) (L : ℝ) : ℝ :=
  max 0 (sSup ((fun x : ℝ ↦ |p.eval x|) '' Set.Icc (-|L|) |L|))

theorem uniformPolynomialBound_nonneg (p : ℝ[X]) (L : ℝ) : 0 ≤ uniformPolynomialBound p L := le_max_left _ _

theorem uniformPolynomialBound_eval (p : ℝ[X]) (L x : ℝ) (hx : |x| ≤ |L|) :
    |p.eval x| ≤ uniformPolynomialBound p L := by
  have hb := le_csSup (isCompact_Icc.image p.continuous.abs).bddAbove
    (show |p.eval x| ∈ (fun y : ℝ ↦ |p.eval y|) '' Set.Icc (-|L|) |L| from ⟨x, abs_le.mp hx, rfl⟩)
  exact hb.trans (le_max_right _ _)

def uniformResponses (h : InexactRealizations.History N) (L : ℝ) (s : Fin N) : ℝ := uniformPolynomialBound (h.response s) L

theorem uniformResponses_bounds (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) :
    InexactRealizations.Risk.ResponseBounds h I (uniformResponses h I.L) := by
  refine ⟨fun s ↦ uniformPolynomialBound_nonneg _ _, fun s x hx ↦ ?_⟩
  apply uniformPolynomialBound_eval
  rw [abs_of_pos (I.mu_pos.trans I.mu_lt_L), abs_of_nonneg (I.mu_pos.le.trans hx.1)]
  exact hx.2

def uniformRelativeRemainder (h : InexactRealizations.History N) (L t0 : ℝ) : ℝ :=
  ∑ s, uniformResponses h L s * deviationMajorant h L t0 s

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem relative_linearization_uniform {p q : ℝ≥0∞} [p.HolderConjugate q]
    (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (H : E →ₗ[ℝ] E) (hH : Admissible I H)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise)
    (t t0 : ℝ) (ht : 0 < t) (htt0 : t ≤ t0) (hi : ‖initial‖ ≤ 1) (delta : Fin N → ℝ)
    (hw : InexactRealizations.Budgets.RelativeErrors p h H initial noise u t delta) :
    ∃ D : Fin N → E →ₗ[ℝ] E, (∀ s, ‖(D s).toContinuousLinearMap‖ ≤ delta s) ∧
      ‖(u.output - (aeval H h.terminal) initial) - t • h.firstVariation H D initial‖ ≤
        t ^ 2 * uniformRelativeRemainder h I.L t0 := by
  exact relative_linearization (p := p) (q := q) h I H hH initial noise u t t0 ht htt0 hi delta hw
    (uniformResponses h I.L) (uniformResponses_bounds h I)

variable [CompleteSpace E] {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ] {𝓕 : MeasureTheory.Filtration ℕ mΩ} {w : ℕ → Ω → E}

end
end InexactRealizations.Prose
