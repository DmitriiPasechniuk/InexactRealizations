import InexactRealizations.Risk.AdaptiveGaussian
import InexactRealizations.Probability.AdaptiveTranslation

/-! Dimension-uniform worst-case MSE for arbitrary adaptive methods.
Coordinates are relative to the fixed initial point, as in the history
risk definitions; `estimation_error_recenter` gives the exact dictionary
for an arbitrary absolute initial point. The one-dimensional Gaussian
instance is an actual member of this full comparison class. 
-/
namespace InexactRealizations.Risk.Adaptive
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open InexactRealizations.Probability
variable {N : ℕ} {U : Type} [MeasurableSpace U]

abbrev Family (N : ℕ) (U : Type) [MeasurableSpace U] :=
  (E : Type) → [NormedAddCommGroup E] → [InnerProductSpace ℝ E] → [CompleteSpace E] →
    [FiniteDimensional ℝ E] → [MeasurableSpace E] → [BorelSpace E] → AdaptiveMethod N E U

def vectorQuery {E Ω : Type} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E]
    (M : AdaptiveMethod N E U) (seed : Ω → U) (target : Ω → E)
    (H : E →ₗ[ℝ] E) (w : ℕ → Ω → E) (s : Fin N) (ξ : Ω) : E :=
  M.query s (seed ξ, fun j ↦ M.answersThrough (fun i q ↦ H (q - target ξ) + w i.val ξ)
    (seed ξ) s.val ⟨j.val, j.isLt.trans s.isLt⟩)

def vectorOutput {E Ω : Type} [AddCommGroup E] [Module ℝ E] [MeasurableSpace E]
    (M : AdaptiveMethod N E U) (seed : Ω → U) (target : Ω → E)
    (H : E →ₗ[ℝ] E) (w : ℕ → Ω → E) (ξ : Ω) : E :=
  M.oracleOutput (fun i q ↦ H (q - target ξ) + w i.val ξ) (seed ξ)

inductive MseValue (M : Family N U) (P : Measure U)
    (I : InexactRealizations.Operators.SpectralInterval) (r sigma : ℝ) : ℝ≥0∞ → Prop where
  | model (E Ω : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
      [mΩ : MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
      (𝓕 : Filtration ℕ mΩ) (seed : Ω → U)
      (hseed : @Measurable Ω U (𝓕 0) inferInstance seed) (hseedlaw : Q.map seed = P)
      (target : Ω → E) (hindep : IndepFun seed target Q)
      (htarget : StronglyMeasurable[𝓕 0] target) (htarget₂ : MemLp target 2 Q)
      (hr : (∫ ξ, ‖target ξ‖ ^ 2 ∂Q) ≤ r ^ 2)
      (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (w : ℕ → Ω → E)
      (hw : MartingaleDifferences N 𝓕 w Q)
      (hvariance : ∀ s, s < N → Q[fun ξ ↦ ‖w s ξ‖ ^ 2 | 𝓕 s] ≤ᵐ[Q] fun _ ↦ sigma ^ 2)
      (hquery : ∀ s, StronglyMeasurable[𝓕 s.val] (vectorQuery (M E) seed target H w s)) :
      MseValue M P I r sigma
        (∫⁻ ξ, ENNReal.ofReal (‖target ξ - vectorOutput (M E) seed target H w ξ‖ ^ 2) ∂Q)

def mseRisk (M : Family N U) (P : Measure U) (I : InexactRealizations.Operators.SpectralInterval) (r sigma : ℝ) : ℝ≥0∞ :=
  sSup {v | MseValue M P I r sigma v}

theorem scalarValue_is_uniformValue (M : Family N U) (P : Measure U)
    (I : InexactRealizations.Operators.SpectralInterval) {r sigma : ℝ} {v : ℝ≥0∞}
    (hv : ScalarMseValue (M ℝ) P I r sigma v) : MseValue M P I r sigma v := by
  cases hv with
  | model Ω Q 𝓕 seed hseed hseedlaw target hindep htarget htarget₂ hr mu hmu w hw hvariance hquery =>
    have ho : vectorOutput (M ℝ) seed target (InexactRealizations.History.scalarOperator mu) w =
        actualOutput (M ℝ) seed target mu w := rfl
    have he : (∫⁻ ξ, ENNReal.ofReal (‖target ξ - vectorOutput (M ℝ) seed target
        (InexactRealizations.History.scalarOperator mu) w ξ‖ ^ 2) ∂Q) =
        (∫⁻ ξ, ENNReal.ofReal ((target ξ - actualOutput (M ℝ) seed target mu w ξ) ^ 2) ∂Q) := by
      apply lintegral_congr
      intro ξ
      rw [ho, Real.norm_eq_abs, sq_abs]
    rw [← he]
    exact MseValue.model ℝ Ω Q 𝓕 seed hseed hseedlaw target hindep htarget htarget₂ hr
      (InexactRealizations.History.scalarOperator mu) (InexactRealizations.Analysis.scalar_admissible I mu hmu)
      w hw hvariance hquery

theorem scalarRisk_le_uniformRisk (M : Family N U) (P : Measure U)
    (I : InexactRealizations.Operators.SpectralInterval) (r sigma : ℝ) :
    scalarMseRisk (M ℝ) P I r sigma ≤ mseRisk M P I r sigma := by
  apply sSup_le
  intro v hv
  exact le_sSup (scalarValue_is_uniformValue M P I hv)

theorem no_uniform_adaptive_improvement (M : Family N U) (P : Measure U) [IsProbabilityMeasure P]
    (I : InexactRealizations.Operators.SpectralInterval) (hN : 0 < N) (r sigma : ℝ)
    (hdom : I.epsilon N * r ^ 2 < (sigma ^ 2 / (I.mu ^ 2 * N)) * (1 - I.epsilon N)) :
    ENNReal.ofReal (AllLinear.allLinearValue I N r sigma) ≤ mseRisk M P I r sigma :=
  (no_adaptive_improvement (M ℝ) P I hN r sigma hdom).trans (scalarRisk_le_uniformRisk M P I r sigma)

end
end InexactRealizations.Risk.Adaptive
