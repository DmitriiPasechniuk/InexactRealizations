import InexactRealizations.Probability.GaussianAdapted
import InexactRealizations.Risk.AllLinearOptima

/-! Actual risks for arbitrary measurable adaptive methods. The scalar
comparison class is a subclass of dimension-uniform class,
so a lower bound here already excludes any improvement in that class.
Coordinates are relative to the fixed initial point; the method itself
has arbitrary measurable queries and output, with no linearity constraint. 
-/
namespace InexactRealizations.Risk.Adaptive
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
variable {N : ℕ} {U : Type} [MeasurableSpace U]
open InexactRealizations.Probability

def actualQuery (M : AdaptiveMethod N ℝ U) {Ω : Type} (seed : Ω → U)
    (target : Ω → ℝ) (mu : ℝ) (w : ℕ → Ω → ℝ) (s : Fin N) (ξ : Ω) : ℝ :=
  M.query s (seed ξ, fun j ↦ M.answersThrough (fun i q ↦ mu * (q - target ξ) + w i.val ξ)
    (seed ξ) s.val ⟨j.val, j.isLt.trans s.isLt⟩)

def actualOutput (M : AdaptiveMethod N ℝ U) {Ω : Type} (seed : Ω → U)
    (target : Ω → ℝ) (mu : ℝ) (w : ℕ → Ω → ℝ) (ξ : Ω) : ℝ :=
  M.oracleOutput (fun i q ↦ mu * (q - target ξ) + w i.val ξ) (seed ξ)

inductive ScalarMseValue (M : AdaptiveMethod N ℝ U) (P : Measure U)
    (I : InexactRealizations.Operators.SpectralInterval) (r sigma : ℝ) : ℝ≥0∞ → Prop where
  | model (Ω : Type) [mΩ : MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
      (𝓕 : Filtration ℕ mΩ) (seed : Ω → U)
      (hseed : @Measurable Ω U (𝓕 0) inferInstance seed)
      (hseedlaw : Q.map seed = P) (target : Ω → ℝ) (hindep : IndepFun seed target Q)
      (htarget : StronglyMeasurable[𝓕 0] target)
      (htarget₂ : MemLp target 2 Q) (hr : (∫ ξ, ‖target ξ‖ ^ 2 ∂Q) ≤ r ^ 2)
      (mu : ℝ) (hmu : mu ∈ Icc I.mu I.L) (w : ℕ → Ω → ℝ)
      (hw : MartingaleDifferences N 𝓕 w Q)
      (hvariance : ∀ s, s < N → Q[fun ξ ↦ ‖w s ξ‖ ^ 2 | 𝓕 s] ≤ᵐ[Q] fun _ ↦ sigma ^ 2)
      (hquery : ∀ s, StronglyMeasurable[𝓕 s.val] (actualQuery M seed target mu w s)) :
      ScalarMseValue M P I r sigma
        (∫⁻ ξ, ENNReal.ofReal ((target ξ - actualOutput M seed target mu w ξ) ^ 2) ∂Q)

def scalarMseRisk (M : AdaptiveMethod N ℝ U) (P : Measure U)
    (I : InexactRealizations.Operators.SpectralInterval) (r sigma : ℝ) : ℝ≥0∞ :=
  sSup {v | ScalarMseValue M P I r sigma v}

end
end InexactRealizations.Risk.Adaptive
