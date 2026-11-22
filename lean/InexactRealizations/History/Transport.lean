import InexactRealizations.History.Oracle
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace InexactRealizations.History
noncomputable section
open scoped BigOperators
section Algebra
variable {N : ℕ} {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Every actual causal oracle execution respects an intertwining linear embedding. -/
theorem oracleAnswers_map (h : InexactRealizations.History N) (J : E →ₗ[ℝ] F)
    (initial : E) (oracle : Fin N → E → E) (ambient : Fin N → F → F)
    (hi : ∀ s x, ambient s (J x)=J (oracle s x)) :
    h.oracleAnswers (J initial) ambient=fun s => J (h.oracleAnswers initial oracle s) := by
  symm
  apply h.oracleAnswers_unique
  intro s
  rw [h.oracleAnswers_eq]
  have he : J initial-∑ j,h.a s j • J (h.oracleAnswers initial oracle j)=
      J (h.oracleQuery initial oracle s) := by
    simp only [oracleQuery, map_sub, map_sum, map_smul]
  rw [he, hi]

/-- The full finite perturbed output, not only its derivative, respects active coordinates. -/
theorem oracleOutput_map (h : InexactRealizations.History N) (J : E →ₗ[ℝ] F)
    (initial : E) (oracle : Fin N → E → E) (ambient : Fin N → F → F)
    (hi : ∀ s x, ambient s (J x)=J (oracle s x)) :
    h.oracleOutput (J initial) ambient=J (h.oracleOutput initial oracle) := by
  simp only [oracleOutput, h.oracleAnswers_map J initial oracle ambient hi,
    map_sub, map_sum, map_smul]
end Algebra

end
end InexactRealizations.History
