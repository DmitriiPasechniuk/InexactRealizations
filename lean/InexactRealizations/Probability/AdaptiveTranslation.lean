import InexactRealizations.Probability.AdaptiveOracle
import Mathlib.MeasureTheory.Group.Arithmetic

/-! Translating an arbitrary adaptive method to coordinates relative to
its fixed initial point changes no oracle answers or estimation error. 
-/
namespace InexactRealizations.Probability.AdaptiveMethod
noncomputable section
open MeasureTheory
variable {N : ℕ} {U : Type*} [MeasurableSpace U]

def recenter (M : AdaptiveMethod N ℝ U) (a : ℝ) : AdaptiveMethod N ℝ U where
  query s p := M.query s p - a
  query_measurable s := (M.query_measurable s).sub_const a
  output p := M.output p - a
  output_measurable := M.output_measurable.sub_const a

end
end InexactRealizations.Probability.AdaptiveMethod
