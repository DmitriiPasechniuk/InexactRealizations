import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace InexactRealizations.Models.Ridge
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The orthogonal rank-one projection along the distinguished unit direction. -/
def projection (v : E) : E →L[ℝ] E := (innerSL ℝ v).smulRight v

/-- A two-eigenvalue operator, written in rank-one form. -/
def spectralMap (v : E) (a b : ℝ) : E →L[ℝ] E :=
  a • ContinuousLinearMap.id ℝ E+(b-a) • projection v

/-- Literal rank-one action of the two-eigenvalue operator. -/
theorem spectralMap_apply (v : E) (a b : ℝ) (x : E) :
    spectralMap v a b x=a • x+((b-a)*inner ℝ v x) • v := by
  simp only [spectralMap, projection, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]

end
end InexactRealizations.Models.Ridge
