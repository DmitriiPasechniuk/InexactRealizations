import InexactRealizations.Operators.Chebyshev.Normalization
import Mathlib.LinearAlgebra.Prod

namespace InexactRealizations.Models.Network
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The inter-network disagreement channel, in its literal two-block form. -/
def projector (x : E×E) : E×E := ((1/2:ℝ) • (x.1-x.2), (1/2:ℝ) • (x.2-x.1))

/-- Antisymmetric disagreement embedded into the two physical networks. -/
def antisymmetric (z : E) : E×E := (z,-z)

/-- The normalized Hessian of two corresponding-vertex coupled networks. -/
def hessian (Lc : E →ₗ[ℝ] E) (a : ℝ) (x : E×E) : E×E :=
  ((4+2*a)⁻¹ • (Lc x.1+a • (x.1-x.2)),
   (4+2*a)⁻¹ • (Lc x.2+a • (x.2-x.1)))

/-- The channel is an actual projection onto the antisymmetric subspace. -/
theorem projector_idempotent (x : E×E) : projector (projector x)=projector x := by
  ext <;> simp only [projector] <;> module

/-- The shared channel acts as the identity on all physical disagreement states. -/
theorem projector_antisymmetric (z : E) : projector (antisymmetric z)=antisymmetric z := by
  ext <;> simp only [projector, antisymmetric] <;> module

/-- Restriction of the physical Hessian is exactly (Lc+2aI)/(4+2a). -/
theorem hessian_antisymmetric (Lc : E →ₗ[ℝ] E) (a : ℝ) (z : E) :
    hessian Lc a (antisymmetric z)=
      antisymmetric ((4+2*a)⁻¹ • (Lc z+(2*a) • z)) := by
  ext <;> simp only [hessian, antisymmetric, map_neg] <;> module

/-- The coupling chosen in the article is strictly positive for every condition number above one. -/
theorem coupling_pos (κ : ℝ) (hκ : 1<κ) : 0<2/(κ-1) := div_pos (by norm_num) (by linarith)

/-- The active lower and upper cycle endpoints give exactly 1/kappa and one. -/
theorem active_endpoints (κ : ℝ) (hκ : 1<κ) :
    (0+2*(2/(κ-1)))/(4+2*(2/(κ-1)))=1/κ ∧
    (4+2*(2/(κ-1)))/(4+2*(2/(κ-1)))=1 := by
  have hk0 : κ≠0 := by linarith
  have hkm : κ-1≠0 := by linarith
  have hd : 4+2*(2/(κ-1))≠0 := ne_of_gt (by have := coupling_pos κ hκ; linarith)
  constructor
  · field_simp [hk0, hkm, hd]
    ring_nf
    exact mul_inv_cancel₀ hk0
  · exact div_self hd

end
end InexactRealizations.Models.Network
