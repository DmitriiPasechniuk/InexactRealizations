import InexactRealizations.Channel.Roots.FiniteProduct
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace InexactRealizations.Channel.Roots
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators

section Transport
variable {N : ℕ} {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- Conjugate every actual time-dependent oracle by an exact linear coordinate change. -/
def conjugateOracle (e : E ≃ₗ[ℝ] F) (oracle : Fin N → E → E) : Fin N → F → F :=
  fun s y => e (oracle s (e.symm y))

end Transport

/-- The literal commuting-channel oracle acting on the finite Euclidean Hilbert space. -/
def euclideanOracle {ι : Type*} {N : ℕ} (eig : ι → ℝ) (δ : ℝ) (ξ : Fin N → ℝ) :
    Fin N → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
  conjugateOracle (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm (modeOracle eig δ ξ)

end
end InexactRealizations.Channel.Roots
