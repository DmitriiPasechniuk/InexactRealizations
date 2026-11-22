import InexactRealizations.Channel.Roots.Actual
import InexactRealizations.Probability.SignProducts

namespace InexactRealizations.Channel.Roots
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators Matrix
open InexactRealizations.Algorithms InexactRealizations.Comparisons.Competitors

/-- A genuinely time-varying commuting channel oracle in spectral coordinates. -/
def modeOracle {ι : Type*} {N : ℕ} (eig : ι → ℝ) (δ : ℝ) (ξ : Fin N → ℝ) :
    Fin N → (ι → ℝ) → (ι → ℝ) := fun s y j => (eig j+δ*ξ s)*y j

end
end InexactRealizations.Channel.Roots
