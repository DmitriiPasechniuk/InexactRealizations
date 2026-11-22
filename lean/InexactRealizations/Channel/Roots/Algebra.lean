import InexactRealizations.Channel.Roots.Factors
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import InexactRealizations.Lower.EndpointGain
import InexactRealizations.Operators.Chebyshev.EndpointDerivatives
import InexactRealizations.Operators.Stepsize.Basic

namespace InexactRealizations.Channel.Roots
noncomputable section
open Polynomial
open scoped BigOperators

/-- Natural-index extension of an arbitrary finite root-step schedule. -/
def extend {N : ℕ} (α : Fin N → ℝ) (j : ℕ) : ℝ := if hj : j<N then α ⟨j,hj⟩ else 0

/-- Extension preserves every actual finite call coefficient. -/
@[simp] theorem extend_fin {N : ℕ} (α : Fin N → ℝ) (j : Fin N) : extend α j.val=α j := by
  simp [extend,j.isLt]

/-- The ordinary root-step polynomial is its literal finite affine product. -/
theorem polynomial_eq_prod (γ : ℕ → ℝ) (N : ℕ) :
    InexactRealizations.Operators.Stepsize.polynomial γ N=∏ j ∈ Finset.range N, (1-C (γ j)*X) := by
  induction N with
  | zero => simp [InexactRealizations.Operators.Stepsize.polynomial]
  | succ N ih => rw [InexactRealizations.Operators.Stepsize.polynomial,Finset.prod_range_succ,ih]; ring

/-- Finite natural extension gives precisely the terminal product of the actual steps. -/
theorem polynomial_extend {N : ℕ} (α : Fin N → ℝ) :
    InexactRealizations.Operators.Stepsize.polynomial (extend α) N=terminal α := by
  rw [polynomial_eq_prod,Finset.prod_range]
  simp only [extend_fin,terminal]

end
end InexactRealizations.Channel.Roots
