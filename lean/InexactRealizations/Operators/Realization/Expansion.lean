import InexactRealizations.Operators.Realization.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import InexactRealizations.Operators.Algebra.OrderedProduct
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! the insertion sum is the actual derivative at zero drift.
Use: `InexactRealizations.Operators.Realization.hasDerivAt_operatorTransfer` feeds
`InexactRealizations.Operators.Realization.kernel_sum_derivative` (The sum of all insertion kernels is the
derivative under a static spectral shift).
Proof chain: `InexactRealizations.Operators.Realization.static_shift_lower_bounds_general` — chebyshev1, Theorem
4.3; All insertion orders, partition bounds, finite/cosh bounds and attainment.
-/
namespace InexactRealizations.Operators.Realization

open scoped BigOperators Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- The term linear in all Hessian perturbations, with sign convention. -/
def linearResponse (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (E : ℕ → Matrix d d ℝ) : Matrix d d ℝ :=
  R.contract (firstVariation (fun s => R.operatorStep s H)
    (fun s => R.operatorInsertion s (E s)) n)

/-- The first variation is the sum of causally ordered single insertions.

Exact identity `R.linearResponse n H E = ∑ s ∈ Finset.range n, R.contract (orderedProduct (fun
i => R.operatorStep (s + 1 + i) H) (n - (s + 1)) * R.operatorInsertion s (E s) * orderedProduct
(fun i => R.operatorStep i H) s)`.
-/
theorem linearResponse_eq_sum (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (E : ℕ → Matrix d d ℝ) :
    R.linearResponse n H E = ∑ s ∈ Finset.range n,
      R.contract (orderedProduct (fun i => R.operatorStep (s + 1 + i) H) (n - (s + 1)) *
        R.operatorInsertion s (E s) * orderedProduct (fun i => R.operatorStep i H) s) := by
  unfold linearResponse
  change R.contractLinear _ = _
  rw [firstVariation_eq_sum, map_sum]
  rfl

end
end InexactRealizations.Operators.Realization
