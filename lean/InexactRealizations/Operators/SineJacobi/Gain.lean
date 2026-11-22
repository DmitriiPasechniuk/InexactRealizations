import InexactRealizations.Operators.SineJacobi.Reversal
import InexactRealizations.Operators.Chebyshev.Normalization
import InexactRealizations.Operators.Jacobi.Kernel
import InexactRealizations.Operators.Realization.GainBounds
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import InexactRealizations.Operators.Chebyshev.EndpointDerivatives
import InexactRealizations.Operators.Realization.Expansion
import InexactRealizations.Operators.Spectral.DiagonalResponse
import InexactRealizations.Operators.Spectral.OperatorNorm

/-! The exact finite gain, in endpoint-product coordinates.
Use: `InexactRealizations.Operators.SineJacobi.gain_exact` feeds `InexactRealizations.Operators.SineJacobi.gain_asymptotic_ratio`
(: the ratio to the stated N^(3/2) leading term tends to one).
-/
namespace InexactRealizations.Operators.SineJacobi
noncomputable section
open Polynomial Real
open scoped BigOperators
variable (I : SpectralInterval)

/-- Exact identity `((data N).realization I).residualPolynomial N = I.residual N`. -/
theorem residualPolynomial (N : ℕ) (hN : 0 < N) :
    ((data N).realization I).residualPolynomial N = I.residual N := by
  rw [JacobiData.residualPolynomial_eq _ I (admissible I N hN) N le_rfl]
  exact (data N).terminal_residual I (by positivity) (terminal N hN)

end
end InexactRealizations.Operators.SineJacobi
