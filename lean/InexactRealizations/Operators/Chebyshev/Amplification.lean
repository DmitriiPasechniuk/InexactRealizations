import InexactRealizations.Operators.Chebyshev.Normalization
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Exact finite amplification, with no large-condition-number approximation.
Use: `InexactRealizations.Operators.SpectralInterval.amplification_accelerated_le` feeds
`InexactRealizations.Operators.SpectralInterval.amplification_effectiveKappa_le` (amplification effective Kappa
le).
Proof chain: `InexactRealizations.Operators.SpectralInterval.amplification_effectiveKappa_le` — chebyshev1,
5; Exact drift scale, accuracy asymptotics and rational finite examples.
-/
namespace InexactRealizations.Operators
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- The identity behind the exact amplification formula.

Exact identity `Real.cosh (2 * Real.arsinh (Real.sqrt u)) = 1 + 2*u`.
-/
theorem cosh_two_arsinh_sqrt (u : ℝ) (hu : 0 ≤ u) :
    Real.cosh (2 * Real.arsinh (Real.sqrt u)) = 1 + 2*u := by
  rw [two_mul, Real.cosh_add, Real.cosh_arsinh, Real.sinh_arsinh]
  nlinarith [Real.sq_sqrt hu,
    Real.sq_sqrt (show 0 ≤ 1 + Real.sqrt u ^ 2 by positivity)]

/-- Exact identity `(T ℝ N).eval (1 + 2*u) = Real.cosh (2*(N:ℝ)*Real.arsinh (Real.sqrt u))`. -/
theorem chebyshev_arsinh (N : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (T ℝ N).eval (1 + 2*u) = Real.cosh (2*(N:ℝ)*Real.arsinh (Real.sqrt u)) := by
  rw [← cosh_two_arsinh_sqrt u hu, T_real_cosh]
  congr 1
  push_cast
  ring

namespace SpectralInterval

/-- Exact identity `I.eta = 1 + 2*I.mu/I.delta`. -/
theorem eta_eq_one_add (I : SpectralInterval) : I.eta = 1 + 2*I.mu/I.delta := by
  dsimp [eta, delta]
  field_simp [ne_of_gt (sub_pos.mpr I.mu_lt_L)]
  ring

/-- Defines `kappa` of type `ℝ` by `I.L/I.mu`. -/
def kappa (I : SpectralInterval) : ℝ := I.L/I.mu

/-- Exact identity `(I.residual N).eval 0 = 1`. -/
@[simp] theorem residual_eval_zero (I : SpectralInterval) (N : ℕ) :
    (I.residual N).eval 0 = 1 := by
  have hz : I.z 0 = I.eta := by simp [z, eta]
  rw [I.residual_eval, hz]
  exact div_self (I.den_ne N)

end SpectralInterval
end
end InexactRealizations.Operators
