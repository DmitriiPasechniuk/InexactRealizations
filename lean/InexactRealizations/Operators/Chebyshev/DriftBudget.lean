import InexactRealizations.Operators.Chebyshev.Amplification
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Algebra.Order.Floor.Semiring

/-! Exact finite drift budgets and the least integer accuracy horizon. -/
namespace InexactRealizations.Operators.SpectralInterval
noncomputable section
open Polynomial Polynomial.Chebyshev Real

/-- The inverse-hyperbolic expression for the spectral normalization. -/
theorem arcosh_eta (I : SpectralInterval) :
    arcosh I.eta = 2 * arsinh (sqrt (I.mu / I.delta)) := by
  have hu : 0 ≤ I.mu / I.delta := div_nonneg I.mu_pos.le I.delta_pos.le
  rw [I.eta_eq_one_add, show 1 + 2 * I.mu / I.delta = 1 + 2 * (I.mu / I.delta) by ring,
    ← InexactRealizations.Operators.cosh_two_arsinh_sqrt _ hu]
  exact arcosh_cosh (mul_nonneg (by norm_num) (arsinh_nonneg_iff.mpr (sqrt_nonneg _)))

theorem den_cosh_arcosh (I : SpectralInterval) (N : ℕ) :
    I.den N = cosh ((N : ℝ) * arcosh I.eta) := by
  rw [I.arcosh_eta]
  change (T ℝ N).eval I.eta = _
  rw [I.eta_eq_one_add, show 1 + 2 * I.mu / I.delta = 1 + 2 * (I.mu / I.delta) by ring,
    chebyshev_arsinh N _ (div_nonneg I.mu_pos.le I.delta_pos.le)]
  congr 1
  ring

end
end InexactRealizations.Operators.SpectralInterval
