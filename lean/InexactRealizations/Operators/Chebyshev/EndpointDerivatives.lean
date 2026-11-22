import InexactRealizations.Operators.Chebyshev.Polynomial

/-! Endpoint Derivatives.
Use: `InexactRealizations.Operators.SpectralInterval.residual_second_derivative_eval_mu` feeds
`InexactRealizations.Operators.Stepsize.endpoint_square_sum` (The endpoint energy is independent of the ordering of
an exact schedule).
Proof chain: `InexactRealizations.Operators.Stepsize.endpoint_square_sum` — chebyshev1,; Sharp
stepsize drift lower bound and asymptotics.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev endpoint derivatives.
The needed form is proved here.
-/
namespace InexactRealizations.Operators.SpectralInterval
noncomputable section
open Polynomial Polynomial.Chebyshev
variable (I : SpectralInterval)

/-- Exact identity `I.eta - (2 / I.delta) * I.mu = 1`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev endpoint
derivatives.
-/
private theorem affine_eval_mu :
    I.eta - (2 / I.delta) * I.mu = 1 := by rw [← I.z_eq, I.z_mu]

/-- Exact identity `(I.residual N).eval I.mu = I.epsilon N`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev endpoint
derivatives.
-/
theorem residual_eval_mu (N : ℕ) : (I.residual N).eval I.mu = I.epsilon N := by
  rw [I.residual_eval, I.z_mu, T_eval_one]
  rfl

/-- Exact identity `(I.residual N).derivative.eval I.mu = -(2 / I.delta) * I.epsilon N * (N : ℝ) ^
2`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev endpoint
derivatives.
-/
theorem residual_derivative_eval_mu (N : ℕ) :
    (I.residual N).derivative.eval I.mu = -(2 / I.delta) * I.epsilon N * (N : ℝ) ^ 2 := by
  simp [residual, derivative_comp, affine_eval_mu, derivative_T_eval_one,
    SpectralInterval.epsilon]
  ring

end
end InexactRealizations.Operators.SpectralInterval
