import InexactRealizations.Operators.TwoTerm.Basic

/-! A block polynomial expressed in the physical spectral variable lambda.
Use: `InexactRealizations.Operators.JacobiData.residual_eval` feeds `InexactRealizations.Operators.JacobiData.scalar_exact` (The
scalar form, including the initial prefix).
Proof chain: `InexactRealizations.Operators.JacobiData.kernel_eq` — chebyshev1,; Block determinants,
first-variation kernel and gain.
-/
namespace InexactRealizations.Operators
noncomputable section
open Polynomial
open scoped Polynomial

/-- Jacobi recurrence data. `aSq s` is the squared coupling between sites s-1 and s. -/
structure JacobiData where
  /-- Diagonal Jacobi coefficients. -/
  b : ℕ → ℝ
  /-- Coefficients representing squared off-diagonal couplings. Determinant recursions use these values algebraically; admissibility imposes nonnegativity. -/
  aSq : ℕ → ℝ

namespace JacobiData

/-- Monic continuants of a contiguous block, with its start and length explicit. -/
def block (J : JacobiData) (a : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X - C (J.b a)
  | n + 2 => (X - C (J.b (a + n + 1))) * J.block a (n + 1) -
      C (J.aSq (a + n + 1)) * J.block a n

/-- Defines `leading` of type `ℝ[X]` by `J.block 0 n`. -/
def leading (J : JacobiData) (n : ℕ) : ℝ[X] := J.block 0 n
/-- Defines `den` of type `ℝ` by `(J.leading n).eval I.eta`. -/
def den (J : JacobiData) (I : SpectralInterval) (n : ℕ) : ℝ := (J.leading n).eval I.eta
/-- Defines `Admissible` of type `Prop` by `∀ n ≤ N, 0 < J.den I n`. -/
def Admissible (J : JacobiData) (I : SpectralInterval) (N : ℕ) : Prop :=
  ∀ n ≤ N, 0 < J.den I n

/-- Defines `residual` of type `ℝ[X]` by `C (J.den I n)⁻¹ * (J.leading n).comp (C I.eta - C (2 /
I.delta) * X)`.
-/
def residual (J : JacobiData) (I : SpectralInterval) (n : ℕ) : ℝ[X] :=
  C (J.den I n)⁻¹ * (J.leading n).comp (C I.eta - C (2 / I.delta) * X)

/-- Constructs `method` of type `TwoTerm` by the displayed record fields. Data fields specify the
construction; proof fields discharge its required properties.
-/
def method (J : JacobiData) (I : SpectralInterval) : TwoTerm where
  a := fun t => J.den I t / J.den I (t + 1) * (I.eta - J.b t)
  b := fun t => -(J.aSq t * J.den I (t - 1) / J.den I (t + 1))
  gamma := fun t => (2 / I.delta) * J.den I t / J.den I (t + 1)

/-- Defines `realization` of type `Realization (Fin 2)` by `(J.method I).realization`. -/
def realization (J : JacobiData) (I : SpectralInterval) : Realization (Fin 2) :=
  (J.method I).realization

/-- Exact identity `J.leading 0 = 1`. -/
@[simp] theorem leading_zero (J : JacobiData) : J.leading 0 = 1 := rfl
/-- Exact identity `J.leading 1 = X - C (J.b 0)`. -/
@[simp] theorem leading_one (J : JacobiData) : J.leading 1 = X - C (J.b 0) := rfl
/-- Exact identity `J.den I 0 = 1`. -/
@[simp] theorem den_zero (J : JacobiData) (I : SpectralInterval) : J.den I 0 = 1 := by simp [den]
/-- Exact identity `J.den I 1 = I.eta - J.b 0`. -/
@[simp] theorem den_one (J : JacobiData) (I : SpectralInterval) : J.den I 1 = I.eta - J.b 0 := by simp [den]

/-- Exact identity `J.den I (n + 2) = (I.eta - J.b (n + 1)) * J.den I (n + 1) - J.aSq (n + 1) *
J.den I n`.
-/
theorem den_add_two (J : JacobiData) (I : SpectralInterval) (n : ℕ) :
    J.den I (n + 2) = (I.eta - J.b (n + 1)) * J.den I (n + 1) -
      J.aSq (n + 1) * J.den I n := by simp [den, leading, block]

/-- Exact identity `(J.method I).a (n + 1) + (J.method I).b (n + 1) = 1`. -/
theorem fixed_point (J : JacobiData) (I : SpectralInterval) (n : ℕ)
    (hne : J.den I (n + 2) ≠ 0) :
    (J.method I).a (n + 1) + (J.method I).b (n + 1) = 1 := by
  dsimp [method]
  field_simp [hne]
  nlinarith [J.den_add_two I n]

/-- Exact identity `(J.residual I n).eval lam = (J.leading n).eval (I.z lam) / J.den I n`. -/
theorem residual_eval (J : JacobiData) (I : SpectralInterval) (n : ℕ) (lam : ℝ) :
    (J.residual I n).eval lam = (J.leading n).eval (I.z lam) / J.den I n := by simp [residual, I.z_eq, div_eq_mul_inv, mul_comm]

end JacobiData
end
end InexactRealizations.Operators
