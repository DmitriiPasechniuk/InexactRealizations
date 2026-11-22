import InexactRealizations.Operators.SineJacobi.RogersPolynomial

/-! E.2's finite Fourier identity is derived from the explicit sine recurrence.
Use: `InexactRealizations.Operators.SineJacobi.leading_fourier` feeds
`InexactRealizations.Operators.SineJacobi.normalized_fourier` (The endpoint-normalized nonnegative cosine expansion
in E.2).
Proof chain: `InexactRealizations.Operators.SineJacobi.endpoint_global_bound` — chebyshev1,;
Hard-edge recurrence, singular ODE, uniqueness and endpoint limits.
-/
namespace InexactRealizations.Operators.SineJacobi
noncomputable section
open Polynomial Real
open scoped BigOperators

/-- Defines `cosineTransform` of type `ℝ[X] →ₗ[ℝ] ℝ` by `Polynomial.lsum (fun k => { toFun := fun a
=> a*cos (((n:ℝ)-2*(k:ℝ))*theta) map_add' := fun _ _ => by ring map_smul' := fun _ _ => by simp
[mul_assoc] })`.
-/
def cosineTransform (n : ℤ) (theta : ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun k =>
    { toFun := fun a => a*cos (((n:ℝ)-2*(k:ℝ))*theta)
      map_add' := fun _ _ => by ring
      map_smul' := fun _ _ => by simp [mul_assoc] })

/-- Exact identity `cosineTransform n theta (monomial k a) = a*cos (((n:ℝ)-2*(k:ℝ))*theta)`. -/
@[simp] theorem cosineTransform_monomial (n : ℤ) (theta a : ℝ) (k : ℕ) :
    cosineTransform n theta (monomial k a) = a*cos (((n:ℝ)-2*(k:ℝ))*theta) := by simp [cosineTransform, lsum_apply, sum_monomial_index]

/-- Exact identity `cosineTransform n theta (C a) = a*cos ((n:ℝ)*theta)`. -/
@[simp] theorem cosineTransform_C (n : ℤ) (theta a : ℝ) :
    cosineTransform n theta (C a) = a*cos ((n:ℝ)*theta) := by
  rw [← monomial_zero_left, cosineTransform_monomial]
  simp

/-- Exact identity `cosineTransform n theta 1 = cos ((n:ℝ)*theta)`. -/
@[simp] theorem cosineTransform_one (n : ℤ) (theta : ℝ) :
    cosineTransform n theta 1 = cos ((n:ℝ)*theta) := by
  change cosineTransform n theta (C 1) = _
  rw [cosineTransform_C]
  simp

/-- Exact identity `cosineTransform n theta X = cos (((n:ℝ)-2)*theta)`. -/
@[simp] theorem cosineTransform_X (n : ℤ) (theta : ℝ) :
    cosineTransform n theta X = cos (((n:ℝ)-2)*theta) := by
  change cosineTransform n theta (monomial 1 1) = _
  simp

/-- Exact identity `cosineTransform n theta (X*p) = cosineTransform (n-2) theta p`. -/
theorem cosineTransform_X_mul (n : ℤ) (theta : ℝ) (p : ℝ[X]) :
    cosineTransform n theta (X*p) = cosineTransform (n-2) theta p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]
  | monomial k a =>
    rw [X_mul_monomial, cosineTransform_monomial, cosineTransform_monomial]
    congr 2
    push_cast
    ring

/-- Exact identity `cosineTransform (n+1) theta p + cosineTransform (n-1) theta p = 2*cos
theta*cosineTransform n theta p`.
-/
theorem cosineTransform_modes (n : ℤ) (theta : ℝ) (p : ℝ[X]) :
    cosineTransform (n+1) theta p + cosineTransform (n-1) theta p =
      2*cos theta*cosineTransform n theta p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add]; rw [mul_add]; linarith
  | monomial k a =>
    simp only [cosineTransform_monomial, Int.cast_add, Int.cast_sub, Int.cast_one]
    rw [show ((n:ℝ)+1-2*(k:ℝ))*theta = ((n:ℝ)-2*(k:ℝ))*theta+theta by ring,
      show ((n:ℝ)-1-2*(k:ℝ))*theta = ((n:ℝ)-2*(k:ℝ))*theta-theta by ring,
      cos_add, cos_sub]
    ring

/-- Exact identity `cosineTransform (n+1) theta ((1+X)*p-C c*X*q) = 2*cos theta*cosineTransform n
theta p-c*cosineTransform (n-1) theta q`.
-/
theorem cosineTransform_recurrence (n : ℤ) (theta c : ℝ) (p q : ℝ[X]) :
    cosineTransform (n+1) theta ((1+X)*p-C c*X*q) =
      2*cos theta*cosineTransform n theta p-c*cosineTransform (n-1) theta q := by
  rw [add_mul, one_mul, mul_assoc, ← smul_eq_C_mul, map_sub, map_add, map_smul,
    cosineTransform_X_mul, cosineTransform_X_mul]
  rw [show n+1-2 = n-1 by omega, cosineTransform_modes]
  rfl

/-- E.2's finite Fourier identity is derived from the explicit sine recurrence.

Exact identity `(2:ℝ)^s*((data N).leading s).eval (cos theta) = cosineTransform (s:ℤ) theta
(rogers N s)`.
-/
theorem leading_cosineTransform (N s : ℕ) (hs : s < N) (theta : ℝ) :
    (2:ℝ)^s*((data N).leading s).eval (cos theta) = cosineTransform (s:ℤ) theta (rogers N s) := by
  induction s using Nat.twoStepInduction with
  | zero => simp [JacobiData.leading, JacobiData.block, rogers_zero N (by omega)]
  | one =>
    simp only [JacobiData.leading_one, data_b, C_0, sub_zero, eval_X, pow_one,
      rogers_one N hs, map_add, cosineTransform_one, cosineTransform_X]
    norm_num
    ring
  | more s ih0 ih1 =>
    have hs0 : s < N := by omega
    have hs1 : s+1 < N := by omega
    rw [show s+2 = (s+1)+1 by omega, rogers_recurrence N (s+1) hs (by omega)]
    rw [show ((s+1+1:ℕ):ℤ) = ((s+1:ℕ):ℤ)+1 by omega, cosineTransform_recurrence]
    rw [← ih1 hs1, show ((s+1:ℕ):ℤ)-1 = (s:ℤ) by omega, Nat.add_sub_cancel, ← ih0 hs0]
    have hr : (data N).leading (s+2) = X*(data N).leading (s+1) -
        C (couplingSq N (s+1))*(data N).leading s := by
      simp only [JacobiData.leading, JacobiData.block, data_b, C_0, sub_zero, Nat.zero_add]
      rw [data_aSq N (s+1) (by omega) hs1]
    rw [show s+1+1 = s+2 by omega, hr]
    simp only [eval_sub, eval_mul, eval_X, eval_C, pow_succ]
    ring

/-- Exact identity `(2:ℝ)^s*((data N).leading s).eval (cos theta) = ∑ k ∈ Finset.range (s+1),
coefficient N s k*cos (((s:ℝ)-2*(k:ℝ))*theta)`.
-/
theorem leading_fourier (N s : ℕ) (hs : s < N) (theta : ℝ) :
    (2:ℝ)^s*((data N).leading s).eval (cos theta) =
      ∑ k ∈ Finset.range (s+1), coefficient N s k*cos (((s:ℝ)-2*(k:ℝ))*theta) := by
  rw [leading_cosineTransform N s hs, rogers, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [C_mul_X_pow_eq_monomial, cosineTransform_monomial, Int.cast_natCast]

end
end InexactRealizations.Operators.SineJacobi
