import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Tactic

/-! The second-kind bound follows from mathlib's endpoint bound for derivatives of T.
Use: `InexactRealizations.Operators.abs_U_eval_le` feeds `InexactRealizations.Operators.Prefix.kernel_abs_le_endpoint` (kernel abs
le endpoint).
Proof chain: `InexactRealizations.Operators.Prefix.gain_exact` — chebyshev1,; Exact prefix kernel,
gain and asymptotics.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval. The needed form is proved here.
-/
namespace InexactRealizations.Operators

noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped Polynomial

/-- The spectral interval , including its strict hypotheses.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
structure SpectralInterval where
  /-- Strictly positive lower spectral endpoint. -/
  mu : ℝ
  /-- Upper spectral endpoint; it is strictly larger than mu. -/
  L : ℝ
  /-- Positivity needed for the outside-spectrum Chebyshev normalization and denominators. -/
  mu_pos : 0 < mu
  /-- Nondegeneracy of the spectral interval, ensuring the affine spectral coordinate is defined. -/
  mu_lt_L : mu < L

namespace SpectralInterval

variable (I : SpectralInterval)

/-- Defines `delta` of type `ℝ` by `I.L - I.mu`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
def delta : ℝ := I.L - I.mu
/-- Defines `eta` of type `ℝ` by `(I.L + I.mu) / I.delta`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
def eta : ℝ := (I.L + I.mu) / I.delta
/-- Defines `z` of type `ℝ` by `(I.L + I.mu - 2 * lam) / I.delta`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
def z (lam : ℝ) : ℝ := (I.L + I.mu - 2 * lam) / I.delta
/-- Defines `den` of type `ℝ` by `(T ℝ n).eval I.eta`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
def den (n : ℕ) : ℝ := (T ℝ n).eval I.eta
/-- Defines `residual` of type `ℝ[X]` by `Polynomial.C (I.den n)⁻¹ * (T ℝ n).comp (Polynomial.C
I.eta - Polynomial.C (2 / I.delta) * X)`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
def residual (n : ℕ) : ℝ[X] :=
  Polynomial.C (I.den n)⁻¹ * (T ℝ n).comp
    (Polynomial.C I.eta - Polynomial.C (2 / I.delta) * X)
/-- Defines `epsilon` of type `ℝ` by `1 / I.den n`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
def epsilon (n : ℕ) : ℝ := 1 / I.den n

/-- The stated quantitative bound `0 < I.delta`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
theorem delta_pos : 0 < I.delta := sub_pos.mpr I.mu_lt_L
/-- The stated quantitative bound `0 < I.L + I.mu`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
theorem sum_pos : 0 < I.L + I.mu := by linarith [I.mu_pos, I.mu_lt_L]
/-- The stated quantitative bound `1 < I.eta`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
theorem eta_gt_one : 1 < I.eta := by
  rw [eta, lt_div_iff₀ I.delta_pos]
  dsimp [delta]
  linarith [I.mu_pos]
/-- The stated quantitative bound `0 < I.den n`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
theorem den_pos (n : ℕ) : 0 < I.den n :=
  lt_of_lt_of_le zero_lt_one (one_le_eval_T_real n I.eta_gt_one.le)
/-- The precise assertion is `I.den n ≠ 0`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
theorem den_ne (n : ℕ) : I.den n ≠ 0 := ne_of_gt (I.den_pos n)
/-- Exact identity `I.den 0 = 1`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
@[simp] theorem den_zero : I.den 0 = 1 := by simp [den]
/-- Exact identity `I.den 1 = I.eta`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
@[simp] theorem den_one : I.den 1 = I.eta := by simp [den]
/-- Exact identity `I.den (n + 2) = 2 * I.eta * I.den (n + 1) - I.den n`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
theorem den_add_two (n : ℕ) :
    I.den (n + 2) = 2 * I.eta * I.den (n + 1) - I.den n := by
  simp [den, Nat.cast_add, T_add_two]
/-- Exact identity `I.z lam = I.eta - 2 / I.delta * lam`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
theorem z_eq (lam : ℝ) : I.z lam = I.eta - 2 / I.delta * lam := by
  dsimp [z, eta]
  ring
/-- Exact identity `I.z I.mu = 1`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
@[simp] theorem z_mu : I.z I.mu = 1 := by
  dsimp [z]
  have h : I.L + I.mu - 2 * I.mu = I.delta := by dsimp [delta]; ring
  rw [h, div_self (ne_of_gt I.delta_pos)]
/-- Membership in the specified domain/enclosure: `I.z lam ∈ Set.Icc (-1) 1`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
theorem z_mem {lam : ℝ} (h : lam ∈ Set.Icc I.mu I.L) :
    I.z lam ∈ Set.Icc (-1) 1 := by
  constructor
  · rw [z, le_div_iff₀ I.delta_pos]
    dsimp [delta]
    linarith [h.2]
  · rw [z, div_le_iff₀ I.delta_pos]
    dsimp [delta]
    linarith [h.1]
/-- Exact identity `(I.residual n).eval lam = (T ℝ n).eval (I.z lam) / I.den n`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
theorem residual_eval (n : ℕ) (lam : ℝ) :
    (I.residual n).eval lam = (T ℝ n).eval (I.z lam) / I.den n := by simp [residual, Polynomial.eval_comp, z_eq, div_eq_mul_inv, mul_comm]

/-- The stated quantitative bound `|(I.residual n).eval lam| ≤ I.epsilon n`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
theorem residual_abs_le (n : ℕ) {lam : ℝ} (h : lam ∈ Set.Icc I.mu I.L) :
    |(I.residual n).eval lam| ≤ I.epsilon n := by
  rw [I.residual_eval, abs_div, abs_of_pos (I.den_pos n)]
  exact div_le_div_of_nonneg_right (abs_eval_T_real_le_one n (abs_le.mpr (I.z_mem h)))
    (I.den_pos n).le

end SpectralInterval

/-- The second-kind bound follows from mathlib's endpoint bound for derivatives of T.

The stated quantitative bound `|(U ℝ n).eval x| ≤ n + 1`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Chebyshev recurrence and
normalization outside the interval.
-/
theorem abs_U_eval_le (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(U ℝ n).eval x| ≤ n + 1 := by
  have h := abs_iterate_derivative_T_real_le (n + 1) 1 hx
  simp only [Function.iterate_one] at h
  simp only [T_derivative_eq_U, add_sub_cancel_right, Polynomial.eval_mul,
    Polynomial.eval_intCast, U_eval_one] at h
  push_cast at h
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [abs_mul, abs_of_pos hn] at h
  nlinarith

end
end InexactRealizations.Operators
