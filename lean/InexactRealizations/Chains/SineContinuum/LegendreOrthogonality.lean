import InexactRealizations.Chains.SineContinuum.LegendrePolynomials
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Polynomial

/-! Orthogonality of the actual community Legendre polynomials, obtained from their Sturm equation and a
boundary flux that vanishes at both ends.
Use: `InexactRealizations.Chains.SineContinuum.legendre_ode` feeds
`InexactRealizations.Chains.SineContinuum.upsilon_explicit_ode` (The genuine second derivative solves's
singular equation with the exact printed eigenvalue).
Proof chain: `InexactRealizations.Chains.SineContinuum.sine_kernel_eigenvalue` — chebyshev2,;
Sine coordinate bijection, symmetry, masses, spectrum, theta formula and tails.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation. The needed form is proved here.
-/
namespace InexactRealizations.Chains.SineContinuum
noncomputable section
open Polynomial Set Real MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- Defines `legendreValue` of type `ℝ` by `(shifted n).eval x`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def legendreValue (n : ℕ) (x : ℝ) : ℝ := (shifted n).eval x
/-- Defines `legendreFlux` of type `Polynomial ℝ` by `(X-X^2)*((shifted n).derivative*shifted
j-shifted n*(shifted j).derivative)`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def legendreFlux (n j : ℕ) : Polynomial ℝ :=
  (X-X^2)*((shifted n).derivative*shifted j-shifted n*(shifted j).derivative)

/-- The precise assertion is `((X-X^2)*(p.derivative*q-p*q.derivative)).derivative=
((X-X^2)*p.derivative).derivative*q-p*((X-X^2)*q.derivative).derivative`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem polynomial_green_identity (p q : Polynomial ℝ) :
    ((X-X^2)*(p.derivative*q-p*q.derivative)).derivative=
      ((X-X^2)*p.derivative).derivative*q-p*((X-X^2)*q.derivative).derivative := by
  simp only [derivative_mul,derivative_sub]
  ring

/-- The precise assertion is `(legendreFlux n j).derivative= C ((j:ℝ)*(j+1)-(n:ℝ)*(n+1))*shifted
n*shifted j`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem legendreFlux_derivative (n j : ℕ) :
    (legendreFlux n j).derivative=
      C ((j:ℝ)*(j+1)-(n:ℝ)*(n+1))*shifted n*shifted j := by
  have hn := eq_neg_of_add_eq_zero_left (shifted_sturm n)
  have hj := eq_neg_of_add_eq_zero_left (shifted_sturm j)
  rw [legendreFlux,polynomial_green_identity,hn,hj,map_sub]
  ring

/-- The stated quantitative bound `StrictMono (fun n : ℕ => (n:ℝ)*(n+1))`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem shifted_eigenvalue_strictMono : StrictMono (fun n : ℕ => (n:ℝ)*(n+1)) := by
  intro n j hnj
  have h : (n:ℝ) < j := by exact_mod_cast hnj
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- Orthogonality of the actual community Legendre polynomials, obtained from their Sturm equation
and a boundary flux that vanishes at both ends.

Exact identity `(∫ x in (0:ℝ)..1, legendreValue n x*legendreValue j x)=0`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem legendre_orthogonal {n j : ℕ} (hnj : n ≠ j) :
    (∫ x in (0:ℝ)..1, legendreValue n x*legendreValue j x)=0 := by
  let P := legendreFlux n j
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => P.hasDerivAt x)
    (P.derivative.continuous.intervalIntegrable (μ := volume) 0 1)
  have h0 : P.eval 0=0 := by simp [P,legendreFlux]
  have h1 : P.eval 1=0 := by simp [P,legendreFlux]
  rw [h0,h1,sub_self] at hi
  have he : (fun x => P.derivative.eval x)=
      (fun x => ((j:ℝ)*(j+1)-(n:ℝ)*(n+1))*(legendreValue n x*legendreValue j x)) := by
    funext x
    rw [show P=legendreFlux n j from rfl,legendreFlux_derivative]
    simp only [eval_mul,eval_C,legendreValue]
    ring
  rw [he,intervalIntegral.integral_const_mul] at hi
  have hc : (j:ℝ)*(j+1)-(n:ℝ)*(n+1) ≠ 0 := by
    intro hz
    exact hnj (shifted_eigenvalue_strictMono.injective (sub_eq_zero.mp hz).symm)
  exact (mul_eq_zero.mp hi).resolve_left hc

end
end InexactRealizations.Chains.SineContinuum
