import InexactRealizations.Chains.SineContinuum.LegendreRecurrence

/-! The exact norm of the community shifted Legendre polynomial.
Use: `InexactRealizations.Chains.SineContinuum.legendre_norm` feeds
`InexactRealizations.Chains.SineContinuum.normalizedLegendre_orthonormal` (normalized Legendre orthonormal).
Proof chain: `InexactRealizations.Chains.SineContinuum.legendreV_domain` — chebyshev2,; Legendre
operator, nonlogarithmic realization and continuum sine spectrum.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation. The needed form is proved here.
-/
namespace InexactRealizations.Chains.SineContinuum
noncomputable section
open Polynomial Real MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- Integration on the unit interval as a linear functional on real polynomials.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def polynomialIntegral : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ x in (0:ℝ)..1, p.eval x
  map_add' p q := by
    simp only [eval_add]
    exact intervalIntegral.integral_add
      (p.continuous.intervalIntegrable (μ := volume) 0 1)
      (q.continuous.intervalIntegrable (μ := volume) 0 1)
  map_smul' c p := by
    simp only [eval_smul, RingHom.id_apply]
    exact intervalIntegral.integral_smul c _

/-- Exact identity `polynomialIntegral (C c*p)=c*polynomialIntegral p`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem polynomialIntegral_C_mul (c : ℝ) (p : Polynomial ℝ) :
    polynomialIntegral (C c*p)=c*polynomialIntegral p := by
  change (∫ x in (0:ℝ)..1, (C c*p).eval x)=c*(∫ x in (0:ℝ)..1, p.eval x)
  simp only [eval_mul, eval_C]
  exact intervalIntegral.integral_const_mul c _

/-- Exact identity `polynomialIntegral p.derivative=p.eval 1-p.eval 0`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem polynomialIntegral_derivative (p : Polynomial ℝ) :
    polynomialIntegral p.derivative=p.eval 1-p.eval 0 :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => p.hasDerivAt x)
    (p.derivative.continuous.intervalIntegrable (μ := volume) 0 1)
/-- Defines `legendreNorm` of type `ℝ` by `polynomialIntegral (shifted n*shifted n)`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def legendreNorm (n : ℕ) : ℝ := polynomialIntegral (shifted n*shifted n)
/-- Defines `legendreCross` of type `ℝ` by `polynomialIntegral ((1-C 2*X)*shifted n*shifted
(n+1))`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def legendreCross (n : ℕ) : ℝ := polynomialIntegral ((1-C 2*X)*shifted n*shifted (n+1))

/-- Exact identity `((n:ℝ)+1)*legendreNorm n=(2*(n:ℝ)+3)*legendreCross n`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem legendre_cross_bonnet (n : ℕ) :
    ((n:ℝ)+1)*legendreNorm n=(2*(n:ℝ)+3)*legendreCross n := by
  have h := congrArg (fun p : Polynomial ℝ => polynomialIntegral (p*shifted n)) (shifted_bonnet n)
  rw [add_mul, LinearMap.map_add] at h
  simp only [mul_assoc, polynomialIntegral_C_mul] at h
  have hz : polynomialIntegral (shifted (n+2)*shifted n)=0 := by
    change (∫ x in (0:ℝ)..1, (shifted (n+2)*shifted n).eval x)=0
    simpa only [eval_mul, legendreValue] using legendre_orthogonal (n := n+2) (j := n) (by omega)
  rw [hz, mul_zero, zero_add] at h
  have hc : (1-C 2*X)*(shifted (n+1)*shifted n)=
      (1-C 2*X)*shifted n*shifted (n+1) := by ring
  rw [hc] at h
  exact h

/-- Exact identity `2*legendreCross n=((n:ℝ)+1)*(legendreNorm n-legendreNorm (n+1))`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem legendre_cross_flux (n : ℕ) :
    2*legendreCross n=((n:ℝ)+1)*(legendreNorm n-legendreNorm (n+1)) := by
  let flux := (X-X^2)*shifted n*shifted (n+1)
  have hf : C 2*flux.derivative=
      C 2*(1-C 2*X)*shifted n*shifted (n+1)+
      C ((n:ℝ)+1)*(shifted (n+1)*shifted (n+1)-shifted n*shifted n) := by
    have hr := raising_shifted n
    have hl := lowering_shifted n
    dsimp [raising,lowering] at hr hl
    dsimp [flux]
    simp only [derivative_mul,derivative_sub,derivative_X,derivative_X_sq]
    simp only [map_ofNat] at hr hl ⊢
    linear_combination shifted (n+1)*hr-shifted n*hl
  have hi := congrArg polynomialIntegral hf
  have hboundary : polynomialIntegral flux.derivative=0 := by
    rw [polynomialIntegral_derivative]
    simp [flux]
  rw [LinearMap.map_add] at hi
  simp only [mul_assoc, polynomialIntegral_C_mul] at hi
  rw [LinearMap.map_sub] at hi
  have hc : polynomialIntegral ((1-C 2*X)*(shifted n*shifted (n+1)))=legendreCross n := by
    congr 1
    ring
  rw [hc] at hi
  rw [hboundary,mul_zero] at hi
  change 2*legendreCross n=((n:ℝ)+1)*(polynomialIntegral (shifted n*shifted n)-polynomialIntegral (shifted (n+1)*shifted (n+1)))
  linear_combination -hi

/-- Exact identity `(2*(n:ℝ)+3)*legendreNorm (n+1)=(2*(n:ℝ)+1)*legendreNorm n`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem legendre_norm_recurrence (n : ℕ) :
    (2*(n:ℝ)+3)*legendreNorm (n+1)=(2*(n:ℝ)+1)*legendreNorm n := by
  have hb := legendre_cross_bonnet n
  have hf := legendre_cross_flux n
  have hn : 0 < (n:ℝ)+1 := by positivity
  nlinarith

/-- The exact norm of the community shifted Legendre polynomial.

Exact identity `legendreNorm n=1/(2*(n:ℝ)+1)`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem legendre_norm (n : ℕ) : legendreNorm n=1/(2*(n:ℝ)+1) := by
  induction n with
  | zero =>
    have hp : shifted 0=1 := by
      ext j
      cases j with
      | zero => simp [shifted_coeff]
      | succ j => simp [shifted_coeff, coeff_one]
    simp [legendreNorm, polynomialIntegral,hp]
  | succ n ih =>
    have h := legendre_norm_recurrence n
    rw [ih] at h
    have hn : 2*(n:ℝ)+1 ≠ 0 := by positivity
    push_cast
    apply (eq_div_iff (by positivity : 2*((n:ℝ)+1)+1 ≠ 0)).2
    field_simp [hn] at h
    nlinarith

/-- Exact identity `(∫ x in (0:ℝ)..1, (legendreValue n x)^2)=1/(2*(n:ℝ)+1)`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem legendre_integral_sq (n : ℕ) :
    (∫ x in (0:ℝ)..1, (legendreValue n x)^2)=1/(2*(n:ℝ)+1) := by
  have h := legendre_norm n
  change (∫ x in (0:ℝ)..1, (shifted n*shifted n).eval x)=_ at h
  simpa only [legendreValue, eval_mul, pow_two] using h

end
end InexactRealizations.Chains.SineContinuum
