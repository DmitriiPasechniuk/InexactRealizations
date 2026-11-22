import InexactRealizations.Chains.SineContinuum.LegendreOrthogonality

/-! Bonnet's three-term recurrence, deduced from the Sturm equation and its unique polynomial solution
with value one at zero.
Use: `InexactRealizations.Chains.SineContinuum.shifted_bonnet` feeds
`InexactRealizations.Chains.SineContinuum.legendre_cross_bonnet` (legendre cross bonnet).
Proof chain: `InexactRealizations.Chains.SineContinuum.legendreV_domain` — chebyshev2,; Legendre
operator, nonlogarithmic realization and continuum sine spectrum.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation. The needed form is proved here.
-/
namespace InexactRealizations.Chains.SineContinuum
noncomputable section
open Polynomial
set_option backward.isDefEq.respectTransparency false

/-- Defines `sturm` of type `Polynomial ℝ` by `((X-X^2)*p.derivative).derivative+C eigenvalue*p`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def sturm (eigenvalue : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  ((X-X^2)*p.derivative).derivative+C eigenvalue*p
/-- Defines `raising` of type `Polynomial ℝ` by `C (c+1)*(1-C 2*X)*p+C 2*(X-X^2)*p.derivative`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def raising (c : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  C (c+1)*(1-C 2*X)*p+C 2*(X-X^2)*p.derivative
/-- Defines `lowering` of type `Polynomial ℝ` by `C c*(1-C 2*X)*p-C 2*(X-X^2)*p.derivative`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def lowering (c : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  C c*(1-C 2*X)*p-C 2*(X-X^2)*p.derivative

/-- Exact identity `(sturm eigenvalue p).coeff j=((j:ℝ)+1)^2*p.coeff
(j+1)+(eigenvalue-(j:ℝ)*(j+1))*p.coeff j`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem sturm_coeff (eigenvalue : ℝ) (p : Polynomial ℝ) (j : ℕ) :
    (sturm eigenvalue p).coeff j=((j:ℝ)+1)^2*p.coeff (j+1)+(eigenvalue-(j:ℝ)*(j+1))*p.coeff j := by
  rw [sturm,coeff_add,coeff_derivative,coeff_C_mul,sub_mul,coeff_sub]
  have hx : (X*p.derivative).coeff (j+1)=p.derivative.coeff j := by
    simpa only [pow_one] using coeff_X_pow_mul p.derivative 1 j
  rw [hx]
  cases j with
  | zero => simp [coeff_X_pow_mul',coeff_derivative]
  | succ j =>
    have hx₂ : (X^2*p.derivative).coeff (j+1+1)=p.derivative.coeff j := by
      simpa only [Nat.add_assoc] using coeff_X_pow_mul p.derivative 2 j
    rw [show j.succ+1=j+1+1 by omega,hx₂,coeff_derivative,coeff_derivative]
    push_cast
    ring

/-- Exact identity `p=q`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem sturm_unique {eigenvalue : ℝ} {p q : Polynomial ℝ}
    (hp : sturm eigenvalue p=0) (hq : sturm eigenvalue q=0) (h0 : p.coeff 0=q.coeff 0) : p=q := by
  ext j
  induction j with
  | zero => exact h0
  | succ j ih =>
    have hpj := congrArg (fun r : Polynomial ℝ => r.coeff j) hp
    have hqj := congrArg (fun r : Polynomial ℝ => r.coeff j) hq
    rw [sturm_coeff,coeff_zero] at hpj hqj
    rw [ih] at hpj
    have he : ((j:ℝ)+1)^2*p.coeff (j+1)=((j:ℝ)+1)^2*q.coeff (j+1) := by linarith
    exact mul_left_cancel₀ (by positivity : ((j:ℝ)+1)^2 ≠ 0) he

/-- Exact identity `sturm eigenvalue (C c*p)=C c*sturm eigenvalue p`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem sturm_const_mul (eigenvalue c : ℝ) (p : Polynomial ℝ) : sturm eigenvalue (C c*p)=C c*sturm eigenvalue p := by
  simp only [sturm,derivative_mul,derivative_C,zero_mul,zero_add]
  ring

/-- The precise assertion is `sturm ((c+1)*(c+2)) (raising c p)= C (c+3)*(1-C 2*X)*sturm (c*(c+1))
p+C 2*(X-X^2)*(sturm (c*(c+1)) p).derivative`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem raising_sturm (c : ℝ) (p : Polynomial ℝ) :
    sturm ((c+1)*(c+2)) (raising c p)=
      C (c+3)*(1-C 2*X)*sturm (c*(c+1)) p+C 2*(X-X^2)*(sturm (c*(c+1)) p).derivative := by
  simp [sturm, raising, derivative_mul, map_add, map_mul, map_ofNat]
  ring

/-- The precise assertion is `sturm (c*(c-1)) (lowering c p)= C (c-2)*(1-C 2*X)*sturm (c*(c+1)) p-C
2*(X-X^2)*(sturm (c*(c+1)) p).derivative`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem lowering_sturm (c : ℝ) (p : Polynomial ℝ) :
    sturm (c*(c-1)) (lowering c p)=
      C (c-2)*(1-C 2*X)*sturm (c*(c+1)) p-C 2*(X-X^2)*(sturm (c*(c+1)) p).derivative := by
  simp [sturm, lowering, derivative_mul, map_add, map_mul, map_sub, map_ofNat]
  ring

/-- Exact identity `raising n (shifted n)=C ((n:ℝ)+1)*shifted (n+1)`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem raising_shifted (n : ℕ) : raising n (shifted n)=C ((n:ℝ)+1)*shifted (n+1) := by
  apply sturm_unique (eigenvalue := ((n:ℝ)+1)*((n:ℝ)+2))
  · rw [raising_sturm,show sturm ((n:ℝ)*(n+1)) (shifted n)=0 from shifted_sturm n]
    simp
  · rw [sturm_const_mul]
    have he : ((n:ℝ)+1)*((n:ℝ)+2)=(n+1:ℕ)*((n+1:ℕ)+1:ℝ) := by push_cast; ring
    rw [he,show sturm ((n+1:ℕ)*((n+1:ℕ)+1:ℝ)) (shifted (n+1))=0 from shifted_sturm (n+1)]
    simp
  · have he : (raising (n:ℝ) (shifted n)).eval 0=(C ((n:ℝ)+1)*shifted (n+1)).eval 0 := by
      simp [raising, ← coeff_zero_eq_eval_zero, shifted_coeff]
    simpa only [← coeff_zero_eq_eval_zero] using he

/-- Exact identity `lowering (j+1) (shifted (j+1))=C ((j:ℝ)+1)*shifted j`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem lowering_shifted (j : ℕ) : lowering (j+1) (shifted (j+1))=C ((j:ℝ)+1)*shifted j := by
  apply sturm_unique (eigenvalue := (j:ℝ)*(j+1))
  · have he : (j:ℝ)*(j+1)=((j:ℝ)+1)*(((j:ℝ)+1)-1) := by ring
    rw [he,lowering_sturm]
    have hz : sturm (((j:ℝ)+1)*(((j:ℝ)+1)+1)) (shifted (j+1))=0 := by
      simpa only [sturm, Nat.cast_add, Nat.cast_one] using shifted_sturm (j+1)
    rw [hz]
    simp
  · rw [sturm_const_mul,show sturm ((j:ℝ)*(j+1)) (shifted j)=0 from shifted_sturm j]
    simp
  · have he : (lowering ((j:ℝ)+1) (shifted (j+1))).eval 0=(C ((j:ℝ)+1)*shifted j).eval 0 := by
      simp [lowering, ← coeff_zero_eq_eval_zero, shifted_coeff]
    simpa only [← coeff_zero_eq_eval_zero] using he

/-- Bonnet's three-term recurrence, deduced from the Sturm equation and its unique polynomial
solution with value one at zero.

The precise assertion is `C ((j:ℝ)+2)*shifted (j+2)+C ((j:ℝ)+1)*shifted j= C (2*(j:ℝ)+3)*(1-C
2*X)*shifted (j+1)`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem shifted_bonnet (j : ℕ) :
    C ((j:ℝ)+2)*shifted (j+2)+C ((j:ℝ)+1)*shifted j=
      C (2*(j:ℝ)+3)*(1-C 2*X)*shifted (j+1) := by
  have hr := raising_shifted (j+1)
  have hl := lowering_shifted j
  dsimp [raising,lowering] at hr hl
  push_cast at hr hl
  simp only [map_add, map_mul, map_ofNat, map_one] at hr hl ⊢
  linear_combination -hr-hl

end
end InexactRealizations.Chains.SineContinuum
