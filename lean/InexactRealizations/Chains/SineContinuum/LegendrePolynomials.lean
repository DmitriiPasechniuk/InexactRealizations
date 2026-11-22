import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! The exact polynomial Sturm--Liouville equation behind.
Use: `InexactRealizations.Chains.SineContinuum.shifted_ode` feeds `InexactRealizations.Chains.SineContinuum.legendre_ode`
(legendre ode).
Proof chain: `InexactRealizations.Chains.SineContinuum.sine_kernel_eigenvalue` — chebyshev2,;
Sine coordinate bijection, symmetry, masses, spectrum, theta formula and tails.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation. The needed form is proved here.
-/
namespace InexactRealizations.Chains.SineContinuum
noncomputable section
open Polynomial
set_option backward.isDefEq.respectTransparency false

/-- The community's exact integer shifted Legendre polynomials, transported to the real coefficient
field.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def shifted (n : ℕ) : Polynomial ℝ := (shiftedLegendre n).map (Int.castRingHom ℝ)

/-- Exact identity `(shifted n).coeff j=(-1:ℝ)^j*(n.choose j:ℝ)*((n+j).choose n:ℝ)`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem shifted_coeff (n j : ℕ) :
    (shifted n).coeff j=(-1:ℝ)^j*(n.choose j:ℝ)*((n+j).choose n:ℝ) := by simp [shifted,coeff_shiftedLegendre]

/-- Exact identity `((j:ℝ)+1)^2*(shifted n).coeff (j+1)+ ((n:ℝ)*(n+1)-(j:ℝ)*(j+1))*(shifted
n).coeff j=0`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem shifted_coeff_recurrence (n j : ℕ) :
    ((j:ℝ)+1)^2*(shifted n).coeff (j+1)+
      ((n:ℝ)*(n+1)-(j:ℝ)*(j+1))*(shifted n).coeff j=0 := by
  rw [shifted_coeff,shifted_coeff]
  by_cases hj : j ≤ n
  · have h₁ : (n.choose (j+1):ℝ)*((j:ℝ)+1)=(n.choose j:ℝ)*((n:ℝ)-j) := by
      exact_mod_cast Nat.choose_succ_right_eq n j
    have h₂ : ((n+j+1).choose n:ℝ)*((j:ℝ)+1)=((n+j).choose n:ℝ)*((n:ℝ)+j+1) := by
      have h := Nat.choose_mul_succ_eq (n+j) n
      rw [show n+j+1-n=j+1 by omega] at h
      exact_mod_cast h.symm
    have hprod : ((j:ℝ)+1)^2*(n.choose (j+1):ℝ)*((n+j+1).choose n:ℝ)=
        ((n:ℝ)-j)*((n:ℝ)+j+1)*(n.choose j:ℝ)*((n+j).choose n:ℝ) := by
      calc
        _ = ((n.choose (j+1):ℝ)*((j:ℝ)+1))*(((n+j+1).choose n:ℝ)*((j:ℝ)+1)) := by ring
        _ = ((n.choose j:ℝ)*((n:ℝ)-j))*(((n+j).choose n:ℝ)*((n:ℝ)+j+1)) := by rw [h₁,h₂]
        _ = _ := by ring
    rw [pow_succ,show n+(j+1)=n+j+1 by omega]
    linear_combination -(-1:ℝ)^j*hprod
  · have hn : n < j := lt_of_not_ge hj
    rw [Nat.choose_eq_zero_of_lt hn,Nat.choose_eq_zero_of_lt (hn.trans (Nat.lt_succ_self j))]
    ring

/-- The exact polynomial Sturm--Liouville equation behind.

Exact identity `((X-X^2)*(shifted n).derivative).derivative+ C ((n:ℝ)*(n+1))*shifted n=0`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem shifted_sturm (n : ℕ) :
    ((X-X^2)*(shifted n).derivative).derivative+
      C ((n:ℝ)*(n+1))*shifted n=0 := by
  ext j
  rw [coeff_add,coeff_derivative,coeff_zero,coeff_C_mul,sub_mul,coeff_sub]
  have hx : (X*(shifted n).derivative).coeff (j+1)=((shifted n).derivative).coeff j := by
    simpa only [pow_one] using coeff_X_pow_mul ((shifted n).derivative) 1 j
  rw [hx]
  cases j with
  | zero =>
    simp only [coeff_X_pow_mul',show ¬ (2:ℕ) ≤ 0+1 by omega,ite_false,sub_zero,coeff_derivative]
    have h := shifted_coeff_recurrence n 0
    norm_num at h ⊢
    exact h
  | succ j =>
    have hx₂ : (X^2*(shifted n).derivative).coeff (j+1+1)=((shifted n).derivative).coeff j := by
      simpa only [Nat.add_assoc] using coeff_X_pow_mul ((shifted n).derivative) 2 j
    rw [show j.succ+1=j+1+1 by omega,hx₂,coeff_derivative,coeff_derivative]
    have h := shifted_coeff_recurrence n (j+1)
    push_cast at h ⊢
    linear_combination h

end
end InexactRealizations.Chains.SineContinuum
