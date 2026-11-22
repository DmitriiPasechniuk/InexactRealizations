import InexactRealizations.Operators.SineJacobi.RogersCoefficients

/-! At degree N all internal Fourier modes cancel, leaving the two Chebyshev modes.
Use: `InexactRealizations.Operators.SineJacobi.rogers_terminal` feeds
`InexactRealizations.Operators.SineJacobi.blockFourier_terminal` (block Fourier terminal).
Proof chain: `InexactRealizations.Operators.SineJacobi.terminal` — chebyshev1,; Sine-lattice
couplings, spectrum, expansion and symmetry.
Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov, q-Ultraspherical
polynomials for q a root of unity — Rogers recurrence and finite Fourier expansion. The needed form
is proved here.
-/
namespace InexactRealizations.Operators.SineJacobi
noncomputable section
open Polynomial
open scoped BigOperators

/-- The finite polynomial encoding the Fourier coefficients by their insertion index.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.
-/
def rogers (N s : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (s+1), C (coefficient N s k) * X^k

/-- Exact identity `(rogers N s).coeff k = coefficient N s k`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.
-/
@[simp] theorem rogers_coeff (N s k : ℕ) : (rogers N s).coeff k = coefficient N s k := by
  by_cases hk : k ≤ s
  · simp [rogers, coefficient, hk, show k < s+1 by omega]
  · simp [rogers, coefficient, hk, show ¬k < s+1 by omega]

/-- Exact identity `coefficient N s k = 0`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.
-/
theorem coefficient_of_gt (N s k : ℕ) (hk : s < k) : coefficient N s k = 0 := by simp [coefficient, Nat.not_le.mpr hk]

/-- Exact identity `rogers N 0 = 1`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.
-/
theorem rogers_zero (N : ℕ) (hN : 0 < N) : rogers N 0 = 1 := by simp [rogers, coefficient_zero N 0 hN]

/-- Exact identity `rogers N 1 = 1+X`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.
-/
theorem rogers_one (N : ℕ) (hN : 1 < N) : rogers N 1 = 1+X := by simp [rogers, Finset.sum_range_succ, coefficient_zero N 1 hN, coefficient_last N 1 hN]

/-- Exact identity `rogers N (s+1) = (1+X)*rogers N s - C (4*couplingSq N s)*X*rogers N (s-1)`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.
-/
theorem rogers_recurrence (N s : ℕ) (hs : s+1 < N) (hs0 : 0 < s) :
    rogers N (s+1) = (1+X)*rogers N s - C (4*couplingSq N s)*X*rogers N (s-1) := by
  rw [add_mul, one_mul, mul_assoc]
  apply Polynomial.ext
  intro k
  cases k with
  | zero => simp [coefficient_zero N (s+1) hs, coefficient_zero N s (by omega)]
  | succ k =>
    simp only [coeff_sub, coeff_add, coeff_X_mul, coeff_C_mul, rogers_coeff]
    by_cases hk : k+1 ≤ s
    · simpa only [Nat.add_sub_cancel] using coefficient_recurrence N s (k+1) hs (by omega) hk
    · by_cases he : k = s
      · subst k
        rw [coefficient_last N (s+1) hs, coefficient_of_gt N s (s+1) (by omega),
          coefficient_last N s (by omega), coefficient_of_gt N (s-1) s (by omega)]
        ring
      · rw [coefficient_of_gt N (s+1) (k+1) (by omega), coefficient_of_gt N s (k+1) (by omega),
          coefficient_of_gt N s k (by omega), coefficient_of_gt N (s-1) k (by omega)]
        ring

/-- At degree N all internal Fourier modes cancel, leaving the two Chebyshev modes.

Exact identity `(1+X)*rogers N (N-1) - C (4*couplingSq N (N-1))*X*rogers N (N-2) = 1+X^N`.

Source: Koekoek and Swarttouw, The Askey-scheme, §3.10.1; Spiridonov and Zhedanov,
q-Ultraspherical polynomials for q a root of unity — Rogers recurrence and finite Fourier
expansion.
-/
theorem rogers_terminal (N : ℕ) (hN : 2 ≤ N) :
    (1+X)*rogers N (N-1) - C (4*couplingSq N (N-1))*X*rogers N (N-2) = 1+X^N := by
  rw [add_mul, one_mul, mul_assoc]
  apply Polynomial.ext
  intro k
  cases k with
  | zero => simp [coefficient_zero N (N-1) (by omega), show (0:ℕ) ≠ N by omega]
  | succ k =>
    simp only [coeff_sub, coeff_add, coeff_X_mul, coeff_C_mul, rogers_coeff]
    by_cases hk : k+1 < N
    · rw [show N-2 = (N-1)-1 by omega]
      have hb := coefficient_terminal_cancel N (k+1) (by omega) hk
      simp only [Nat.add_sub_cancel] at hb
      rw [show N-2 = (N-1)-1 by omega] at hb
      rw [hb]
      simp [coeff_X_pow, coeff_one, show k+1 ≠ N by omega]
    · by_cases he : k+1 = N
      · have hk' : k = N-1 := by omega
        rw [hk']
        rw [coefficient_of_gt N (N-1) (N-1+1) (by omega), coefficient_last N (N-1) (by omega),
          coefficient_of_gt N (N-2) (N-1) (by omega)]
        simp [coeff_X_pow, coeff_one, show N-1+1 = N by omega, show N ≠ 0 by omega]
      · rw [coefficient_of_gt N (N-1) (k+1) (by omega), coefficient_of_gt N (N-1) k (by omega),
          coefficient_of_gt N (N-2) k (by omega)]
        simp [coeff_X_pow, coeff_one, show k+1 ≠ N by omega]

end
end InexactRealizations.Operators.SineJacobi
