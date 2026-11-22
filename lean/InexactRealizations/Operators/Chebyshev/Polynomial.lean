import InexactRealizations.Operators.Chebyshev.Normalization
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.Polynomial.Roots

/-! Equality on the nondegenerate spectral interval is polynomial equality.
Use: `InexactRealizations.Operators.SpectralInterval.residual_ne_zero` feeds `InexactRealizations.Operators.TwoTerm.local_unique`
(Local coefficient uniqueness (C.1), requiring only the three scalar prefixes).
Proof chain: `InexactRealizations.Operators.TwoTerm.local_unique` — chebyshev1,; Local uniqueness of
the causal two-term realization.
Source: mathlib polynomial theory; NIST Digital Library of Mathematical Functions, Chapter 18 —
Chebyshev degree and affine polynomial substitution. The needed form is proved here.
-/
namespace InexactRealizations.Operators.SpectralInterval
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped Polynomial
variable (I : SpectralInterval)

/-- Exact identity `(I.residual n).natDegree = n`.

Source: mathlib polynomial theory; NIST Digital Library of Mathematical Functions, Chapter 18 —
Chebyshev degree and affine polynomial substitution.
-/
theorem residual_natDegree (n : ℕ) : (I.residual n).natDegree = n := by
  have ha : (2 / I.delta : ℝ) ≠ 0 := div_ne_zero (by norm_num) (ne_of_gt I.delta_pos)
  have hz : (Polynomial.C I.eta - Polynomial.C (2 / I.delta) * X).natDegree = 1 := by
    rw [← neg_sub, natDegree_neg,
      natDegree_sub_C, natDegree_C_mul_X _ ha]
  rw [residual, natDegree_C_mul (inv_ne_zero (I.den_ne n)), natDegree_comp, hz]
  simp

end
end InexactRealizations.Operators.SpectralInterval
