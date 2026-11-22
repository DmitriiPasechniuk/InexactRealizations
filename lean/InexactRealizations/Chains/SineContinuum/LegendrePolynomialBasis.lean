import InexactRealizations.Chains.SineContinuum.LegendrePolynomials
import Mathlib.Algebra.Polynomial.Sequence

/-! Every real polynomial is a finite linear combination of shifted Legendre polynomials.
Use: `InexactRealizations.Chains.SineContinuum.shifted_span` feeds
`InexactRealizations.Chains.SineContinuum.normalizedLegendre_span_dense` (normalized Legendre span dense).
Proof chain: `InexactRealizations.Chains.SineContinuum.legendreV_domain` — chebyshev2,; Legendre
operator, nonlogarithmic realization and continuum sine spectrum.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation. The needed form is proved here.
-/
namespace InexactRealizations.Chains.SineContinuum
noncomputable section
open Polynomial

/-- The exact community Legendre polynomials have degree equal to their index.

Exact identity `(shifted n).degree=n`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
theorem shifted_degree (n : ℕ) : (shifted n).degree=n := by rw [shifted, degree_map_eq_of_injective (Int.cast_injective), degree_shiftedLegendre]

/-- Constructs `legendreSequence` of type `Polynomial.Sequence ℝ` by the displayed record fields.
Data fields specify the construction; proof fields discharge its required properties.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def legendreSequence : Polynomial.Sequence ℝ where
  elems' := shifted
  degree_eq' := shifted_degree

end
end InexactRealizations.Chains.SineContinuum
