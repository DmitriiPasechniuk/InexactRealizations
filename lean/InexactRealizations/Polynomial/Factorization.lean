import InexactRealizations.Polynomial.Graded
import Mathlib.Algebra.Polynomial.Roots

namespace InexactRealizations.GradedFamily
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ} (Q : InexactRealizations.GradedFamily N)

/-- The second-variable polynomial obtained from a separated factor family.
Use: expresses the Bezoutian factorization in the exact graded query basis. 
-/
def separation (f : Fin N → ℝ[X]) (x : ℝ) : ℝ[X] :=
  ∑ s, C ((f s).eval x) * Q.poly s

/-- A separated polynomial identity has unique first-variable polynomial factors.
Use: the unique-factorization assertion. 
-/
theorem separation_injective (f g : Fin N → ℝ[X])
    (h : ∀ x : ℝ, Q.separation f x = Q.separation g x) : f = g := by
  funext s
  apply Polynomial.funext
  intro x
  have hc := Q.expansion_unique (fun j => (f j).eval x) (fun j => (g j).eval x)
    (by simpa only [separation, smul_eq_C_mul] using h x)
  exact congrFun hc s

/-- Pointwise real equality of a factorization is enough for uniqueness.
Use: matches the two-variable evaluation identity as printed in the article. 
-/
theorem factors_unique (f g : Fin N → ℝ[X])
    (h : ∀ x y : ℝ, ∑ s, (f s).eval x * (Q.poly s).eval y =
      ∑ s, (g s).eval x * (Q.poly s).eval y) : f = g := by
  apply Q.separation_injective f g
  intro x
  apply Polynomial.funext
  intro y
  simpa only [separation, eval_finsetSum, eval_mul, eval_C] using h x y

end
end InexactRealizations.GradedFamily
