import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

/-! Exact quadratic remainder for the finite polynomial rounding witness. -/
namespace InexactRealizations.Accuracy
noncomputable section
open Polynomial Filter Topology Asymptotics

theorem polynomial_quadratic_remainder (p : ℝ[X]) :
    ∃ q : ℝ[X], ∀ u : ℝ,
      p.eval u = p.coeff 0 + u * p.coeff 1 + u ^ 2 * q.eval u := by
  have hd : (X : ℝ[X]) ^ 2 ∣ p - C (p.coeff 0) - C (p.coeff 1) * X := by
    apply X_pow_dvd_iff.mpr
    intro d hd
    interval_cases d <;> simp
  obtain ⟨q, hq⟩ := hd
  refine ⟨q, fun u ↦ ?_⟩
  have hh := congrArg (fun f : ℝ[X] ↦ f.eval u) hq
  simp only [eval_sub, eval_mul, eval_C, eval_X, eval_pow] at hh
  linarith

end
end InexactRealizations.Accuracy
