import InexactRealizations.Synthesis.Theorem

namespace InexactRealizations.History
noncomputable section
open Polynomial
variable {N : ℕ}

/-- The actual one-dimensional Hessian, acting by multiplication by its spectral value.
Use: constructs the scalar oracle executions testing comparison-class membership. 
-/
def scalarOperator (lam : ℝ) : ℝ →ₗ[ℝ] ℝ :=
  algebraMap ℝ (Module.End ℝ ℝ) lam

/-- The scalar operator is literal scalar multiplication.
Use: its physical oracle is the quadratic gradient `lam*x`. 
-/
@[simp] theorem scalarOperator_apply (lam x : ℝ) : scalarOperator lam x = lam * x := by
  simp only [scalarOperator, Module.algebraMap_end_apply, smul_eq_mul]

/-- Polynomial action on a one-dimensional Hessian is ordinary polynomial evaluation.
Use: relates actual noiseless runs to the terminal evaluations in the comparison class. 
-/
theorem scalarOperator_polynomial_action (lam : ℝ) (p : ℝ[X]) (x : ℝ) :
    (aeval (scalarOperator lam) p) x = p.eval lam * x := by
  rw [scalarOperator, aeval_algebraMap_apply_eq_algebraMap_eval]
  simp only [Module.algebraMap_end_apply, smul_eq_mul]

/-- The actual noiseless scalar oracle run returns the polynomial terminal value.
Use: tests exactness using physical execution rather than a supplied transfer identity. 
-/
theorem noiseless_scalar_output (h : InexactRealizations.History N) (lam initial : ℝ) :
    (h.run (scalarOperator lam) initial (fun _ => 0)).output =
      h.terminal.eval lam * initial := by
  calc
    _ = (aeval (scalarOperator lam) h.terminal) initial :=
      h.nominal_output (scalarOperator lam) initial
        (h.run (scalarOperator lam) initial (fun _ => 0))
    _ = _ := scalarOperator_polynomial_action lam h.terminal initial

end
end InexactRealizations.History
