import InexactRealizations.Gains.Bounds
import Mathlib.Topology.Order.LiminfLimsup

namespace InexactRealizations.Gains
noncomputable section
open Polynomial Filter Topology
open scoped BigOperators
variable {N : ℕ}

section Homogeneity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scale every state and physical error in one actual execution by the same scalar. -/
def scaleExecution (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise) (c : ℝ) :
    h.Execution H (c • initial) (fun s => c • noise s) where
  query s := c • u.query s
  answer s := c • u.answer s
  query_eq s := by
    rw [u.query_eq]
    simp only [smul_sub, Finset.smul_sum, smul_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  answer_eq s := by rw [u.answer_eq, smul_add, map_smul]

/-- The physical terminal scales with the actual execution. -/
theorem scaleExecution_output (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise) (c : ℝ) :
    (scaleExecution h H initial noise u c).output = c • u.output := by
  simp only [InexactRealizations.History.Execution.output, scaleExecution, smul_sub,
    Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_comm]

/-- Normalized deviation risk is homogeneous in the initial radius. -/
theorem scaleExecution_error (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise) (c : ℝ) :
    ‖(scaleExecution h H initial noise u c).output - (aeval H h.terminal) (c • initial)‖ =
      |c| * ‖u.output - (aeval H h.terminal) initial‖ := by
  rw [scaleExecution_output, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs]

end Homogeneity

end
end InexactRealizations.Gains
