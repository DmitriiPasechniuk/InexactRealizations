import InexactRealizations.History.Bezout
import Mathlib.Topology.Algebra.Polynomial

namespace InexactRealizations.History

noncomputable section
variable {N : ℕ}

/-- The physical Bezoutian is jointly continuous in the two spectral parameters. Use: the stated continuous diagonal extension. -/
theorem continuous_physical_bezout (h : InexactRealizations.History N) :
    Continuous (fun xy : ℝ × ℝ => dividedDifference h.terminal xy.1 xy.2) := by
  have hf : (fun xy : ℝ × ℝ => dividedDifference h.terminal xy.1 xy.2) =
      (fun xy => ∑ s, (h.response s).eval xy.1 * (h.query s).eval xy.2) := by
    funext xy
    exact (h.physical_bezout_all xy.1 xy.2).symm
  rw [hf]
  fun_prop

end
end InexactRealizations.History
