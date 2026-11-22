import InexactRealizations.Accuracy.Uncompensated.Accuracy

/-! The uncorrected variant under the same per-coordinate instruction
model as(a). 
-/
namespace InexactRealizations.Accuracy.Componentwise
noncomputable section
open InexactRealizations.Accuracy.Execution
variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ ι

theorem uncompensated_accuracy {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ} {p : Prepared I N u}
    {H : V →ₗ[ℝ] V} {initial target : V} {hu : 0 ≤ u}
    (v : Run p H initial target uO hu) (hc : v.toNormed.Uncompensated) (hN : 2 ≤ N)
    (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1) (hH : InexactRealizations.Analysis.Admissible I H) :
    ‖v.states N 0 - target‖ ≤
      I.epsilon N * (1 + 2 * cubicConstant I.kappa * (u + uO) * (N : ℝ) ^ 3) * ‖initial - target‖ +
      (2 * (u + uO) * I.L * InexactRealizations.Lower.additiveScale I N + 8 * u * prefixFactor I N +
        u * I.L * UncompensatedWitness.averageFactor I N) * ‖target‖ +
      (u + uO) ^ 2 * uncompensatedQuadraticConstant I.kappa N * (‖initial - target‖ + ‖target‖) :=
  Execution.uncompensated_accuracy v.toNormed hc hN hu hu2 huO huO1 hH

end
end InexactRealizations.Accuracy.Componentwise
