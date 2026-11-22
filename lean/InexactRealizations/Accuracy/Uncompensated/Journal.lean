import InexactRealizations.Accuracy.Uncompensated.Admissible
import InexactRealizations.Accuracy.Uncompensated.Registers

/-! Current(b): the actual uncorrected instruction model,
the exact finite upper coefficient, the asserted lower limiting value,
and an executed admissible-error witness attaining that coefficient.
The per-coordinate terminal upper theorem is
Componentwise.uncompensated_accuracy. Part (a) is
Componentwise.compensated_accuracy. 
-/
namespace InexactRealizations.Accuracy.Uncompensated
noncomputable section
open Filter Topology

theorem journal_average_factors (I : InexactRealizations.Operators.SpectralInterval) :
    (∀ (N : ℕ), 2 ≤ N → I.L * UncompensatedWitness.averageFactor I N ≤
      (N : ℝ) * (I.kappa - 1) * Real.sqrt I.kappa / (4 * N - 4)) ∧
    (∀ eps : ℝ, 0 < eps → ∀ᶠ N : ℕ in atTop,
      (Real.sqrt I.kappa - 1) ^ 2 * Real.sqrt I.kappa / 8 - eps ≤
        I.L * UncompensatedWitness.averageFactor I N) ∧
    (∀ (N : ℕ), 2 ≤ N → ∀ rho : ℝ, 0 ≤ rho →
      Tendsto (fun u : ℝ ↦ |(UncompensatedWitness.atScale I N rho u).x N - rho| / u)
        (𝓝[>] 0) (𝓝 (I.L * UncompensatedWitness.averageFactor I N * rho))) :=
  ⟨fun _ hN ↦ averageFactor_upper I hN,
    fun _ heps ↦ averageFactor_eventual_lower I heps,
    fun _ hN _ hrho ↦ actual_witness_normalized_error I hN hrho⟩

theorem journal_witness_admissible (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (rho : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (hs2 : 2 ≤ s) (hsN : s + 2 < N) :
    let v := AverageExecution.states I N (UncompensatedWitness.hessian I.L) (Polynomial.C rho)
      (Polynomial.C rho) (UncompensatedWitness.rounding N) s
    (UncompensatedWitness.atScale I N rho u).average s =
      (lastAdditionStep N s (v.x.eval u) ((AverageExecution.oldAverage s v).eval u)
        (InexactRealizations.Algorithms.AveragedBalanced.phi I N s) u hu).result :=
  actual_average_instruction I rho hu hs2 hsN

end
end InexactRealizations.Accuracy.Uncompensated
