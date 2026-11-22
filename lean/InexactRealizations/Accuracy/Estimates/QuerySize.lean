import InexactRealizations.Accuracy.Estimates.Sizes

/-! The exact stopped-parity nominal query and its r/Z_s bound. -/
namespace InexactRealizations.Accuracy
noncomputable section
open Polynomial
open InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Roundoff

def physicalPsi (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ[X] :=
  physicalRemainder I N s + C (InexactRealizations.Balanced.omega N s) * physicalT I s

theorem physicalPsi_eval (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (lam : ℝ) :
    (physicalPsi I N s).eval lam = (InexactRealizations.Balanced.psi N s).eval (I.z lam) := by
  simp only [physicalPsi, eval_add, eval_mul, eval_C, physicalRemainder_eval, physicalT_eval,
    InexactRealizations.Balanced.psi]

section Algebra
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {H : E →ₗ[ℝ] E} {initial target : E}

theorem nominal_query_weighted (u : LocalExecution I N H initial target (zeroErrors E))
    (hN : 2 ≤ N) (s : ℕ) (hs : s < N) :
    InexactRealizations.Balanced.normalizer I N s • (u.y s - target) =
      (aeval H (physicalPsi I N s)) (initial - target) := by
  have hprev : mass I N s • (earlierAverage u.average s - target) =
      (aeval H (physicalRemainder I N s)) (initial - target) := by
    by_cases hsmall : s < 2
    · rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
        simp [physicalRemainder, InexactRealizations.Balanced.remainder]
    · have hh := nominal_average_weighted u hN (s - 2) (by omega)
      have hidx : s - 2 + 2 = s := by omega
      rw [hidx] at hh
      simpa only [earlierAverage, hsmall, ite_false] using hh
  have hp : InexactRealizations.Balanced.normalizer I N s * theta I N s =
      InexactRealizations.Balanced.omega N s * I.den s := by
    rw [theta_eq I hN hs]
    field_simp [(InexactRealizations.Balanced.normalizer_pos I hN hs).ne']
  have hq : InexactRealizations.Balanced.normalizer I N s * (1 - theta I N s) = mass I N s := by
    rw [theta_mass I hN hs]
    field_simp [(InexactRealizations.Balanced.normalizer_pos I hN hs).ne']
  rw [u.query_eq s hs]
  simp only [computedQuery, zeroErrors, add_zero]
  calc
    _ = (InexactRealizations.Balanced.normalizer I N s * theta I N s) • (u.x s - target) +
        (InexactRealizations.Balanced.normalizer I N s * (1 - theta I N s)) •
          (earlierAverage u.average s - target) := by module
    _ = InexactRealizations.Balanced.omega N s • (aeval H (physicalT I s)) (initial - target) +
        (aeval H (physicalRemainder I N s)) (initial - target) := by
      rw [hp, hq, hprev, nominal_state u hN s hs.le, physicalT_action, smul_smul]
    _ = _ := by
      rw [physicalPsi, map_add, map_mul, Polynomial.aeval_C, LinearMap.add_apply,
        Module.End.mul_apply, Module.algebraMap_end_apply]
      abel
end Algebra

section Norm
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {H : E →ₗ[ℝ] E} {initial target : E}

theorem nominal_query_bound (u : LocalExecution I N H initial target (zeroErrors E))
    (hN : 2 ≤ N) (hH : InexactRealizations.Analysis.Admissible I H) (s : ℕ) (hs : s < N) :
    ‖u.y s - target‖ ≤ ‖initial - target‖ / InexactRealizations.Balanced.normalizer I N s := by
  have hz := InexactRealizations.Balanced.normalizer_pos I hN hs
  have hp (lam : ℝ) (hlam : lam ∈ Set.Icc I.mu I.L) : |(physicalPsi I N s).eval lam| ≤ 1 := by
    rw [physicalPsi_eval]
    exact InexactRealizations.Balanced.abs_psi_eval_le_one hN hs (abs_le.mpr (I.z_mem hlam))
  have hb := InexactRealizations.Analysis.polynomial_action_bound I H hH (physicalPsi I N s) 1 zero_le_one hp
    (initial - target)
  rw [← nominal_query_weighted u hN s hs, norm_smul, Real.norm_eq_abs, abs_of_pos hz, one_mul] at hb
  exact (le_div_iff₀ hz).mpr (by simpa only [mul_comm] using hb)
end Norm

end
end InexactRealizations.Accuracy
