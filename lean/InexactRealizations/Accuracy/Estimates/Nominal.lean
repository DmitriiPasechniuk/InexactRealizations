import InexactRealizations.Accuracy.LocalExecutionMap

/-! Exact Prefix and weighted-average identities for the noiseless local
execution. These are the nominal sizes. The weighted
identity includes the zero startup mass and never divides by it. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators
open InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Roundoff
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def physicalT (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) : ℝ[X] :=
  (T ℝ s).comp (C I.eta - C (2 / I.delta) * X)
def physicalRemainder (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ[X] :=
  (InexactRealizations.Balanced.remainder N s).comp (C I.eta - C (2 / I.delta) * X)

theorem physicalT_eval (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) (lam : ℝ) :
    (physicalT I s).eval lam = (T ℝ s).eval (I.z lam) := by
  have hz : I.eta - 2 / I.delta * lam = I.z lam := by
    unfold InexactRealizations.Operators.SpectralInterval.eta InexactRealizations.Operators.SpectralInterval.z
    ring
  simp only [physicalT, eval_comp, eval_sub, eval_mul, eval_C, eval_X, hz]

theorem physicalRemainder_step (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    physicalRemainder I N (s + 2) = physicalRemainder I N s +
      C (InexactRealizations.Balanced.omega N s - InexactRealizations.Balanced.omega N (s + 2)) * physicalT I s := by
  simp only [physicalRemainder, InexactRealizations.Balanced.remainder, add_comp, mul_comp, C_comp, physicalT]

theorem physicalT_action (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) (H : E →ₗ[ℝ] E) (v : E) :
    (aeval H (physicalT I s)) v = I.den s • (aeval H (I.residual s)) v := by
  have hp : physicalT I s = C (I.den s) * I.residual s := by
    apply Polynomial.funext
    intro lam
    rw [physicalT_eval, eval_mul, eval_C, prefix_scaled]
  rw [hp, map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]

theorem mass_phi (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s + 2 < N) :
    mass I N (s + 2) * phi I N s =
      (InexactRealizations.Balanced.omega N s - InexactRealizations.Balanced.omega N (s + 2)) * I.den s := by
  by_cases hsmall : s < 2
  · have hm : mass I N s = 0 := by
      rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;> simp
    simp only [phi, hsmall, ite_true, mul_one, mass_step, hm, zero_add]
  · rw [phi_eq I hN (by omega) hs]
    field_simp [(mass_next_pos I hN (by omega : 2 ≤ s) hs).ne']

theorem mass_one_minus_phi (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s + 2 < N) :
    mass I N (s + 2) * (1 - phi I N s) = mass I N s := by
  rw [mul_sub, mul_one, mass_phi I hN hs, mass_step]
  ring

theorem nominal_state {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {H : E →ₗ[ℝ] E}
    {initial target : E} (u : LocalExecution I N H initial target (zeroErrors E))
    (hN : 2 ≤ N) (s : ℕ) (hs : s ≤ N) :
    u.x s - target = (aeval H (I.residual s)) (initial - target) := by
  have hw : hatNoise I N H (zeroErrors E) = 0 := by
    funext i
    simp [hatNoise, combinedOracleError, zeroErrors]
  have hi : averageNoise H (zeroErrors E) = 0 := by
    funext i
    simp [averageNoise, combinedAverageError, zeroErrors]
  have hstep (j : Fin N) := u.centered_step hN j
  simp only [hw, hi, recoveredError_zero] at hstep
  simp only [zeroErrors, smul_zero, sub_zero, add_zero] at hstep
  have hh := (prefixPair_unique I N H (initial - target) 0 (fun j ↦ u.x j - target)
    (by rw [u.initial_eq]) (fun j ↦ by simpa only [Pi.zero_apply, add_zero] using hstep j) s hs).1
  rw [← hh, prefixPair_response]
  simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero, add_zero]

theorem nominal_average_weighted {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {H : E →ₗ[ℝ] E}
    {initial target : E} (u : LocalExecution I N H initial target (zeroErrors E))
    (hN : 2 ≤ N) (s : ℕ) (hs : s + 2 < N) :
    mass I N (s + 2) • (u.average s - target) =
      (aeval H (physicalRemainder I N (s + 2))) (initial - target) := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    have hprev : mass I N s • (earlierAverage u.average s - target) =
        (aeval H (physicalRemainder I N s)) (initial - target) := by
      by_cases hsmall : s < 2
      · rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;>
          simp [physicalRemainder, InexactRealizations.Balanced.remainder]
      · have hh := ih (s - 2) (by omega) (by omega)
        have hidx : s - 2 + 2 = s := by omega
        rw [hidx] at hh
        simpa only [earlierAverage, hsmall, ite_false] using hh
    rw [u.average_eq s hs]
    simp only [updatedAverage, zeroErrors, add_zero]
    calc
      _ = (mass I N (s + 2) * phi I N s) • (u.x s - target) +
          (mass I N (s + 2) * (1 - phi I N s)) • (earlierAverage u.average s - target) := by module
      _ = (InexactRealizations.Balanced.omega N s - InexactRealizations.Balanced.omega N (s + 2)) •
          (aeval H (physicalT I s)) (initial - target) +
          (aeval H (physicalRemainder I N s)) (initial - target) := by
        rw [mass_phi I hN hs, mass_one_minus_phi I hN hs, hprev, nominal_state u hN s (by omega),
          physicalT_action, smul_smul]
      _ = _ := by
        rw [physicalRemainder_step, map_add, map_mul, Polynomial.aeval_C,
          LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply]
        abel

end
end InexactRealizations.Accuracy
