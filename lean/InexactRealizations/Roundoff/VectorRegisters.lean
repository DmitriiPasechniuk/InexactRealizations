import InexactRealizations.Algorithms.JournalBalanced
import InexactRealizations.Roundoff.ErrorSystem
import InexactRealizations.Roundoff.LocalErrors

/-! Vector discrepancy identities for the actual averaged-Prefix registers. -/
namespace InexactRealizations.Roundoff
noncomputable section
open InexactRealizations.Algorithms InexactRealizations.Algorithms.AveragedBalanced AveragedParameters
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

omit [Module ℝ E] in
theorem vector_correction_value (n : ℕ) (u : Fin 9 → E) (h4 : u 4 = 0) (h5 : u 5 = 0) :
    u (correctionSlot n) = 0 := by
  by_cases hp : Even n <;> simp [correctionSlot, hp, h4, h5]

theorem vector_next_corrections (d : AveragedParameters N) (s : Fin N) (u : Fin 9 → E) (a : E)
    (h4 : u 4 = 0) (h5 : u 5 = 0) : d.nextState s u a 4 = 0 ∧ d.nextState s u a 5 = 0 := by
  by_cases hp : Even s.val <;> simp [nextState, averageSlot, correctionSlot, gradientSlot, hp, h4, h5]

theorem vector_next_other_average (d : AveragedParameters N) (s : Fin N) (u : Fin 9 → E) (a : E) :
    d.nextState s u a (averageSlot (s.val + 1)) = u (averageSlot (s.val + 1)) := by
  by_cases hp : Even s.val <;> simp [nextState, averageSlot, correctionSlot, gradientSlot, Nat.even_add, hp]

theorem vector_next_other_gradient (d : AveragedParameters N) (s : Fin N) (u : Fin 9 → E) (a : E) :
    d.nextState s u a (gradientSlot (s.val + 1)) = u (gradientSlot (s.val + 1)) := by
  by_cases hp : Even s.val <;> simp [nextState, averageSlot, correctionSlot, gradientSlot, Nat.even_add, hp]

theorem vector_next_current_average (d : AveragedParameters N) (s : Fin N) (u : Fin 9 → E) (a : E)
    (hs : s.val + 2 < N) :
    d.nextState s u a (averageSlot s.val) =
      if s.val < 2 then u 0 else d.phi s • u 0 + (1 - d.phi s) • u (averageSlot s.val) +
        (1 - d.phi s) • u (correctionSlot s.val) := by
  by_cases hp : Even s.val <;> simp [nextState, averageSlot, correctionSlot, gradientSlot, hp, hs]

theorem vector_next_current_gradient (d : AveragedParameters N) (s : Fin N) (u : Fin 9 → E) (a : E)
    (hs : s.val + 2 < N) :
    d.nextState s u a (gradientSlot s.val) =
      if s.val < 2 then a else (1 - d.phi s) • u (gradientSlot s.val) + d.phi s • d.recoveredValue s u a := by
  by_cases hp : Even s.val <;> simp [nextState, averageSlot, correctionSlot, gradientSlot, hp, hs]

theorem recovered_with_filter (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (s : Fin N)
    (H : E →ₗ[ℝ] E) (w : ℕ → E) (u : Fin 9 → E) (h4 : u 4 = 0) (h5 : u 5 = 0)
    (hg : 2 ≤ s.val → u (gradientSlot s.val) - H (u (averageSlot s.val)) = averageError I N w 0 (s.val - 2)) :
    (parameters I N).recoveredValue s u (H ((parameters I N).queryValue s u) + w s.val) =
      H (u 0) + recoveredError I N w 0 s.val := by
  by_cases hs : s.val < 2
  · simp only [recoveredValue, queryValue, recoveredError, hs, ite_true]
  · have hc := vector_correction_value s.val u h4 h5
    have htheta := (theta_unit I hN s.isLt).1.ne'
    have hquery : (parameters I N).queryValue s u = computedQuery (theta I N s.val) (u 0) (u (averageSlot s.val)) 0 := by
      simp only [queryValue, hs, ite_false, parameters, hc, add_zero, computedQuery]
      module
    have hrec (a : E) : (parameters I N).recoveredValue s u a =
        recoveredGradient (theta I N s.val) (u (gradientSlot s.val)) a 0 := by
      simp only [recoveredValue, hs, ite_false, parameters, recoveredGradient, add_zero]
      module
    have hh := recovered_gradient_error H (theta I N s.val) htheta (u 0) 0
      (u (averageSlot s.val)) (u (gradientSlot s.val)) (w s.val) 0 0
    simp only [computedAnswer, combinedOracleError, sub_zero, map_zero, smul_zero, add_zero,
      hg (by omega)] at hh
    have hactual : theta I N s.val •
        ((parameters I N).recoveredValue s u (H ((parameters I N).queryValue s u) + w s.val) - H (u 0)) =
        w s.val - (1 - theta I N s.val) • averageError I N w 0 (s.val - 2) := by
      rw [hquery, hrec]
      exact hh
    have hcanonical := canonical_recovery I hN s.isLt w (0 : ℕ → E)
    simp only [priorError, hs, ite_false] at hcanonical
    have he := congrArg (fun x : E ↦ (theta I N s.val)⁻¹ • x) (hactual.trans hcanonical.symm)
    simp only [smul_smul, inv_mul_cancel₀ htheta, one_smul] at he
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

theorem affine_average_error (H : E →ₗ[ℝ] E) (phi : ℝ) (oldGradient recovered x average : E) :
    ((1 - phi) • oldGradient + phi • recovered) - H (phi • x + (1 - phi) • average) =
      (1 - phi) • (oldGradient - H average) + phi • (recovered - H x) := by
  simp only [map_add, map_smul]
  module

end
end InexactRealizations.Roundoff
