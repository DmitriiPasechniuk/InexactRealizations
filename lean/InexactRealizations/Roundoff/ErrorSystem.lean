import InexactRealizations.Roundoff.ErrorFilter

/-! The printed local discrepancy recurrences uniquely determine the
causal error filter. These recurrences do not assume a terminal response. 
-/
namespace InexactRealizations.Roundoff
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def priorError (bar : ℕ → E) (s : ℕ) : E := if s < 2 then 0 else bar (s - 2)

structure ErrorSystem (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (w iota hat bar : ℕ → E) : Prop where
  recovery : ∀ s, s < N → theta I N s • hat s = w s - (1 - theta I N s) • priorError bar s
  averaging : ∀ s, s + 2 < N →
    bar s = (1 - phi I N s) • priorError bar s + phi I N s • hat s + iota s

theorem canonical_recovery (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s < N) (w iota : ℕ → E) :
    theta I N s • recoveredError I N w iota s =
      w s - (1 - theta I N s) • priorError (averageError I N w iota) s := by
  by_cases hsmall : s < 2
  · simp [recoveredError, priorError, theta, hsmall]
  · simp only [recoveredError, priorError, hsmall, ite_false, smul_smul,
      mul_inv_cancel₀ (theta_unit I hN hs).1.ne', one_smul]

theorem canonical_averaging (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s + 2 < N) (w iota : ℕ → E) :
    averageError I N w iota s = (1 - phi I N s) • priorError (averageError I N w iota) s +
      phi I N s • recoveredError I N w iota s + iota s := by
  cases s with
  | zero => simp [averageError, recoveredError, priorError, phi]
  | succ s =>
    cases s with
    | zero => simp [averageError, recoveredError, priorError, phi]
    | succ s =>
      have hsmall : ¬s + 2 < 2 := by omega
      have ht := (theta_unit I hN (by omega : s + 2 < N)).1.ne'
      have hc : 1 - phi I N (s + 2) / theta I N (s + 2) =
          (1 - phi I N (s + 2)) - phi I N (s + 2) * (theta I N (s + 2))⁻¹ * (1 - theta I N (s + 2)) := by
        field_simp [ht]
        ring
      change averageError I N w iota (s + 2) =
        (1 - phi I N (s + 2)) • priorError (averageError I N w iota) (s + 2) +
          phi I N (s + 2) • recoveredError I N w iota (s + 2) + iota (s + 2)
      simp only [averageError, priorError, recoveredError, hsmall, ite_false, Nat.add_sub_cancel]
      rw [hc]
      simp only [div_eq_mul_inv]
      module

theorem errorSystem_unique (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (w iota hat bar : ℕ → E) (h : ErrorSystem I N w iota hat bar) :
    ∀ s, s < N → hat s = recoveredError I N w iota s ∧
      (s + 2 < N → bar s = averageError I N w iota s) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro hs
    have hp : priorError bar s = priorError (averageError I N w iota) s := by
      by_cases hsmall : s < 2
      · simp [priorError, hsmall]
      · have hh := (ih (s - 2) (by omega) (by omega)).2 (by omega)
        simp only [priorError, hsmall, ite_false, hh]
    have he : theta I N s • hat s = theta I N s • recoveredError I N w iota s := by
      rw [h.recovery s hs, hp, canonical_recovery I hN hs w iota]
    have hh := congrArg (fun x : E ↦ (theta I N s)⁻¹ • x) he
    have hhat : hat s = recoveredError I N w iota s := by
      simpa only [smul_smul, inv_mul_cancel₀ (theta_unit I hN hs).1.ne', one_smul] using hh
    refine ⟨hhat, ?_⟩
    intro hs'
    rw [h.averaging s hs', hp, hhat]
    exact (canonical_averaging I hN hs' w iota).symm

end
end InexactRealizations.Roundoff
