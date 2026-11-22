import InexactRealizations.Roundoff.PrefixProgram

/-! Exact forced Prefix execution used in the roundoff identity, in every
real module and with arbitrary errors. 
-/
namespace InexactRealizations.Roundoff
noncomputable section
open scoped BigOperators
open InexactRealizations.Algorithms InexactRealizations.Algorithms.AveragedBalanced
open InexactRealizations.Comparisons.Competitors
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def prefixPair (I : InexactRealizations.Operators.SpectralInterval) (H : E →ₗ[ℝ] E) (initial : E) (e : ℕ → E) : ℕ → E × E
  | 0 => (initial, initial)
  | s + 1 =>
    let p := prefixPair I H initial e s
    ((1 + beta I s) • p.1 - beta I s • p.2 - alpha I s • (H p.1 + e s), p.1)

theorem prefixPair_program (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E)
    (initial : E) (e : ℕ → E) (k : ℕ) (hk : k ≤ N) :
    let u := ((prefixMomentum I).program N).runPrefix (fun s y ↦ H y + e s.val) initial k
    u.vectors 0 = (prefixPair I H initial e k).1 ∧ u.vectors 1 = (prefixPair I H initial e k).2 := by
  induction k with
  | zero => simp [prefixPair, RegisterProgram.runPrefix, RegisterProgram.initialState, Momentum.program]
  | succ k ih =>
    have hlt : k < N := by omega
    have hi := ih (by omega)
    let old := ((prefixMomentum I).program N).runPrefix (fun s y ↦ H y + e s.val) initial k
    have hv : old = ⟨![old.vectors 0, old.vectors 1, old.vectors 2], old.calls⟩ := by
      apply RegisterState.ext
      · ext i; fin_cases i <;> rfl
      · rfl
    have hh := (prefixMomentum I).stage_vectors N ⟨k, hlt⟩ (fun s y ↦ H y + e s.val)
      (old.vectors 0) (old.vectors 1) (old.vectors 2) old.calls
    rw [RegisterProgram.runPrefix, dite_eq_left hlt]
    change (((prefixMomentum I).program N).stage _ ⟨k, hlt⟩ old).vectors 0 = _ ∧
      (((prefixMomentum I).program N).stage _ ⟨k, hlt⟩ old).vectors 1 = _
    rw [hv, hh]
    dsimp only [old] at hi
    simp only [prefixMomentum, Momentum.previous, Momentum.query, Bool.false_eq_true, ite_false] at *
    change (1 + beta I k) • old.vectors 0 - beta I k • old.vectors 1 - alpha I k • (H (old.vectors 0) + e k) = _ ∧
      old.vectors 0 = _
    rw [show old.vectors 0 = _ from hi.1, show old.vectors 1 = _ from hi.2]
    exact ⟨rfl, rfl⟩

theorem prefixPair_response (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E)
    (initial : E) (e : ℕ → E) :
    (prefixPair I H initial e N).1 =
      (Polynomial.aeval H (I.residual N)) initial +
        ∑ s : Fin N, (Polynomial.aeval H ((InexactRealizations.Classical.history I N).response s)) (e s.val) := by
  have hp := (prefixPair_program I N H initial e N le_rfl).1
  have ho := (prefixMomentum I).output_eq_history N (fun s y ↦ H y + e s.val) initial
  change (((prefixMomentum I).program N).runPrefix (fun s y ↦ H y + e s.val) initial N).vectors 0 = _ at ho
  rw [hp, prefix_history_eq_classical] at ho
  rw [ho, InexactRealizations.History.oracleOutput_linear, InexactRealizations.History.physical_response,
    InexactRealizations.Classical.history_exact I N]

end
end InexactRealizations.Roundoff
