import InexactRealizations.Algorithms.FlatRatios

/-! Current LemmaB.1 and Algorithm1: the ratio-prepared four-register
program has the original Flat queries/output/responses for every oracle. 
-/
namespace InexactRealizations.Algorithms.Flat
noncomputable section
open scoped BigOperators

theorem journal_flat_preparation_defined (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    0 < 2 * I.eta ∧ (∀ j, 0 < 2 * I.eta - ratioU I j) ∧
      0 < ratioMass I N ∧ 0 < I.delta ∧ 0 < I.eta - ratioU I (N - 2) ∧
      ∀ s : Fin N, 0 < 1 + ratioTau I N s := by
  refine ⟨by linarith only [I.eta_gt_one], ratioU_denominator_pos I,
    ratioMass_pos I (by omega), I.delta_pos, ratio_terminal_denominator_pos I N, ?_⟩
  intro s
  rw [ratioTau_eq I (by omega : 0 < N) s.isLt]
  have hh := InexactRealizations.Flat.tau_nonneg I N (by omega) s.val s.isLt
  linarith only [hh]

theorem journal_flat_physical_response {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (initial : E) (w : Fin N → E) :
    (ratioProgram I N).output (fun s y ↦ H y + w s) initial =
      (Polynomial.aeval H (I.residual N)) initial +
        ∑ s, (Polynomial.aeval H ((InexactRealizations.Flat.history I N hN).response s)) (w s) := by
  rw [ratioProgram_eq I N hN]
  exact physical_response I N hN H initial w

theorem journal_flat_oracle_calls {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (oracle : Fin N → E → E) (initial : E) :
    ((ratioProgram I N).run oracle initial).calls = N := RegisterProgram.run_calls _ _ _

theorem journal_flat_vector_slots : Fintype.card (Fin 4) = 4 := Fintype.card_fin 4

end
end InexactRealizations.Algorithms.Flat
