import InexactRealizations.Probability.History

/-! The random F0-measurable minimizer model of current Theorem3.2.
Conditional centering removes cross terms with a random initial state;
neither independence of the errors nor a posterior-risk bound is assumed. 
-/
namespace InexactRealizations.Probability.MartingaleDifferences
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {N : ℕ} {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}
  (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ) [IsProbabilityMeasure μ]

include hw

theorem integral_norm_sq_randomInitial (V : Ω → E) (hV : StronglyMeasurable[𝓕 0] V)
    (hV₂ : MemLp V 2 μ) :
    (∫ ω, ‖V ω + ∑ s ∈ Finset.range N, w s ω‖ ^ 2 ∂μ) =
      (∫ ω, ‖V ω‖ ^ 2 ∂μ) + ∑ s ∈ Finset.range N, ∫ ω, ‖w s ω‖ ^ 2 ∂μ := by
  have hp (n : ℕ) (hn : n ≤ N) :
      (∫ ω, ‖V ω + ∑ s ∈ Finset.range n, w s ω‖ ^ 2 ∂μ) =
        (∫ ω, ‖V ω‖ ^ 2 ∂μ) + ∑ s ∈ Finset.range n, ∫ ω, ‖w s ω‖ ^ 2 ∂μ := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h₂ := hw.squareIntegrable n (by omega)
      have hleft : MemLp (fun ω ↦ V ω + ∑ s ∈ Finset.range n, w s ω) 2 μ :=
        hV₂.add (hw.memLp_sum n (by omega))
      have hm : StronglyMeasurable[𝓕 n] (fun ω ↦ V ω + ∑ s ∈ Finset.range n, w s ω) := by
        apply (hV.mono (𝓕.mono (Nat.zero_le n))).add
        apply Finset.stronglyMeasurable_fun_sum (Finset.range n)
        intro s hs
        have hsn := Finset.mem_range.mp hs
        exact (hw.adapted s (by omega)).mono (𝓕.mono (by omega))
      have hcross : (∫ ω, inner ℝ (V ω + ∑ s ∈ Finset.range n, w s ω) (w n ω) ∂μ) = 0 :=
        integral_inner_eq_zero_of_condExp (𝓕.le n) hm hleft h₂ (hw.centered n (by omega))
      have hli := hleft.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
      have hri := h₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
      have hci := (integrable_inner_of_memLp hleft h₂).const_mul 2
      have he : (fun ω ↦ ‖V ω + ∑ s ∈ Finset.range (n + 1), w s ω‖ ^ 2) =
          fun ω ↦ ‖V ω + ∑ s ∈ Finset.range n, w s ω‖ ^ 2 +
            2 * inner ℝ (V ω + ∑ s ∈ Finset.range n, w s ω) (w n ω) + ‖w n ω‖ ^ 2 := by
        funext ω
        rw [Finset.sum_range_succ, ← add_assoc, norm_add_sq_real]
      rw [he]
      have hsplit := integral_add (hli.add hci) hri
      dsimp only [Pi.add_apply] at hsplit
      rw [hsplit]
      have hsplit₂ := integral_add hli hci
      dsimp only [Pi.add_apply] at hsplit₂
      rw [hsplit₂, integral_const_mul, hcross]
      simp only [mul_zero, add_zero]
      rw [ih (by omega), Finset.sum_range_succ]
      ring
  exact hp N le_rfl

theorem integral_norm_sq_randomInitial_response (V : Ω → F) (hV : StronglyMeasurable[𝓕 0] V)
    (hV₂ : MemLp V 2 μ) (L : Fin N → E →L[ℝ] F) :
    (∫ ω, ‖V ω + ∑ s : Fin N, L s (w s.val ω)‖ ^ 2 ∂μ) =
      (∫ ω, ‖V ω‖ ^ 2 ∂μ) + ∑ s : Fin N, ∫ ω, ‖L s (w s.val ω)‖ ^ 2 ∂μ := by
  have hh := (hw.map (responseExtension L)).integral_norm_sq_randomInitial V hV hV₂
  simpa only [Finset.sum_range, responseExtension, Fin.isLt, dite_true] using hh

end
end InexactRealizations.Probability.MartingaleDifferences

namespace InexactRealizations.History
noncomputable section
open MeasureTheory
open scoped BigOperators
variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {N : ℕ} {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E} [IsProbabilityMeasure μ]

theorem integral_randomInitial_stochasticOutput (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (V : Ω → E) (hV : StronglyMeasurable[𝓕 0] V) (hV₂ : MemLp V 2 μ)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ) :
    (∫ ω, ‖h.stochasticOutput H (V ω) w ω‖ ^ 2 ∂μ) =
      (∫ ω, ‖(Polynomial.aeval H h.terminal) (V ω)‖ ^ 2 ∂μ) +
        ∑ s : Fin N, ∫ ω, ‖h.responseOperator H s (w s.val ω)‖ ^ 2 ∂μ := by
  let B : E →L[ℝ] E := (Polynomial.aeval H h.terminal).toContinuousLinearMap
  simp_rw [stochasticOutput_response]
  exact hw.integral_norm_sq_randomInitial_response (fun ω ↦ B (V ω))
    (B.continuous.comp_stronglyMeasurable hV) (hV₂.continuousLinearMap_comp B) (h.responseOperator H)

end
end InexactRealizations.History
