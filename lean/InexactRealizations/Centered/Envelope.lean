import InexactRealizations.Analysis.Relative
import InexactRealizations.Probability.History

/-! The printed causal majorants in arbitrary Hilbert norm, in particular
the actual L2 norm of a stochastic execution. 
-/
namespace InexactRealizations.Centered
noncomputable section
open Polynomial InexactRealizations.Analysis
open scoped BigOperators
variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem query_envelope (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (L : ℝ) (hL : 0 ≤ L)
    (hH : ∀ v : E, ‖H v‖ ≤ L * ‖v‖) (initial : E) (noise : Fin N → E)
    (u : h.Execution H initial noise) (r t t0 : ℝ) (ht : 0 ≤ t) (htt0 : t ≤ t0)
    (hi : ‖initial‖ ≤ r) (hw : ∀ s, ‖noise s‖ ≤ t * ‖u.query s‖) (s : Fin N) :
    ‖u.query s‖ ≤ r * queryMajorant h L t0 s := by
  induction s using (measure (fun s : Fin N ↦ s.val)).wf.induction with
  | h s ih =>
    have ha (j : Fin N) (hj : j < s) :
        ‖u.answer j‖ ≤ (L + t0) * (r * queryMajorant h L t0 j) := by
      rw [u.answer_eq]
      calc
        _ ≤ L * ‖u.query j‖ + t0 * ‖u.query j‖ :=
          (norm_add_le _ _).trans (add_le_add (hH _) ((hw j).trans
            (mul_le_mul_of_nonneg_right htt0 (norm_nonneg _))))
        _ = (L + t0) * ‖u.query j‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (ih j hj) (add_nonneg hL (ht.trans htt0))
    calc
      _ ≤ r + ∑ j : Fin N, if j < s then |h.a s j| * ‖u.answer j‖ else 0 :=
        (query_norm_le h H initial noise u s).trans (add_le_add hi le_rfl)
      _ ≤ r + ∑ j : Fin N, if j < s then
          |h.a s j| * ((L + t0) * (r * queryMajorant h L t0 j)) else 0 := by
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro j _
        split_ifs with hj
        · exact mul_le_mul_of_nonneg_left (ha j hj) (abs_nonneg _)
        · exact le_rfl
      _ = _ := by
        rw [queryMajorant, mul_add, mul_one, Finset.mul_sum, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring

theorem deviation_envelope (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (L : ℝ) (hL : 0 ≤ L)
    (hH : ∀ v : E, ‖H v‖ ≤ L * ‖v‖) (initial : E) (noise : Fin N → E)
    (u : h.Execution H initial noise) (r t t0 : ℝ) (ht : 0 ≤ t) (htt0 : t ≤ t0)
    (hi : ‖initial‖ ≤ r) (hw : ∀ s, ‖noise s‖ ≤ t * ‖u.query s‖) (s : Fin N) :
    ‖u.query s - (aeval H (h.query s)) initial‖ ≤ t * r * deviationMajorant h L t0 s := by
  let v := h.run H initial (fun _ ↦ 0)
  have hc := query_envelope h H L hL hH initial noise u r t t0 ht htt0 hi hw
  have hn (j : Fin N) : ‖noise j‖ ≤ t * r * queryMajorant h L t0 j := by
    exact ((hw j).trans (mul_le_mul_of_nonneg_left (hc j) ht)).trans_eq (by ring)
  have hd (s : Fin N) : ‖u.query s - v.query s‖ ≤ t * r * deviationMajorant h L t0 s := by
    induction s using (measure (fun s : Fin N ↦ s.val)).wf.induction with
    | h s ih =>
      rw [query_difference h H initial noise u v s, norm_neg]
      calc
        _ ≤ ∑ j, ‖h.a s j • (H (u.query j - v.query j) + noise j)‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin N, if j < s then |h.a s j| *
            (L * (t * r * deviationMajorant h L t0 j) + t * r * queryMajorant h L t0 j) else 0 := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : j < s
          · simp only [hj, ite_true, norm_smul, Real.norm_eq_abs]
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact (norm_add_le _ _).trans (add_le_add
              ((hH _).trans (mul_le_mul_of_nonneg_left (ih j hj) hL)) (hn j))
          · simp only [hj, ite_false, h.triangular s j (le_of_not_gt hj), zero_smul, norm_zero, le_refl]
        _ = _ := by
          rw [deviationMajorant, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> ring
  simpa only [h.nominal_query H initial v] using hd s

end
end InexactRealizations.Centered
