import InexactRealizations.Budgets.Norm
import InexactRealizations.Analysis.Relative

/-! The printed finite causal majorants hold for every lp call budget,
including p=1 and p=infinity and arbitrary adapted error choices. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial InexactRealizations.Analysis
open scoped BigOperators ENNReal NNReal
variable {N : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def RelativeErrors (p : ℝ≥0∞) (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (noise : Fin N → E) (u : h.Execution H initial noise) (t : ℝ) (delta : Fin N → ℝ) : Prop :=
  (∀ s, 0 ≤ delta s) ∧ callNorm p delta ≤ 1 ∧ ∀ s, ‖noise s‖ ≤ t * delta s * ‖u.query s‖

theorem actual_query_bound (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (initial : E) (noise : Fin N → E)
    (u : h.Execution H initial noise) (r t t0 : ℝ) (_hr : 0 ≤ r)
    (ht : 0 ≤ t) (htt0 : t ≤ t0) (hi : ‖initial‖ ≤ r) (δ : Fin N → ℝ)
    (hw : RelativeErrors p h H initial noise u t δ) (s : Fin N) :
    ‖u.query s‖ ≤ r * queryMajorant h I.L t0 s := by
  have hL : 0 ≤ I.L := (I.mu_pos.trans I.mu_lt_L).le
  induction s using (measure (fun s : Fin N => s.val)).wf.induction with
  | h s ih =>
    have ha (j : Fin N) (hj : j < s) :
        ‖u.answer j‖ ≤ (I.L + t0) * (r * queryMajorant h I.L t0 j) := by
      have hd : δ j ≤ 1 := (show Budget p δ from ⟨hw.1, hw.2.1⟩).coordinate j
      have hn : ‖noise j‖ ≤ t0 * ‖u.query j‖ := by
        exact (hw.2.2 j).trans (mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left hd ht).trans (by simpa using htt0)) (norm_nonneg _))
      rw [u.answer_eq]
      calc
        _ ≤ I.L * ‖u.query j‖ + t0 * ‖u.query j‖ :=
          (norm_add_le _ _).trans (add_le_add (hessian_action_bound I H hH _) hn)
        _ = (I.L + t0) * ‖u.query j‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (ih j hj) (add_nonneg hL (ht.trans htt0))
    calc
      _ ≤ r + ∑ j : Fin N, if j < s then |h.a s j| * ‖u.answer j‖ else 0 :=
        (query_norm_le h H initial noise u s).trans (add_le_add hi le_rfl)
      _ ≤ r + ∑ j : Fin N, if j < s then
          |h.a s j| * ((I.L + t0) * (r * queryMajorant h I.L t0 j)) else 0 := by
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

theorem query_deviation_bound (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (initial : E) (noise : Fin N → E)
    (u : h.Execution H initial noise) (r t t0 : ℝ) (hr : 0 ≤ r)
    (ht : 0 ≤ t) (htt0 : t ≤ t0) (hi : ‖initial‖ ≤ r) (δ : Fin N → ℝ)
    (hw : RelativeErrors p h H initial noise u t δ) (s : Fin N) :
    ‖u.query s - (aeval H (h.query s)) initial‖ ≤
      t * r * deviationMajorant h I.L t0 s := by
  let v := h.run H initial (fun _ => 0)
  have hL : 0 ≤ I.L := (I.mu_pos.trans I.mu_lt_L).le
  have hc := actual_query_bound h I H hH initial noise u r t t0 hr ht htt0 hi δ hw
  have hn (j : Fin N) : ‖noise j‖ ≤ t * r * queryMajorant h I.L t0 j := by
    have hd : δ j ≤ 1 := (show Budget p δ from ⟨hw.1, hw.2.1⟩).coordinate j
    calc
      _ ≤ t * δ j * ‖u.query j‖ := hw.2.2 j
      _ ≤ t * ‖u.query j‖ := mul_le_mul_of_nonneg_right
        (by simpa using mul_le_mul_of_nonneg_left hd ht) (norm_nonneg _)
      _ ≤ t * (r * queryMajorant h I.L t0 j) := mul_le_mul_of_nonneg_left (hc j) ht
      _ = _ := by ring
  have hd (s : Fin N) : ‖u.query s - v.query s‖ ≤ t * r * deviationMajorant h I.L t0 s := by
    induction s using (measure (fun s : Fin N => s.val)).wf.induction with
    | h s ih =>
      rw [query_difference h H initial noise u v s, norm_neg]
      calc
        _ ≤ ∑ j, ‖h.a s j • (H (u.query j - v.query j) + noise j)‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin N, if j < s then |h.a s j| *
            (I.L * (t * r * deviationMajorant h I.L t0 j) +
              t * r * queryMajorant h I.L t0 j) else 0 := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : j < s
          · simp only [hj, ite_true, norm_smul, Real.norm_eq_abs]
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact (norm_add_le _ _).trans (add_le_add
              ((hessian_action_bound I H hH _).trans
                (mul_le_mul_of_nonneg_left (ih j hj) hL)) (hn j))
          · simp only [hj, ite_false, h.triangular s j (le_of_not_gt hj), zero_smul,
              norm_zero, le_refl]
        _ = _ := by
          rw [deviationMajorant, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> ring
  simpa only [h.nominal_query H initial v] using hd s

end
end InexactRealizations.Budgets
