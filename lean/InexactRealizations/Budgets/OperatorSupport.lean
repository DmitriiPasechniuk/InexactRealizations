import InexactRealizations.Budgets.Symmetric

/-! Exact directional operator support for every call exponent. The
maximizing maps are actual symmetric contractions, including zero factors. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial
open scoped BigOperators ENNReal NNReal
variable {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem operator_support_upper (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (D : Fin N → E →ₗ[ℝ] E) (delta : Fin N → ℝ) (hd : Budget p delta)
    (hD : ∀ s, ‖(D s).toContinuousLinearMap‖ ≤ delta s) (e v : E) :
    inner ℝ e (h.firstVariation H D v) ≤
      callNorm q (fun s ↦ ‖(aeval H (h.response s)) e‖ * ‖(aeval H (h.query s)) v‖) := by
  unfold InexactRealizations.History.firstVariation InexactRealizations.History.variationNoise
  rw [inner_sum]
  have hb (s : Fin N) :
      inner ℝ e ((aeval H (h.response s)) (D s ((aeval H (h.query s)) v))) ≤
        delta s * (‖(aeval H (h.response s)) e‖ * ‖(aeval H (h.query s)) v‖) := by
    rw [← polynomial_symmetric H hH (h.response s) e]
    have hact := ((D s).toContinuousLinearMap.le_opNorm ((aeval H (h.query s)) v)).trans
      (mul_le_mul_of_nonneg_right (hD s) (norm_nonneg _))
    exact (real_inner_le_norm _ _).trans (by
      have hh := mul_le_mul_of_nonneg_left hact (norm_nonneg ((aeval H (h.response s)) e))
      convert hh using 1
      · rfl
      · ring)
  exact (Finset.sum_le_sum (fun s _ ↦ hb s)).trans
    (holder_budget _ delta (fun s ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)) hd)

set_option maxHeartbeats 1000000 in
theorem operator_support_attained [Nonempty (Fin N)] (h : InexactRealizations.History N)
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (e v : E) (he : ‖e‖ = 1) :
    ∃ (D : Fin N → E →ₗ[ℝ] E) (delta : Fin N → ℝ),
      Budget p delta ∧ (∀ s, (D s).IsSymmetric) ∧
      (∀ s, ‖(D s).toContinuousLinearMap‖ ≤ delta s) ∧
      inner ℝ e (h.firstVariation H D v) =
        callNorm q (fun s ↦ ‖(aeval H (h.response s)) e‖ * ‖(aeval H (h.query s)) v‖) := by
  classical
  obtain ⟨delta, hd, hvalue⟩ := exists_holder_budget (p := p) (q := q)
    (fun s : Fin N ↦ ‖(aeval H (h.response s)) e‖ * ‖(aeval H (h.query s)) v‖)
    (fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
  let w := fun s : Fin N ↦ (delta s * ‖(aeval H (h.query s)) v‖) •
    unitDirection ((aeval H (h.response s)) e) e
  have hw (s : Fin N) : ‖w s‖ ≤ delta s * ‖(aeval H (h.query s)) v‖ := by
    simp only [w, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hd.1 s) (norm_nonneg _)), unitDirection_norm _ _ he, mul_one, le_refl]
  choose D hsym hmap hD using fun s ↦ exists_symmetric_interpolation
    ((aeval H (h.query s)) v) (w s) (delta s) (hd.1 s) (hw s)
  refine ⟨D, delta, hd, hsym, hD, ?_⟩
  unfold InexactRealizations.History.firstVariation InexactRealizations.History.variationNoise
  rw [inner_sum, ← hvalue]
  apply Finset.sum_congr rfl
  intro s _
  rw [hmap s, ← polynomial_symmetric H hH (h.response s) e]
  simp only [w, inner_smul_right, inner_unitDirection]
  ring

omit [FiniteDimensional ℝ E] in
theorem firstVariation_smul (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (D : Fin N → E →ₗ[ℝ] E) (v : E) (c : ℝ) :
    h.firstVariation H D (c • v) = c • h.firstVariation H D v := by
  simp only [InexactRealizations.History.firstVariation, InexactRealizations.History.variationNoise,
    map_smul, Finset.smul_sum]

end
end InexactRealizations.Budgets
