import InexactRealizations.Budgets.Operator
import InexactRealizations.Budgets.Remainder

/-! A relative error at an actual query is an actual bounded linear
perturbation. The resulting first-variation remainder is uniform over
dimensions, queries and feasible call budgets. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial InexactRealizations.Analysis
open scoped BigOperators ENNReal NNReal
variable {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_linear_interpolation (v w : E) (c : ℝ) (hc : 0 ≤ c)
    (hw : ‖w‖ ≤ c * ‖v‖) :
    ∃ D : E →ₗ[ℝ] E, D v = w ∧ ‖D.toContinuousLinearMap‖ ≤ c := by
  by_cases hv : v = 0
  · have hw0 : w = 0 := norm_eq_zero.mp (by simpa [hv] using hw)
    exact ⟨0, by simp [hw0], by simpa using hc⟩
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let D : E →L[ℝ] E := (‖v‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ w v
    refine ⟨D.toLinearMap, ?_, ?_⟩
    · change (‖v‖ ^ 2)⁻¹ • (inner ℝ v v • w) = w
      rw [real_inner_self_eq_norm_sq, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hn.ne')]
      exact one_smul ℝ w
    · change ‖D‖ ≤ c
      dsimp only [D]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hn)),
        InnerProductSpace.norm_rankOne]
      apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw hn.le)
        (inv_nonneg.mpr (sq_nonneg ‖v‖))).trans
      have he : (‖v‖ ^ 2)⁻¹ * (c * ‖v‖ * ‖v‖) = c := by field_simp
      exact he.le

include q in
theorem relative_linearization (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (initial : E) (noise : Fin N → E)
    (u : h.Execution H initial noise) (t t0 : ℝ) (ht : 0 < t) (htt0 : t ≤ t0)
    (hi : ‖initial‖ ≤ 1) (delta : Fin N → ℝ)
    (hw : RelativeErrors p h H initial noise u t delta) (P : Fin N → ℝ)
    (hP : InexactRealizations.Risk.ResponseBounds h I P) :
    ∃ D : Fin N → E →ₗ[ℝ] E,
      (∀ s, ‖(D s).toContinuousLinearMap‖ ≤ delta s) ∧
      ‖(u.output - (aeval H h.terminal) initial) - t • h.firstVariation H D initial‖ ≤
        t ^ 2 * ∑ s, P s * deviationMajorant h I.L t0 s := by
  classical
  let : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have hb (s : Fin N) : ‖t⁻¹ • noise s‖ ≤ delta s * ‖u.query s‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    have hh := mul_le_mul_of_nonneg_left (hw.2.2 s) (inv_pos.mpr ht).le
    convert hh using 1; field_simp
  choose D hmap hD using fun s ↦
    exists_linear_interpolation (u.query s) (t⁻¹ • noise s) (delta s) (hw.1 s) (hb s)
  refine ⟨D, hD, ?_⟩
  have hn (s : Fin N) : noise s = t • D s (u.query s) := by
    rw [hmap s, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hd := query_deviation_bound h I H hH initial noise u 1 t t0 zero_le_one
    ht.le htt0 hi delta hw
  have hres (s : Fin N) :
      ‖noise s - t • D s ((aeval H (h.query s)) initial)‖ ≤
        t ^ 2 * deviationMajorant h I.L t0 s := by
    rw [hn s, ← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hdelta : delta s ≤ 1 := (show Budget p delta from ⟨hw.1, hw.2.1⟩).coordinate s
    have hDs : ‖(D s).toContinuousLinearMap‖ ≤ 1 := (hD s).trans hdelta
    have hact := ((D s).toContinuousLinearMap.le_opNorm
      (u.query s - (aeval H (h.query s)) initial)).trans
      (mul_le_mul_of_nonneg_right hDs (norm_nonneg _))
    simp only [one_mul, mul_one] at hact hd
    calc
      _ ≤ t * (t * deviationMajorant h I.L t0 s) :=
        mul_le_mul_of_nonneg_left (hact.trans (hd s)) ht.le
      _ = _ := by ring
  have he : (u.output - (aeval H h.terminal) initial) - t • h.firstVariation H D initial =
      ∑ s, (aeval H (h.response s))
        (noise s - t • D s ((aeval H (h.query s)) initial)) := by
    rw [h.physical_response H initial noise u, add_sub_cancel_left,
      InexactRealizations.History.firstVariation, Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    simp only [InexactRealizations.History.variationNoise, map_sub, map_smul]
  rw [he]
  calc
    _ ≤ ∑ s, P s * ‖noise s - t • D s ((aeval H (h.query s)) initial)‖ :=
      norm_sum_le_energy _ _ (fun s ↦
        polynomial_action_bound I H hH _ _ (hP.1 s) (hP.2 s) _)
    _ ≤ ∑ s, P s * (t ^ 2 * deviationMajorant h I.L t0 s) :=
      Finset.sum_le_sum (fun s _ ↦ mul_le_mul_of_nonneg_left (hres s) (hP.1 s))
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring

end
end InexactRealizations.Budgets
