import InexactRealizations.Budgets.Interpolation
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Symmetric perturbations suffice without enlarging the spectral interval:
a scaled orthogonal reflection interpolates any one vector and its image. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial
open scoped BigOperators ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_symmetric_interpolation (v w : E) (c : ℝ) (hc : 0 ≤ c)
    (hw : ‖w‖ ≤ c * ‖v‖) :
    ∃ D : E →ₗ[ℝ] E, D.IsSymmetric ∧ D v = w ∧ ‖D.toContinuousLinearMap‖ ≤ c := by
  by_cases hv : v = 0
  · have hw0 : w = 0 := norm_eq_zero.mp (by simpa [hv] using hw)
    exact ⟨0, LinearMap.IsSymmetric.zero, by simp [hw0], by simpa using hc⟩
  by_cases hw0 : w = 0
  · exact ⟨0, LinearMap.IsSymmetric.zero, by simp [hw0], by simpa using hc⟩
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hwp : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  let z := (‖v‖ / ‖w‖) • w
  have hz : ‖z‖ = ‖v‖ := by
    simp only [z, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hvp hwp)]
    exact div_mul_cancel₀ _ hwp.ne'
  let R := Submodule.reflection (ℝ ∙ (v - z))ᗮ
  have hR : R.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℝ (R x) y = inner ℝ x (R y)
    exact R.inner_map_eq_flip x y
  have hRv : R v = z := Submodule.reflection_sub hz.symm
  let a := ‖w‖ / ‖v‖
  have ha : 0 ≤ a := (div_pos hwp hvp).le
  refine ⟨a • R.toLinearMap, hR.smul (by simp), ?_, ?_⟩
  · change a • R v = w
    rw [hRv]
    dsimp only [a, z]
    rw [smul_smul]
    have he : ‖w‖ / ‖v‖ * (‖v‖ / ‖w‖) = 1 := by field_simp
    rw [he, one_smul]
  · have hbound : ‖(a • R.toLinearMap).toContinuousLinearMap‖ ≤ a := by
      apply ContinuousLinearMap.opNorm_le_bound _ ha
      intro x
      change ‖a • R x‖ ≤ a * ‖x‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, R.norm_map]
    exact hbound.trans ((div_le_iff₀ hvp).mpr hw)

variable {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]

include q in
theorem operatorGain_symmetric (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) :
    operatorGain p h I true = operatorGain p h I false := by
  classical
  apply le_antisymm
  · apply csSup_le (operatorValues_nonempty (p := p) (q := q) h I true)
    intro v hv
    cases hv with
    | execution E H hH D delta hd hD hsym initial hi =>
      exact le_csSup (operatorValues_bddAbove (p := p) (q := q) h I false)
        (OperatorValue.execution E H hH D delta hd hD (by simp) initial hi)
  · apply csSup_le (operatorValues_nonempty (p := p) (q := q) h I false)
    intro v hv
    cases hv with
    | execution E H hH D delta hd hD hsym initial hi =>
      have hb (s : Fin N) : ‖D s ((aeval H (h.query s)) initial)‖ ≤
          delta s * ‖(aeval H (h.query s)) initial‖ :=
        ((D s).toContinuousLinearMap.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hD s) (norm_nonneg _))
      choose A hAsym hAv hAnorm using fun s ↦ exists_symmetric_interpolation
        ((aeval H (h.query s)) initial) (D s ((aeval H (h.query s)) initial))
        (delta s) (hd.1 s) (hb s)
      have he : h.firstVariation H D initial = h.firstVariation H A initial := by
        unfold InexactRealizations.History.firstVariation InexactRealizations.History.variationNoise
        simp_rw [hAv]
      rw [he]
      exact le_csSup (operatorValues_bddAbove (p := p) (q := q) h I true)
        (OperatorValue.execution E H hH A delta hd hAnorm (fun _ ↦ hAsym) initial hi)

end
end InexactRealizations.Budgets
