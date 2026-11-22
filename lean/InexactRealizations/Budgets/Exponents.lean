import InexactRealizations.Budgets.Norm

/-! Every gamma>=1 has its printed conjugate exponent, including both
endpoints. The constant call profile has the exact N^(-1/gamma) norm. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open scoped BigOperators ENNReal NNReal

def dualExponent (p : ℝ≥0∞) : ℝ≥0∞ := (1 - p⁻¹)⁻¹

theorem holder_dualExponent (p : ℝ≥0∞) (hp : 1 ≤ p) : p.HolderConjugate (dualExponent p) := by
  constructor
  simp only [dualExponent, inv_inv, inv_one]
  have hpinv : p⁻¹ ≤ 1 := by simpa only [inv_one] using ENNReal.inv_le_inv.mpr hp
  simpa only [add_comm] using tsub_add_cancel_of_le hpinv

@[simp] theorem dualExponent_one : dualExponent 1 = ∞ := by simp [dualExponent]
@[simp] theorem dualExponent_top : dualExponent ∞ = 1 := by simp [dualExponent]

theorem inverse_conjugates {p q : ℝ≥0∞} [p.HolderConjugate q] :
    (1 / p).toReal + (1 / q).toReal = 1 := by
  have hh := congrArg ENNReal.toReal (ENNReal.HolderConjugate.inv_add_inv_eq_one p q)
  have hp0 := ENNReal.HolderConjugate.ne_zero p q
  have hq0 := ENNReal.HolderConjugate.ne_zero q p
  simpa only [one_div, ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hp0) (ENNReal.inv_ne_top.mpr hq0),
    ENNReal.toReal_one] using hh

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem callNorm_const {p : ℝ≥0∞} [Fact (1 ≤ p)] (c : ℝ) :
    callNorm p (fun _ : ι ↦ c) = (Fintype.card ι : ℝ) ^ (1 / p).toReal * |c| := by
  have hh := PiLp.norm_toLp_const' (p := p) (ι := ι) c
  convert hh using 1
  all_goals norm_cast

theorem uniform_budget {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Budget p (fun _ : ι ↦ (Fintype.card ι : ℝ) ^ (-(1 / p).toReal)) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  constructor
  · intro i
    exact Real.rpow_nonneg hn.le _
  · rw [callNorm_const, abs_of_nonneg (Real.rpow_nonneg hn.le _), ← Real.rpow_add hn]
    simp only [add_neg_cancel, Real.rpow_zero, le_refl]

end
end InexactRealizations.Budgets
