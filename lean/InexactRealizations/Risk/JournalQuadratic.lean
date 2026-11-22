import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-! The exact constrained scalar minimization in current Theorem3.2,
including zero signal/noise. This is proved algebra, not a risk certificate. 
-/
namespace InexactRealizations.Risk.AllLinear
noncomputable section
open Set

def objective (A B c : ℝ) : ℝ := A * c ^ 2 + B * (1 - c) ^ 2

def value (A B e : ℝ) : ℝ :=
  if B * (1 - e) ≤ e * A then objective A B e else A * B / (A + B)

def shrink (A B e : ℝ) : ℝ := min 1 (A / ((A + B) * (1 - e)))

theorem completed_square (A B c : ℝ) (h : A + B ≠ 0) :
    objective A B c = A * B / (A + B) + (A + B) * (c - B / (A + B)) ^ 2 := by
  unfold objective
  field_simp
  ring

theorem objective_sub (A B c e : ℝ) :
    objective A B c - objective A B e = (c - e) * ((A + B) * (c + e) - 2 * B) := by
  unfold objective
  ring

theorem boundary_lower {A B e c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hec : e ≤ c) (hbind : B * (1 - e) ≤ e * A) : objective A B e ≤ objective A B c := by
  have hs := mul_nonneg (add_nonneg hA hB) (sub_nonneg.mpr hec)
  have hf : 0 ≤ (A + B) * (c + e) - 2 * B := by nlinarith only [hbind, hs]
  have hh := mul_nonneg (sub_nonneg.mpr hec) hf
  rw [← objective_sub] at hh
  exact sub_nonneg.mp hh

theorem interior_positive {A B e : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (he : 0 < e) (he₁ : e < 1) (hfree : ¬B * (1 - e) ≤ e * A) : 0 < A + B := by
  have hh : 0 < B * (1 - e) := (mul_nonneg he.le hA).trans_lt (lt_of_not_ge hfree)
  have hp : 0 < B := (mul_pos_iff_of_pos_right (sub_pos.mpr he₁)).mp hh
  exact add_pos_of_nonneg_of_pos hA hp

theorem value_lower {A B e c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he : 0 < e) (he₁ : e < 1) (hc : c ∈ Icc e 1) : value A B e ≤ objective A B c := by
  unfold value
  split_ifs with hb
  · exact boundary_lower hA hB hc.1 hb
  · have hs := interior_positive hA hB he he₁ hb
    rw [completed_square A B c hs.ne']
    exact le_add_of_nonneg_right (mul_nonneg hs.le (sq_nonneg _))

theorem value_attained {A B e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he : 0 < e) (he₁ : e < 1) :
    ∃ c ∈ Icc e 1, objective A B c = value A B e := by
  by_cases hb : B * (1 - e) ≤ e * A
  · exact ⟨e, ⟨le_rfl, he₁.le⟩, by simp only [value, ite_eq_left hb]⟩
  · have hs := interior_positive hA hB he he₁ hb
    have hlo : e < B / (A + B) := (lt_div_iff₀ hs).mpr (by nlinarith only [lt_of_not_ge hb])
    have hhi : B / (A + B) ≤ 1 := (div_le_one hs).mpr (by linarith only [hA])
    refine ⟨B / (A + B), ⟨hlo.le, hhi⟩, ?_⟩
    rw [value, ite_eq_right hb, completed_square A B _ hs.ne']
    simp

theorem value_isLeast {A B e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he : 0 < e) (he₁ : e < 1) :
    IsLeast (objective A B '' Icc e 1) (value A B e) := by
  obtain ⟨c, hc, hce⟩ := value_attained hA hB he he₁
  refine ⟨⟨c, hc, hce⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact value_lower hA hB he he₁ hx

theorem clipped_value_lower {A B e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he : 0 < e) (he₁ : e < 1) (c : ℝ) :
    value A B e ≤ A * (max e |c|) ^ 2 + B * (1 - c) ^ 2 := by
  have hM : 0 ≤ max e |c| := he.le.trans (le_max_left _ _)
  by_cases hlo : c < e
  · have hs := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ he.le hM).mpr (le_max_left _ _)) hA
    have hn := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (sub_nonneg.mpr he₁.le) (by linarith : 0 ≤ 1 - c)).mpr (by linarith : 1 - e ≤ 1 - c)) hB
    have hv := value_lower hA hB he he₁ (show e ∈ Icc e 1 from ⟨le_rfl, he₁.le⟩)
    unfold objective at hv
    linarith only [hv, hs, hn]
  · have hce : e ≤ c := le_of_not_gt hlo
    by_cases hhi : c ≤ 1
    · rw [abs_of_nonneg (he.le.trans hce), max_eq_right hce]
      exact value_lower hA hB he he₁ ⟨hce, hhi⟩
    · have hc : 1 ≤ max e |c| := (le_of_lt (lt_of_not_ge hhi)).trans ((le_abs_self c).trans (le_max_right _ _))
      have hs := mul_le_mul_of_nonneg_left ((sq_le_sq₀ zero_le_one hM).mpr hc) hA
      have hv := value_lower hA hB he he₁ (show (1 : ℝ) ∈ Icc e 1 from ⟨he₁.le, le_rfl⟩)
      norm_num only [objective, one_pow, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at hv
      nlinarith only [hv, hs, mul_nonneg hB (sq_nonneg (1 - c))]

theorem flat_attains_iff {A B e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he : 0 < e) (he₁ : e < 1) :
    objective A B e = value A B e ↔ B * (1 - e) ≤ e * A := by
  constructor
  · intro hh
    by_contra hb
    have hs := interior_positive hA hB he he₁ hb
    have hlo : e < B / (A + B) := (lt_div_iff₀ hs).mpr (by nlinarith only [lt_of_not_ge hb])
    rw [value, ite_eq_right hb, completed_square A B e hs.ne'] at hh
    have hpos := mul_pos hs (sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt hlo)))
    linarith only [hh, hpos]
  · intro hb
    simp only [value, ite_eq_left hb]

theorem flat_multiplicative_bound {A B e : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (he : 0 < e) (_he₁ : e < 1) :
    objective A B e ≤ (1 + B / A) * value A B e := by
  by_cases hb : B * (1 - e) ≤ e * A
  · rw [value, ite_eq_left hb]
    exact le_mul_of_one_le_left (add_nonneg (mul_nonneg hA.le (sq_nonneg _))
      (mul_nonneg hB (sq_nonneg _))) (by have hh := div_nonneg hB hA.le; linarith only [hh])
  · have hs : 0 < A + B := add_pos_of_pos_of_nonneg hA hB
    have hid : (1 + B / A) * value A B e = B := by
      rw [value, ite_eq_right hb]
      field_simp
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left (le_of_not_ge hb) he.le
    have hBe := mul_nonneg hB he.le
    unfold objective
    nlinarith only [hh, hBe]

theorem shrink_nonneg {A B e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (he : e < 1) :
    0 ≤ shrink A B e :=
  le_min zero_le_one (div_nonneg hA (mul_nonneg (add_nonneg hA hB) (sub_nonneg.mpr he.le)))

theorem shrink_attains {A B e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (_he : 0 < e) (he₁ : e < 1) :
    objective A B (1 - shrink A B e * (1 - e)) = value A B e := by
  by_cases hz : A + B = 0
  · have hAz : A = 0 := by linarith
    have hBz : B = 0 := by linarith
    simp [hAz, hBz, objective, value]
  · have hs : 0 < A + B := lt_of_le_of_ne (add_nonneg hA hB) (Ne.symm hz)
    have hd : 0 < (A + B) * (1 - e) := mul_pos hs (sub_pos.mpr he₁)
    by_cases hb : B * (1 - e) ≤ e * A
    · have hq : 1 ≤ A / ((A + B) * (1 - e)) := (le_div_iff₀ hd).mpr (by nlinarith only [hb])
      simp only [shrink, min_eq_left hq, one_mul, sub_sub_cancel, value, ite_eq_left hb]
    · have hq : A / ((A + B) * (1 - e)) ≤ 1 := (div_le_one hd).mpr (by nlinarith only [lt_of_not_ge hb])
      have hc : 1 - shrink A B e * (1 - e) = B / (A + B) := by
        rw [shrink, min_eq_right hq]
        field_simp [hs.ne', (sub_pos.mpr he₁).ne']
        ring
      rw [hc, value, ite_eq_right hb, completed_square A B _ hs.ne']
      simp

end
end InexactRealizations.Risk.AllLinear
