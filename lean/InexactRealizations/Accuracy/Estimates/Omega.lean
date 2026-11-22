import InexactRealizations.Algorithms.AveragedBalancedBounds

/-! The quantitative parity-weight estimates used in the proof of
Only the ranges actually used by the printed algorithm occur. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
open InexactRealizations.Balanced

theorem omega_drop_exact {N s : ℕ} (hN : 2 ≤ N) (hs : 1 ≤ s) :
    omega N s - omega N (s + 2) =
      if Even N then 2 / (N : ℝ) else
      if Even s then 2 * ((N : ℝ) + 1) / ((N : ℝ) ^ 2 + 1) else 2 / ((N : ℝ) + 1) := by
  have hnR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases hs1 : s = 1
  · subst s
    by_cases hn : Even N
    · simp only [omega, show (1 : ℕ) < 2 by decide, ite_true,
        show ¬(3 : ℕ) < 2 by decide, ite_false, hn, Nat.cast_one]
      norm_num
      field_simp [(show (0 : ℝ) < N by linarith).ne']
      ring
    · simp only [omega, show (1 : ℕ) < 2 by decide, ite_true,
        show ¬(3 : ℕ) < 2 by decide, ite_false, hn, show ¬Even (1 : ℕ) by decide,
        show ¬Even (3 : ℕ) by decide, Nat.cast_one]
      field_simp [(show (0 : ℝ) < (N : ℝ) + 1 by linarith).ne']
      ring
  · have hsmall : ¬s < 2 := by omega
    have hlarge : ¬s + 2 < 2 := by omega
    have hp : Even (s + 2) ↔ Even s := by simp [Nat.even_add]
    have hm : (s + 2) % 2 = s % 2 := by omega
    unfold omega
    simp only [hsmall, hlarge, ite_false, hp, hm, Nat.cast_add, Nat.cast_ofNat]
    split_ifs <;> ring

theorem omega_drop_bounds {N s : ℕ} (hN : 2 ≤ N) (hs : 1 ≤ s) :
    2 / ((N : ℝ) + 1) ≤ omega N s - omega N (s + 2) ∧
      omega N s - omega N (s + 2) ≤ 2 / ((N : ℝ) - 1) := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  rw [omega_drop_exact hN hs]
  split_ifs
  · constructor <;> apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr <;> nlinarith
  · constructor
    · apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
      nlinarith
    · apply (div_le_div_iff₀ (by positivity) (by linarith)).mpr
      nlinarith
  · constructor
    · exact le_rfl
    · apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
      nlinarith

theorem omega_next_bounds {N s : ℕ} (hN : 2 ≤ N) (hs : s + 2 < N) :
    ((N : ℝ) - 1 - s) / N ≤ omega N (s + 2) ∧
      omega N (s + 2) ≤ ((N : ℝ) - s) / N := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsR : (s : ℝ) + 2 < N := by exact_mod_cast hs
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hlarge : ¬s + 2 < 2 := by omega
  have hm : (s + 2) % 2 = s % 2 := by omega
  have hp : Even (s + 2) ↔ Even s := by simp [Nat.even_add]
  unfold omega
  simp only [hlarge, ite_false, hp, hm, Nat.cast_add, Nat.cast_ofNat]
  split_ifs
  · have hr : ((s % 2 : ℕ) : ℝ) = 0 ∨ ((s % 2 : ℕ) : ℝ) = 1 := by
      have hh : s % 2 = 0 ∨ s % 2 = 1 := by omega
      rcases hh with hh | hh <;> simp [hh]
    constructor <;> apply (div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < N)).mpr <;>
      rcases hr with hr | hr <;> linarith
  · constructor
    · apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
      nlinarith
    · apply (div_le_div_iff₀ (by positivity) (by linarith)).mpr
      nlinarith
  · constructor
    · apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
      nlinarith
    · apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
      nlinarith

end
end InexactRealizations.Accuracy
