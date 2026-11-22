import InexactRealizations.Balanced.Basis

/-! Literal ratio preparation in the current nine-vector.
The earlier prediction program uses different preparation; no equivalence
with that program is assumed here. 
-/
namespace InexactRealizations.Algorithms.AveragedBalanced
noncomputable section
open Polynomial Polynomial.Chebyshev
open InexactRealizations.Balanced

def ratio (I : InexactRealizations.Operators.SpectralInterval) : ℕ → ℝ
  | 0 => 1 / I.eta
  | j + 1 => 1 / (2 * I.eta - ratio I j)

theorem ratio_unit (I : InexactRealizations.Operators.SpectralInterval) (j : ℕ) :
    0 < ratio I j ∧ ratio I j < 1 := by
  induction j with
  | zero =>
    simp only [ratio]
    exact ⟨one_div_pos.mpr (lt_trans zero_lt_one I.eta_gt_one),
      (div_lt_one (lt_trans zero_lt_one I.eta_gt_one)).mpr I.eta_gt_one⟩
  | succ j ih =>
    have hd : 1 < 2 * I.eta - ratio I j := by linarith [I.eta_gt_one]
    simp only [ratio]
    exact ⟨one_div_pos.mpr (by linarith), (div_lt_one (by linarith)).mpr hd⟩

theorem ratio_eq (I : InexactRealizations.Operators.SpectralInterval) (j : ℕ) :
    ratio I j = I.den j / I.den (j + 1) := by
  induction j with
  | zero => simp [ratio]
  | succ j ih =>
    have he : 2 * I.eta - I.den j / I.den (j + 1) = I.den (j + 2) / I.den (j + 1) := by
      rw [I.den_add_two]
      field_simp [I.den_ne (j + 1)]
    rw [ratio, ih, he]
    field_simp [I.den_ne (j + 1), I.den_ne (j + 2)]

theorem den_strictMono (I : InexactRealizations.Operators.SpectralInterval) : StrictMono I.den := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hh := (ratio_unit I j).2
  rw [ratio_eq] at hh
  exact (div_lt_one (I.den_pos (j + 1))).mp hh

theorem ratio_denominator (I : InexactRealizations.Operators.SpectralInterval) (j : ℕ) :
    1 < 2 * I.eta - ratio I j := by linarith [(ratio_unit I j).2, I.eta_gt_one]

def zeta (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | s + 2 => omega N (s + 2) + (zeta I N s - omega N (s + 2)) * ratio I s * ratio I (s + 1)

theorem normalizer_step (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    normalizer I N (s + 2) = normalizer I N s + omega N (s + 2) * (I.den (s + 2) - I.den s) :=
  normalizer_add_two I N s

theorem zeta_eq (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    zeta I N s = normalizer I N s / I.den s := by
  induction s using Nat.twoStepInduction with
  | zero => simp [zeta]
  | one => simp [zeta, (lt_trans zero_lt_one I.eta_gt_one).ne']
  | more s ih _ =>
    rw [zeta, ih, ratio_eq, ratio_eq, normalizer_step]
    field_simp [I.den_ne s, I.den_ne (s + 1), I.den_ne (s + 2)]
    ring

theorem normalizer_le_den (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    normalizer I N s ≤ I.den s := by
  induction s using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more s ih _ =>
    have hprev := ih (by omega : s < N)
    have hw := omega_le_one hN hs
    have hdiff : 0 ≤ I.den (s + 2) - I.den s :=
      sub_nonneg.mpr ((den_strictMono I).monotone (by omega))
    have hm := mul_le_mul_of_nonneg_right hw hdiff
    rw [normalizer_step]
    linarith

theorem normalizer_ge_top (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    omega N s * I.den s ≤ normalizer I N s := by
  have hr := remainder_eval_ge_mass hN hs I.eta_gt_one.le
  have hw := omega_le_one hN hs
  have hn : 0 ≤ (remainder N s).eval I.eta := by linarith
  unfold normalizer psi
  simp only [eval_add, eval_mul, eval_C]
  exact le_add_of_nonneg_left hn

theorem zeta_unit (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    0 < zeta I N s ∧ zeta I N s ≤ 1 := by
  rw [zeta_eq]
  exact ⟨div_pos (normalizer_pos I hN hs) (I.den_pos s),
    (div_le_one (I.den_pos s)).mpr (normalizer_le_den I hN hs)⟩

theorem omega_le_zeta (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    omega N s ≤ zeta I N s := by
  rw [zeta_eq]
  exact (le_div_iff₀ (I.den_pos s)).mpr (normalizer_ge_top I hN hs)

theorem omega_strict_drop {N s : ℕ} (hN : 2 ≤ N) (hs : 2 ≤ s) (_hsN : s + 2 < N) :
    omega N (s + 2) < omega N s := by
  have hsmall : ¬s < 2 := by omega
  have hlarge : ¬s + 2 < 2 := by omega
  have hp : Even (s + 2) ↔ Even s := by simp [Nat.even_add]
  have hm : (s + 2) % 2 = s % 2 := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold omega
  simp only [hsmall, hlarge, ite_false, hp, hm, Nat.cast_add, Nat.cast_ofNat]
  split_ifs
  · exact (div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < N)).mpr (by linarith)
  · exact (div_lt_div_iff_of_pos_right (by positivity : 0 < (N : ℝ) ^ 2 + 1)).mpr (by nlinarith)
  · exact (div_lt_div_iff_of_pos_right (by positivity : 0 < (N : ℝ) + 1)).mpr (by linarith)

def theta (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ :=
  if s < 2 then 1 else omega N s / zeta I N s

def phi (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ :=
  if s < 2 then 1 else (omega N s - omega N (s + 2)) / (zeta I N s - omega N (s + 2))

theorem theta_unit (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    0 < theta I N s ∧ theta I N s ≤ 1 := by
  unfold theta
  split_ifs
  · exact ⟨zero_lt_one, le_rfl⟩
  · exact ⟨div_pos (omega_pos hN hs) (zeta_unit I hN hs).1,
      (div_le_one (zeta_unit I hN hs).1).mpr (omega_le_zeta I hN hs)⟩

theorem phi_denominator_pos (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : 2 ≤ s) (hsN : s + 2 < N) :
    0 < zeta I N s - omega N (s + 2) := by
  have hd := omega_strict_drop hN hs hsN
  have hw := omega_le_zeta I hN (by omega : s < N)
  linarith

theorem phi_unit (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : 2 ≤ s) (hsN : s + 2 < N) :
    0 < phi I N s ∧ phi I N s ≤ 1 := by
  have hsmall : ¬s < 2 := by omega
  rw [phi, ite_eq_right hsmall]
  have hden := phi_denominator_pos I hN hs hsN
  exact ⟨div_pos (sub_pos.mpr (omega_strict_drop hN hs hsN)) hden,
    (div_le_one hden).mpr (by linarith [omega_le_zeta I hN (by omega : s < N)])⟩

theorem theta_eq (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    theta I N s = omega N s * I.den s / normalizer I N s := by
  unfold theta
  split_ifs with hsmall
  · rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
    · simp
    · simp [(lt_trans zero_lt_one I.eta_gt_one).ne']
  · rw [zeta_eq]
    field_simp [I.den_ne s, (normalizer_pos I hN hs).ne']

end
end InexactRealizations.Algorithms.AveragedBalanced
