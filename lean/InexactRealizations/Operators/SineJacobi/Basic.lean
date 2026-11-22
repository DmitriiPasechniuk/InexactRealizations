import InexactRealizations.Operators.Jacobi.Determinant

/-! The exact reflection symmetry in E.6 follows directly from the sine coefficients.
Use: `InexactRealizations.Operators.SineJacobi.couplingSq_reflect` feeds
`InexactRealizations.Operators.SineJacobi.data_aSq_reflect` (data a Sq reflect).
Proof chain: `InexactRealizations.Operators.SineJacobi.matrix_persymmetric` — chebyshev1,;
Sine-lattice couplings, spectrum, expansion and symmetry.
-/
namespace InexactRealizations.Operators.SineJacobi
noncomputable section
open Real

/-- Defines `h` of type `ℝ` by `π / N`. -/
def h (N : ℕ) : ℝ := π / N
/-- Defines `couplingSq` of type `ℝ` by `(1 / 4) * sin ((s : ℝ) * h N) ^ 2 / (sin (((s : ℝ) - 1 /
2) * h N) * sin (((s : ℝ) + 1 / 2) * h N))`.
-/
def couplingSq (N s : ℕ) : ℝ :=
  (1 / 4) * sin ((s : ℝ) * h N) ^ 2 /
    (sin (((s : ℝ) - 1 / 2) * h N) * sin (((s : ℝ) + 1 / 2) * h N))

/-- Extend the finite chain by zero couplings outside its physical sites. -/
def data (N : ℕ) : JacobiData where
  b := fun _ => 0
  aSq := fun s => if 0 < s ∧ s < N then couplingSq N s else 0

/-- Exact identity `(data N).b s = 0`. -/
@[simp] theorem data_b (N s : ℕ) : (data N).b s = 0 := rfl
/-- Exact identity `(data N).aSq 0 = 0`. -/
@[simp] theorem data_aSq_zero (N : ℕ) : (data N).aSq 0 = 0 := by simp [data]
/-- Exact identity `(data N).aSq s = couplingSq N s`. -/
theorem data_aSq (N s : ℕ) (hs : 0 < s) (hsN : s < N) :
    (data N).aSq s = couplingSq N s := by simp [data, hs, hsN]

/-- Membership in the specified domain/enclosure: `t * h N ∈ Set.Ioo (0 : ℝ) π`. -/
theorem angle_mem (N : ℕ) (hN : 0 < N) {t : ℝ} (ht : 0 < t) (htN : t < N) :
    t * h N ∈ Set.Ioo (0 : ℝ) π := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < h N := div_pos pi_pos hn
  refine ⟨mul_pos ht hp, ?_⟩
  have he : (N : ℝ) * h N = π := by unfold h; field_simp
  rw [← he]
  exact mul_lt_mul_of_pos_right htN hp

/-- The stated quantitative bound `0 < sin (((s : ℝ) - 1 / 2) * h N) * sin (((s : ℝ) + 1 / 2) * h
N)`.
-/
theorem coupling_den_pos (N s : ℕ) (hs : 0 < s) (hsN : s < N) :
    0 < sin (((s : ℝ) - 1 / 2) * h N) * sin (((s : ℝ) + 1 / 2) * h N) := by
  have hn : 0 < N := by omega
  have hs0 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hs1 : (s : ℝ) + 1 ≤ N := by exact_mod_cast hsN
  apply mul_pos
  · exact sin_pos_of_mem_Ioo (angle_mem N hn (by linarith) (by linarith))
  · exact sin_pos_of_mem_Ioo (angle_mem N hn (by linarith) (by linarith))

/-- The stated quantitative bound `0 < couplingSq N s`. -/
theorem couplingSq_pos (N s : ℕ) (hs : 0 < s) (hsN : s < N) : 0 < couplingSq N s := by
  have hsin := sin_pos_of_mem_Ioo (angle_mem N (by omega)
    (show (0 : ℝ) < s by exact_mod_cast hs) (show (s : ℝ) < N by exact_mod_cast hsN))
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hsin)) (coupling_den_pos N s hs hsN)

/-- The stated quantitative bound `0 ≤ (data N).aSq s`. -/
theorem data_aSq_nonneg (N s : ℕ) : 0 ≤ (data N).aSq s := by
  by_cases hs : 0 < s ∧ s < N
  · rw [data_aSq N s hs.1 hs.2]; exact (couplingSq_pos N s hs.1 hs.2).le
  · simp [data, hs]

/-- The exact reflection symmetry in E.6 follows directly from the sine coefficients.

Exact identity `couplingSq N (N - s) = couplingSq N s`.
-/
theorem couplingSq_reflect (N s : ℕ) (hs : 0 < s) (hsN : s < N) :
    couplingSq N (N - s) = couplingSq N s := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have he : (N : ℝ) * h N = π := by unfold h; field_simp
  unfold couplingSq
  rw [Nat.cast_sub hsN.le]
  have h0 : ((N : ℝ) - s) * h N = π - (s : ℝ) * h N := by rw [sub_mul, he]
  have hm : ((N : ℝ) - s - 1 / 2) * h N = π - ((s : ℝ) + 1 / 2) * h N := by rw [← he]; ring
  have hp : ((N : ℝ) - s + 1 / 2) * h N = π - ((s : ℝ) - 1 / 2) * h N := by rw [← he]; ring
  rw [h0, hm, hp, sin_pi_sub, sin_pi_sub, sin_pi_sub,
    mul_comm (sin (((s : ℝ) + 1 / 2) * h N)) (sin (((s : ℝ) - 1 / 2) * h N))]

end
end InexactRealizations.Operators.SineJacobi
