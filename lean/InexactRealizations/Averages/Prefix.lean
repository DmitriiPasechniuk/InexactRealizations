import InexactRealizations.Averages.Measure
import InexactRealizations.Comparisons.Classical.History
import Mathlib.Algebra.BigOperators.Intervals

/-! The spectral-average formula follows from the
actual Prefix responses for every spectral probability measure. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Polynomial Polynomial.Chebyshev MeasureTheory
open scoped BigOperators
variable {I : InexactRealizations.Operators.SpectralInterval} (ρ : SpectralLaw I)

def moment (k : ℕ) : ℝ := ∫ x, (U ℝ ((k : ℤ) - 1)).eval (I.z x) ^ 2 ∂ρ.measure

theorem moment_nonneg (k : ℕ) : 0 ≤ moment ρ k := integral_nonneg fun _ ↦ sq_nonneg _

theorem moment_zero : moment ρ 0 = 0 := by simp [moment]

theorem prefix_energy (N : ℕ) (hN : 0 < N) (s : Fin N) :
    ρ.energy ((InexactRealizations.Classical.history I N).response s) =
      (16 * I.epsilon N ^ 2 / I.delta ^ 2) *
        (InexactRealizations.Classical.initialWeight s.val * I.den s.val) ^ 2 * moment ρ (N - s.val) := by
  have hind : ((N - 1 - s.val : ℕ) : ℤ) = ((N - s.val : ℕ) : ℤ) - 1 := by omega
  simp only [SpectralLaw.energy, InexactRealizations.Classical.response_eval I N hN, mul_pow,
    div_pow, hind, integral_const_mul, moment]
  ring

theorem prefix_variance_reversed (N : ℕ) (hN : 0 < N) :
    ρ.variance (InexactRealizations.Classical.history I N) =
      (16 * I.epsilon N ^ 2 / I.delta ^ 2) *
        ∑ k ∈ Finset.range N,
          (InexactRealizations.Classical.initialWeight (N - 1 - k) * I.den (N - 1 - k)) ^ 2 * moment ρ (k + 1) := by
  unfold SpectralLaw.variance
  simp_rw [prefix_energy ρ N hN, mul_assoc]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (fun s ↦ (InexactRealizations.Classical.initialWeight s * I.den s) ^ 2 * moment ρ (N - s)) N,
    ← Finset.sum_range_reflect]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [show N - (N - 1 - k) = k + 1 by have := Finset.mem_range.mp hk; omega]

theorem prefix_variance (N : ℕ) (hN : 0 < N) :
    ρ.variance (InexactRealizations.Classical.history I N) =
      (16 * I.epsilon N ^ 2 / I.delta ^ 2) *
        (moment ρ N / 4 + ∑ k ∈ Finset.Ico 1 N, I.den (N - k) ^ 2 * moment ρ k) := by
  rw [prefix_variance_reversed ρ N hN]
  congr 1
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [Finset.sum_range_succ]
  have hlast : (InexactRealizations.Classical.initialWeight (n + 1 - 1 - n) * I.den (n + 1 - 1 - n)) ^ 2 *
      moment ρ (n + 1) = moment ρ (n + 1) / 4 := by
    simp only [Nat.add_sub_cancel, Nat.sub_self, InexactRealizations.Classical.initialWeight, ite_true,
      InexactRealizations.Operators.SpectralInterval.den, Nat.cast_zero, T_zero, eval_one]
    ring
  rw [hlast, add_comm]
  congr 1
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have hs : n + 1 - 1 - k ≠ 0 := by have := Finset.mem_range.mp hk; omega
  simp only [InexactRealizations.Classical.initialWeight, hs, ite_false, one_mul]
  rw [show n + 1 - 1 - k = n + 1 - (k + 1) by omega, add_comm k 1]

end
end InexactRealizations.Averages
