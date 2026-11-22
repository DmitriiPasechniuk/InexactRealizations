import InexactRealizations.Accuracy.Uncompensated.Mass
import Mathlib.Analysis.SpecificLimits.Normed

/-! The weighted geometric series in the uncorrected-average estimate. -/
namespace InexactRealizations.Accuracy.Uncompensated
noncomputable section
open scoped BigOperators

def geometricTerm (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) : ℝ :=
  (k : ℝ) * InexactRealizations.Classical.decay I ^ (k + 1)

theorem geometricTerm_nonneg (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) : 0 ≤ geometricTerm I k :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (InexactRealizations.Classical.decay_mem I).1.le _)

theorem geometricSeries_hasSum (I : InexactRealizations.Operators.SpectralInterval) :
    HasSum (geometricTerm I) (InexactRealizations.Classical.decay I ^ 2 / (1 - InexactRealizations.Classical.decay I) ^ 2) := by
  have hq : ‖InexactRealizations.Classical.decay I‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (InexactRealizations.Classical.decay_mem I).1]
    exact (InexactRealizations.Classical.decay_mem I).2
  have hh := (hasSum_descFactorial_mul_geometric_of_norm_lt_one 1 hq).mul_right (InexactRealizations.Classical.decay I)
  simp only [Nat.descFactorial_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one, Nat.reduceAdd] at hh
  convert hh using 1
  · funext k
    unfold geometricTerm
    rw [pow_succ]
    ring
  · ring

theorem reversed_geometric_sum_le (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    (∑ s : Fin (N - 2), geometricTerm I (N - 1 - s.val)) ≤
      InexactRealizations.Classical.decay I ^ 2 / (1 - InexactRealizations.Classical.decay I) ^ 2 := by
  let f : Fin (N - 2) → Fin N := fun s ↦ ⟨N - 1 - s.val, by have := s.isLt; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have hh := congrArg Fin.val hab
    dsimp only [f] at hh
    have ha := a.isLt
    have hb := b.isLt
    omega
  have hmap : (∑ s : Fin (N - 2), geometricTerm I (N - 1 - s.val)) =
      ∑ k ∈ Finset.image f Finset.univ, geometricTerm I k.val := by
    rw [Finset.sum_image (by intro a _ b _ hab; exact hf hab)]
  rw [hmap]
  have hsub : (∑ k ∈ Finset.image f Finset.univ, geometricTerm I k.val) ≤
      ∑ k : Fin N, geometricTerm I k.val :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intro k _ _; exact geometricTerm_nonneg I _)
  have hfull : (∑ k : Fin N, geometricTerm I k.val) ≤ ∑' k : ℕ, geometricTerm I k := by
    rw [Fin.sum_univ_eq_sum_range (geometricTerm I) N]
    exact (geometricSeries_hasSum I).summable.sum_le_tsum (Finset.range N) (by intro k _; exact geometricTerm_nonneg I k)
  rw [(geometricSeries_hasSum I).tsum_eq] at hfull
  exact hsub.trans hfull

end
end InexactRealizations.Accuracy.Uncompensated
