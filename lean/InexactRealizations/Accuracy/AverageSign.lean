import InexactRealizations.Roundoff.Journal

/-! The upper-endpoint parity of the average-error channel, used by the
admissible uncompensated-rounding witness. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

theorem averageChart_neg_one (k : ℕ) :
    (InexactRealizations.Roundoff.averageChart k).eval (-1) =
      (-1 : ℝ) ^ k * (((k ^ 2 / 4 : ℕ)) : ℝ) := by
  rw [← InexactRealizations.Roundoff.averageChart_endpoint, InexactRealizations.Roundoff.averageChart]
  simp only [eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : 2 * (i + 1) ≤ k := by have := Finset.mem_range.mp hi; omega
  have hp : (-1 : ℝ) ^ (k - 2 * (i + 1)) = (-1 : ℝ) ^ k := by
    nth_rw 2 [← Nat.sub_add_cancel hle]
    rw [pow_add, pow_mul]
    norm_num
  rw [U_eval_neg, Int.cast_negOnePow_natCast, hp]

theorem averageResponse_at_L (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    (InexactRealizations.Roundoff.averageResponse I N s).eval I.L =
      (-1 : ℝ) ^ (N - 1 - s) * (InexactRealizations.Roundoff.averageResponse I N s).eval I.mu := by
  have hz : I.z I.L = -1 := by
    unfold InexactRealizations.Operators.SpectralInterval.z InexactRealizations.Operators.SpectralInterval.delta
    field_simp [(sub_pos.mpr I.mu_lt_L).ne']
    ring
  rw [InexactRealizations.Roundoff.averageResponse_eval, hz, averageChart_neg_one,
    InexactRealizations.Roundoff.averageResponse_endpoint]
  ring

end
end InexactRealizations.Accuracy
