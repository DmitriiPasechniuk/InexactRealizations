import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals

/-! Exact finite parity count in the average-error response. -/
namespace InexactRealizations.Roundoff
open scoped BigOperators

theorem parity_endpoint_sum (k : ℕ) :
    (∑ i ∈ Finset.range (k / 2), (k - 2 * (i + 1) + 1)) = k ^ 2 / 4 := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more k ih _ =>
    have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
    have hsum : (∑ i ∈ Finset.range ((k + 2) / 2), (k + 2 - 2 * (i + 1) + 1)) =
        (k + 1) + ∑ i ∈ Finset.range (k / 2), (k - 2 * (i + 1) + 1) := by
      rw [hdiv, Finset.sum_range_succ']
      have hh : (∑ i ∈ Finset.range (k / 2), (k + 2 - 2 * (i + 1 + 1) + 1)) =
          ∑ i ∈ Finset.range (k / 2), (k - 2 * (i + 1) + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        omega
      rw [hh]
      omega
    rw [hsum, ih]
    have hsq : (k + 2) ^ 2 = k ^ 2 + 4 * k + 4 := by ring
    omega

theorem parity_endpoint_sum_real (k : ℕ) :
    (∑ i ∈ Finset.range (k / 2), (((k - 2 * (i + 1) : ℕ) : ℝ) + 1)) = ((k ^ 2 / 4 : ℕ) : ℝ) := by
  have hh := congrArg (fun n : ℕ ↦ (n : ℝ)) (parity_endpoint_sum k)
  simp only [Nat.cast_sum, Nat.cast_add, Nat.cast_one] at hh
  exact hh

end InexactRealizations.Roundoff
