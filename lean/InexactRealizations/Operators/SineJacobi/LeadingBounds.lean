import InexactRealizations.Operators.SineJacobi.Terminal

/-! The endpoint-normalized nonnegative cosine expansion in E.2.
Result: `InexactRealizations.Operators.SineJacobi.normalized_fourier` supplies the stated article conclusion.
-/
namespace InexactRealizations.Operators.SineJacobi
noncomputable section
open Polynomial Real
open scoped BigOperators

/-- Defines `endpoint` of type `ℝ` by `(2:ℝ)^s*((data N).leading s).eval 1`. -/
def endpoint (N s : ℕ) : ℝ := (2:ℝ)^s*((data N).leading s).eval 1

/-- Exact identity `endpoint N s = ∑ k ∈ Finset.range (s+1), coefficient N s k`. -/
theorem endpoint_sum (N s : ℕ) (hs : s < N) :
    endpoint N s = ∑ k ∈ Finset.range (s+1), coefficient N s k := by simpa only [mul_zero, cos_zero, mul_one, endpoint] using leading_fourier N s hs 0

/-- All proper leading blocks attain their absolute maxima at one.

The stated quantitative bound `|((data N).leading s).eval x| ≤ ((data N).leading s).eval 1`.
-/
theorem leading_endpoint_max (N s : ℕ) (hs : s < N) (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) :
    |((data N).leading s).eval x| ≤ ((data N).leading s).eval 1 := by
  have hf := leading_fourier N s hs (arccos x)
  rw [cos_arccos hx.1 hx.2] at hf
  have hb : |(2:ℝ)^s*((data N).leading s).eval x| ≤ endpoint N s := by
    rw [hf, endpoint_sum N s hs]
    calc
      _ ≤ ∑ k ∈ Finset.range (s+1), |coefficient N s k*cos (((s:ℝ)-2*(k:ℝ))*arccos x)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        have hc := (coefficient_pos N s k hs (by have := Finset.mem_range.mp hk; omega)).le
        rw [abs_mul, abs_of_nonneg hc]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_cos_le_one _) hc
  rw [abs_mul, abs_of_pos (pow_pos (by norm_num : (0:ℝ) < 2) s)] at hb
  exact (mul_le_mul_iff_right₀ (pow_pos (by norm_num : (0:ℝ) < 2) s)).mp hb

end
end InexactRealizations.Operators.SineJacobi
