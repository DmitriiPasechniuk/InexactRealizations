import InexactRealizations.Averages.Optimal
import InexactRealizations.Averages.UniformChristoffel
import Mathlib.NumberTheory.ZetaValues

/-! The actual positive-noise additive optima force the printed uniform
spectral lower bound; its endpoint Christoffel sum has the Basel limit. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Polynomial MeasureTheory Real Filter Topology
open scoped BigOperators

def AdditiveOptimal {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) : Prop :=
  (∃ r t : ℝ, 0 ≤ r ∧ 0 < t ∧ InexactRealizations.Risk.additiveRisk h I r t = InexactRealizations.Risk.additiveOptimum I N r t) ∨
  (∃ r σ : ℝ, 0 ≤ r ∧ 0 < σ ∧ InexactRealizations.Risk.mseRisk h I r σ = InexactRealizations.Risk.mseOptimum I N r σ)

def inverseSquareSum (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹

theorem uniform_optimal_lower {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (ho : AdditiveOptimal h I) :
    (InexactRealizations.Lower.additiveScale I N / N) ^ 2 * inverseSquareSum N ≤ (uniform I).variance h := by
  rcases ho with ⟨r, t, hr, ht, hh⟩ | ⟨r, σ, hr, hσ, hh⟩
  · simpa only [uniform_christoffel, inverseSquareSum] using
      variance_lower_of_additive_optimal (uniform I) h he hN r t hr ht hh
  · simpa only [uniform_christoffel, inverseSquareSum] using
      variance_lower_of_mse_optimal (uniform I) h he hN r σ hr hσ hh

theorem inverseSquareSum_one_le (N : ℕ) (hN : 0 < N) : 1 ≤ inverseSquareSum N := by
  have hh := Finset.single_le_sum (f := fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)
    (fun k _ ↦ by positivity) (Finset.mem_range.mpr hN)
  simpa only [Nat.zero_add, Nat.cast_one, one_pow, inv_one, inverseSquareSum] using hh

theorem inverseSquareSum_tendsto : Tendsto inverseSquareSum atTop (𝓝 (π ^ 2 / 6)) := by
  have hh := hasSum_zeta_two.summable.tsum_eq_zero_add
  rw [hasSum_zeta_two.tsum_eq] at hh
  have hsum : HasSum (fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹) (π ^ 2 / 6) := by
    have hs := hasSum_zeta_two.summable.comp_injective Nat.succ_injective
    have hs' : Summable (fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
      simpa only [Function.comp_def, Nat.succ_eq_add_one, one_div] using hs
    apply hs'.hasSum_iff.mpr
    simpa only [Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), div_zero, zero_add, one_div] using hh.symm
  exact hsum.tendsto_sum_nat

theorem inverseSquareSum_eventually_lower (b : ℝ) (hb : b < π ^ 2 / 6) :
    ∃ N0 : ℕ, ∀ N ≥ N0, b < inverseSquareSum N := by
  exact eventually_atTop.mp (inverseSquareSum_tendsto.eventually (lt_mem_nhds hb))

end
end InexactRealizations.Averages
