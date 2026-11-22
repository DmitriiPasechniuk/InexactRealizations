import InexactRealizations.Centered.Spectral
import InexactRealizations.Gains.Spectral
import InexactRealizations.Balanced.Gains

/-! The exact centered relative coefficient dominates the spectral gain
squared and the sharp universal optimum; Balanced attains both inequalities. 
-/
namespace InexactRealizations.Centered
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ}

theorem coefficient_point_bound (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (x : ℝ) (hx : x ∈ Set.Icc I.mu I.L) :
    (∑ s, responsePeak h I s ^ 2 * (h.query s).eval x ^ 2) ≤ centeredCoefficient h I := by
  have hh := polynomialPeak_bound I (variancePolynomial h (responsePeak h I)) x hx
  rw [abs_of_nonneg (variancePolynomial_nonneg _ _ x), variancePolynomial_eval] at hh
  exact hh

theorem spectralGain_sq_le_coefficient (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) :
    h.spectralGain I ^ 2 ≤ centeredCoefficient h I := by
  obtain ⟨x, hx, y, hy, he⟩ := h.spectralGain_attained I
  have hb : InexactRealizations.Lower.physicalKernelSq h x y ≤ centeredCoefficient h I := by
    apply le_trans (b := ∑ s, responsePeak h I s ^ 2 * (h.query s).eval y ^ 2)
    · apply Finset.sum_le_sum
      intro s _
      have hh := (sq_le_sq₀ (abs_nonneg _) ((responsePeak_bounds h I).1 s)).mpr
        ((responsePeak_bounds h I).2 s x hx)
      rw [sq_abs] at hh
      simpa only [InexactRealizations.Lower.physicalKernel, mul_pow] using
        mul_le_mul_of_nonneg_right hh (sq_nonneg ((h.query s).eval y))
    · exact coefficient_point_bound h I y hy
  rw [← Real.sq_sqrt (InexactRealizations.Lower.physicalKernelSq_nonneg h x y), he] at hb
  exact hb

theorem sharp_coefficient_lower (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 2 ≤ N) :
    InexactRealizations.Lower.linearGain I N ^ 2 ≤ h.spectralGain I ^ 2 ∧
      h.spectralGain I ^ 2 ≤ centeredCoefficient h I := by
  have hA : 0 ≤ h.spectralGain I := by
    obtain ⟨x, _, y, _, hx⟩ := h.spectralGain_attained I
    rw [← hx]
    exact Real.sqrt_nonneg _
  exact ⟨(sq_le_sq₀ (InexactRealizations.Lower.linearGain_nonneg I N) hA).mpr (h.linearGain_le_spectralGain I he hN),
    spectralGain_sq_le_coefficient h I⟩

theorem balanced_responsePeak (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (s : Fin N) :
    responsePeak (InexactRealizations.Balanced.history I N hN) I s = InexactRealizations.Balanced.responseBound I N s := by
  obtain ⟨x, hx, he⟩ := responsePeak_attained (InexactRealizations.Balanced.history I N hN) I s
  apply le_antisymm (he.trans_le (InexactRealizations.Balanced.response_bound I N hN s hx))
  have hb := polynomialPeak_bound I ((InexactRealizations.Balanced.history I N hN).response s) I.mu ⟨le_rfl, I.mu_lt_L.le⟩
  simpa only [responsePeak, InexactRealizations.Balanced.response_endpoint, abs_neg,
    abs_of_pos (InexactRealizations.Balanced.responseBound_pos I hN s.isLt)] using hb

theorem balanced_coefficient (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) :
    centeredCoefficient (InexactRealizations.Balanced.history I N hN) I = InexactRealizations.Lower.linearGain I N ^ 2 := by
  apply le_antisymm
  · obtain ⟨x, hx, he⟩ := centeredCoefficient_attained (InexactRealizations.Balanced.history I N hN) I
    rw [he, ← InexactRealizations.Balanced.bound_energy I N hN]
    apply Finset.sum_le_sum
    intro s _
    rw [balanced_responsePeak, mul_pow]
    have hb := (sq_le_sq₀ (abs_nonneg _) (InexactRealizations.Balanced.queryBound_pos I hN s.isLt).le).mpr
      (InexactRealizations.Balanced.query_bound_physical I N hN s hx)
    rw [sq_abs] at hb
    exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)
  · rw [← InexactRealizations.Balanced.spectralGain_eq I N hN]
    exact spectralGain_sq_le_coefficient _ I

end
end InexactRealizations.Centered
