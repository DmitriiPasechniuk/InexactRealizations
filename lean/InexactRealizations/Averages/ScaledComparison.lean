import InexactRealizations.Averages.UpperRatio
import InexactRealizations.Averages.OptimalLower

/-! Dimensionless comparison of the actual two spectral variances. All
numeric conditions below are discharged in the final joint-range theorem. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Real
open InexactRealizations.Classical

def normalizedLower (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : ℝ :=
  ((1 - I.epsilon N) * I.kappa / (N : ℝ)) ^ 2 * inverseSquareSum N

def normalizedLimit (I : InexactRealizations.Operators.SpectralInterval) : ℝ :=
  sqrt I.kappa * log I.kappa / (1 - I.kappa⁻¹)

theorem normalized_limit_pos (I : InexactRealizations.Operators.SpectralInterval) : 0 < normalizedLimit I := by
  have he : normalizedLimit I = I.L ^ 2 * spectralLimit (uniform I) := by
    rw [uniform_limit_value]
    unfold normalizedLimit
    field_simp [(I.mu_pos.trans I.mu_lt_L).ne']
  rw [he]
  exact mul_pos (sq_pos_of_pos (I.mu_pos.trans I.mu_lt_L)) (uniform_limit_pos I)

theorem normalized_optimal_lower {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (ho : AdditiveOptimal h I) :
    normalizedLower I N ≤ I.L ^ 2 * (uniform I).variance h := by
  have hh := mul_le_mul_of_nonneg_left (uniform_optimal_lower h I he hN ho) (sq_nonneg I.L)
  have hscale : I.L * InexactRealizations.Lower.additiveScale I N = (1 - I.epsilon N) * I.kappa := by
    unfold InexactRealizations.Lower.additiveScale InexactRealizations.Operators.SpectralInterval.kappa
    ring
  have hid : I.L ^ 2 * ((InexactRealizations.Lower.additiveScale I N / (N : ℝ)) ^ 2 * inverseSquareSum N) =
      normalizedLower I N := by
    unfold normalizedLower
    rw [← hscale]
    ring
  rwa [hid] at hh

theorem normalized_prefix_upper (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (hk : 9 ≤ I.kappa) (hl : 1 ≤ log I.kappa) (hN : 0 < N) (hNk : (N : ℝ) ≤ I.kappa) :
    I.L ^ 2 * (uniform I).variance (history I N) ≤
      (1 + 128 * exp (-((N : ℝ) / sqrt I.kappa))) * normalizedLimit I := by
  have hh := mul_le_mul_of_nonneg_left (uniform_prefix_ratio I N hk hl hN hNk) (sq_nonneg I.L)
  rw [uniform_limit_value] at hh
  exact hh.trans_eq (by unfold normalizedLimit; field_simp [(I.mu_pos.trans I.mu_lt_L).ne'])

theorem strict_comparison_of_normalized {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (ho : AdditiveOptimal h I)
    (hk : 9 ≤ I.kappa) (hl : 1 ≤ log I.kappa) (hNk : (N : ℝ) ≤ I.kappa)
    (hgap : (1 + 128 * exp (-((N : ℝ) / sqrt I.kappa))) * normalizedLimit I < normalizedLower I N) :
    (uniform I).variance (history I N) < (uniform I).variance h := by
  have hh := (normalized_prefix_upper I N hk hl hN hNk).trans_lt
    (hgap.trans_le (normalized_optimal_lower h I he hN ho))
  exact (mul_lt_mul_iff_right₀ (sq_pos_of_pos (I.mu_pos.trans I.mu_lt_L))).mp hh

theorem normalizedLower_bound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (a b : ℝ) (ha : 0 ≤ a) (hae : a ≤ 1 - I.epsilon N)
    (hb : 0 ≤ b) (hbN : b ≤ inverseSquareSum N) :
    a ^ 2 * b * (I.kappa ^ 2 / (N : ℝ) ^ 2) ≤ normalizedLower I N := by
  have hs := (sq_le_sq₀ ha (ha.trans hae)).mpr hae
  have hh := mul_le_mul hs hbN hb (sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_right hh (div_nonneg (sq_nonneg I.kappa) (sq_nonneg (N : ℝ)))
  exact hm.trans_eq (by unfold normalizedLower; ring)

end
end InexactRealizations.Averages
