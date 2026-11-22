import InexactRealizations.Averages.Measure
import InexactRealizations.Properties.Incompatibility

/-! The Christoffel lower bound for every actual history, and the stronger
bound for histories attaining either of the positive-noise additive optima. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ}

theorem additive_optimal_responses (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (r t : ℝ) (hr : 0 ≤ r) (ht : 0 < t)
    (hopt : InexactRealizations.Risk.additiveRisk h I r t = InexactRealizations.Risk.additiveOptimum I N r t) :
    ∀ s, (h.response s).eval I.mu = -InexactRealizations.Lower.additiveScale I N / N := by
  obtain ⟨w, hw, hout⟩ := InexactRealizations.Risk.scalar_additive_attainment h I he r t hr ht.le
  have hb : I.epsilon N * r + t * InexactRealizations.Analysis.energyNorm (fun s ↦ (h.response s).eval I.mu) ≤
      InexactRealizations.Risk.additiveRisk h I r t := by
    apply le_csInf (InexactRealizations.Risk.additiveBounds_nonempty h I he r t ht.le)
    intro C hC
    have hu := hC ℝ (InexactRealizations.History.scalarOperator I.mu)
      (InexactRealizations.Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩) r w
      (by simp [abs_of_nonneg hr]) hw (h.run _ r w)
    simpa only [hout] using hu
  rw [hopt] at hb
  unfold InexactRealizations.Risk.additiveOptimum at hb
  have hnorm : InexactRealizations.Analysis.energyNorm (fun s ↦ (h.response s).eval I.mu) ≤
      InexactRealizations.Lower.additiveScale I N / Real.sqrt N := by
    rw [mul_div_assoc] at hb
    nlinarith
  have hsq := (sq_le_sq₀ (InexactRealizations.Analysis.energyNorm_nonneg _)
    (div_nonneg (InexactRealizations.Risk.additiveScale_nonneg I N) (Real.sqrt_nonneg _))).mpr hnorm
  rw [InexactRealizations.Analysis.energyNorm_sq, div_pow, Real.sq_sqrt (Nat.cast_nonneg N)] at hsq
  exact InexactRealizations.Properties.uniform_profile_of_energy_le hN _ _ (InexactRealizations.Lower.response_sum_mu h I he) hsq

theorem christoffel_sum_reverse {I : InexactRealizations.Operators.SpectralInterval} (ρ : SpectralLaw I) :
    (∑ s : Fin N, ρ.christoffel (N - 1 - s.val)) = ∑ k ∈ Finset.range N, ρ.christoffel k := by
  rw [Fin.sum_univ_eq_sum_range (fun s ↦ ρ.christoffel (N - 1 - s)) N]
  exact Finset.sum_range_reflect _ N

theorem variance_lower_of_uniform_responses {I : InexactRealizations.Operators.SpectralInterval} (ρ : SpectralLaw I)
    (h : InexactRealizations.History N)
    (hp : ∀ s, (h.response s).eval I.mu = -InexactRealizations.Lower.additiveScale I N / N) :
    (InexactRealizations.Lower.additiveScale I N / N) ^ 2 * (∑ k ∈ Finset.range N, ρ.christoffel k) ≤ ρ.variance h := by
  have hh := ρ.variance_christoffel_lower h
  simp_rw [hp, neg_div, neg_sq] at hh
  rw [← Finset.sum_mul, christoffel_sum_reverse] at hh
  simpa only [mul_comm] using hh

theorem variance_lower_of_additive_optimal {I : InexactRealizations.Operators.SpectralInterval} (ρ : SpectralLaw I)
    (h : InexactRealizations.History N) (he : h.ChebyshevExact I) (hN : 0 < N)
    (r t : ℝ) (hr : 0 ≤ r) (ht : 0 < t)
    (hopt : InexactRealizations.Risk.additiveRisk h I r t = InexactRealizations.Risk.additiveOptimum I N r t) :
    (InexactRealizations.Lower.additiveScale I N / N) ^ 2 * (∑ k ∈ Finset.range N, ρ.christoffel k) ≤ ρ.variance h :=
  variance_lower_of_uniform_responses ρ h (additive_optimal_responses h I he hN r t hr ht hopt)

theorem variance_lower_of_mse_optimal {I : InexactRealizations.Operators.SpectralInterval} (ρ : SpectralLaw I)
    (h : InexactRealizations.History N) (he : h.ChebyshevExact I) (hN : 0 < N)
    (r σ : ℝ) (hr : 0 ≤ r) (hσ : 0 < σ)
    (hopt : InexactRealizations.Risk.mseRisk h I r σ = InexactRealizations.Risk.mseOptimum I N r σ) :
    (InexactRealizations.Lower.additiveScale I N / N) ^ 2 * (∑ k ∈ Finset.range N, ρ.christoffel k) ≤ ρ.variance h :=
  variance_lower_of_uniform_responses ρ h
    (InexactRealizations.Properties.mse_optimal_responses h I he hN r σ hr hσ hopt)

end
end InexactRealizations.Averages
