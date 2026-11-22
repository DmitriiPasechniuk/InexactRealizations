import InexactRealizations.Budgets.PeakProfiles
import InexactRealizations.Budgets.FlatPeaks

/-! The exact Flat relative gain in Theorem5.1(d), for every call budget. -/
namespace InexactRealizations.Budgets
noncomputable section
open scoped ENNReal NNReal
variable {N : ℕ}

theorem callNorm_mul {p : ℝ≥0∞} [Fact (1 ≤ p)] {J : Type*} [Fintype J]
    (c : ℝ) (f : J → ℝ) : callNorm p (fun i ↦ c * f i) = |c| * callNorm p f := by
  change ‖c • WithLp.toLp p f‖ = |c| * ‖WithLp.toLp p f‖
  rw [norm_smul, Real.norm_eq_abs]

theorem flat_all_gamma_relative (p : ℝ≥0∞) (hp : 1 ≤ p) (I : InexactRealizations.Operators.SpectralInterval)
    (hN : 2 ≤ N) (r : ℝ) (hr : 0 < r) :
    localRelativeGain p (InexactRealizations.Flat.history I N hN) I r =
      (InexactRealizations.Lower.additiveScale I N / N) *
        callNorm (dualExponent p) (fun s : Fin N ↦ FlatQuery.peak I N s) := by
  let : p.HolderConjugate (dualExponent p) := holder_dualExponent p hp
  let : Fact (1 ≤ dualExponent p) := ⟨ENNReal.HolderConjugate.one_le (dualExponent p) p⟩
  have hc : 0 ≤ InexactRealizations.Lower.additiveScale I N / N :=
    div_nonneg (InexactRealizations.Risk.additiveScale_nonneg I N) (Nat.cast_nonneg _)
  rw [localRelativeGain_eq_operatorGain p hp _ I r hr]
  have he := operatorGain_of_common_peaks (p := p) (q := dualExponent p)
    (InexactRealizations.Flat.history I N hN) I (by omega) false
    (fun _ ↦ InexactRealizations.Lower.additiveScale I N / N) (fun s ↦ FlatQuery.peak I N s)
    ⟨fun _ ↦ hc, fun s _ hx ↦ InexactRealizations.Flat.response_abs_le I N hN s hx⟩
    (fun s ↦ FlatQuery.peak_nonneg I hN s)
    (fun s x hx ↦ FlatQuery.query_bound I hN s x hx)
    I.mu I.L ⟨le_rfl, I.mu_lt_L.le⟩ ⟨I.mu_lt_L.le, le_rfl⟩
    (fun s ↦ by rw [InexactRealizations.Flat.response_mu, abs_neg, abs_of_nonneg hc])
    (fun s ↦ FlatQuery.query_at_L I hN s)
  rw [he, callNorm_mul, abs_of_nonneg hc]

end
end InexactRealizations.Budgets
