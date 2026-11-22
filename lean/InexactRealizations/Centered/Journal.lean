import InexactRealizations.Centered.RawModel
import InexactRealizations.Centered.Comparison

/-! 2 of the current journal article. The risk is the literal
supremum over actual executions satisfying the stated conditional law;
square integrability is a theorem of that law, not an added assumption. 
-/
namespace InexactRealizations.Centered
noncomputable section
open Filter Topology
open scoped BigOperators
variable {N : ℕ}

theorem coefficient_maximum (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) :
    (∀ ν ∈ Set.Icc I.mu I.L,
      (∑ s, responsePeak h I s ^ 2 * (h.query s).eval ν ^ 2) ≤ centeredCoefficient h I) ∧
    ∃ ν ∈ Set.Icc I.mu I.L,
      centeredCoefficient h I = ∑ s, responsePeak h I s ^ 2 * (h.query s).eval ν ^ 2 :=
  ⟨coefficient_point_bound h I, centeredCoefficient_attained h I⟩

theorem journal_centered (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 2 ≤ N) (r : ℝ) (hr : 0 < r) :
    Filter.limsup (fun t : ℝ ↦ rawRisk h I r t / (t ^ 2 * r ^ 2)) (𝓝[>] (0 : ℝ)) =
        centeredCoefficient h I ∧
      h.spectralGain I ^ 2 ≤ centeredCoefficient h I ∧
      InexactRealizations.Lower.linearGain I N ^ 2 ≤ h.spectralGain I ^ 2 := by
  simp_rw [rawRisk_eq]
  exact ⟨centered_risk_limsup h I r hr, (sharp_coefficient_lower h I he hN).2,
    (sharp_coefficient_lower h I he hN).1⟩

theorem journal_centered_balanced (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N)
    (r : ℝ) (hr : 0 < r) :
    Filter.limsup (fun t : ℝ ↦ rawRisk (InexactRealizations.Balanced.history I N hN) I r t / (t ^ 2 * r ^ 2))
        (𝓝[>] (0 : ℝ)) = InexactRealizations.Lower.linearGain I N ^ 2 ∧
      centeredCoefficient (InexactRealizations.Balanced.history I N hN) I = InexactRealizations.Lower.linearGain I N ^ 2 ∧
      (InexactRealizations.Balanced.history I N hN).spectralGain I ^ 2 = InexactRealizations.Lower.linearGain I N ^ 2 := by
  simp_rw [rawRisk_eq]
  exact ⟨(centered_risk_limsup _ I r hr).trans (balanced_coefficient I hN),
    balanced_coefficient I hN, congrArg (fun x : ℝ ↦ x ^ 2) (InexactRealizations.Balanced.spectralGain_eq I N hN)⟩

end
end InexactRealizations.Centered
