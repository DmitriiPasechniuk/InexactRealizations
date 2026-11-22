import InexactRealizations.Properties.Incompatibility

namespace InexactRealizations.Risk
noncomputable section
open scoped BigOperators
variable {N : ℕ}

/-- Endpoint attainment identifies the temporal response energy exactly. -/
theorem endpoint_response_energy (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (P : Fin N → ℝ) (hp : ∀ s, |(h.response s).eval I.mu| = P s) :
    (∑ s, (h.response s).eval I.mu ^ 2) = ∑ s, P s ^ 2 := by
  apply Finset.sum_congr rfl
  intro s _
  rw [← sq_abs, hp]

/-- A fixed exact history with jointly sharp endpoint response bounds has this
exact worst-case martingale MSE, even when its temporal bounds are unequal. 
-/
theorem mseRisk_eq_of_endpoint_bounds (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (he : h.ChebyshevExact I) (hN : 0 < N)
    (P : Fin N → ℝ) (hP : ResponseBounds h I P)
    (hp : ∀ s, |(h.response s).eval I.mu| = P s) (r σ : ℝ) (hr : 0 ≤ r) :
    mseRisk h I r σ = I.epsilon N ^ 2 * r ^ 2 + σ ^ 2 * ∑ s, P s ^ 2 := by
  apply le_antisymm
  · apply csInf_le ⟨mseOptimum I N r σ, fun C hb => mseBound_lower h I he hN r σ C hr hb⟩
    intro E Ω _ _ _ _ _ μ _ 𝓕 w hw hσ H hH initial hi
    exact mse_upper h I he H hH P hP initial hw r σ hr hi hσ
  · simpa only [endpoint_response_energy h I P hp] using
      InexactRealizations.Properties.scalar_mse_le_risk h I he r σ hr

end
end InexactRealizations.Risk
