import InexactRealizations.Balanced.Bounds
import InexactRealizations.Gains.Bounds
import InexactRealizations.Gains.HilbertSchmidt

namespace InexactRealizations.Balanced
noncomputable section
open scoped BigOperators

/-- The actual Balanced response bounds form a genuine uniform response certificate. -/
theorem responseBounds (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    Risk.ResponseBounds (history I N hN) I (fun s => responseBound I N s) :=
  ⟨fun s => (responseBound_pos I hN s.isLt).le, fun s _ hx => response_bound I N hN s hx⟩

/-- The temporal norm of the constructed product profile is exactly the sharp gain. -/
theorem product_energyNorm (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    Analysis.energyNorm (fun s : Fin N => responseBound I N s * queryBound I N s) =
      Lower.linearGain I N := by
  unfold Analysis.energyNorm
  rw [bound_energy I N hN, Real.sqrt_sq (Lower.linearGain_nonneg I N)]

/-- The spectral maximum of the actual Balanced history equals G_N, in both parities. -/
theorem spectralGain_eq (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (history I N hN).spectralGain I = Lower.linearGain I N := by
  rw [InexactRealizations.History.spectralGain_eq_product_energy _ I
    (fun s => responseBound I N s) (fun s => queryBound I N s) (responseBounds I N hN)
    (fun s => (queryBound_pos I hN s.isLt).le)
    (fun s _ hx => query_bound_physical I N hN s hx)
    (fun s => by rw [response_endpoint, abs_neg, abs_of_pos (responseBound_pos I hN s.isLt)])
    (fun s => by rw [query_endpoint_physical, abs_of_pos (queryBound_pos I hN s.isLt)]),
    product_energyNorm I N hN]

/-- Balanced controls arbitrary operator-norm perturbations by exactly the sharp coefficient. -/
theorem operatorBound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (symmetric : Bool) : Gains.OperatorBound (history I N hN) I symmetric (Lower.linearGain I N) := by
  rw [← product_energyNorm I N hN]
  exact Gains.operatorBound_of_product_bounds _ I _ _ (responseBounds I N hN)
    (fun s => (queryBound_pos I hN s.isLt).le)
    (fun s _ hx => query_bound_physical I N hN s hx) symmetric

/-- Balanced controls arbitrary actual-query relative errors by the sharp local coefficient. -/
theorem localRelativeBound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    Gains.LocalRelativeBound (history I N hN) I (Lower.linearGain I N) := by
  rw [← product_energyNorm I N hN]
  exact Gains.localRelativeBound_of_product_bounds _ I _ _ (responseBounds I N hN)
    (fun s => (queryBound_pos I hN s.isLt).le)
    (fun s _ hx => query_bound_physical I N hN s hx)

/-- The actual Balanced matrix derivative obeys the same coefficient under either HS class. -/
theorem hsBound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (symmetric : Bool) : Gains.HsBound (history I N hN) I symmetric (Lower.linearGain I N) := by
  rw [← spectralGain_eq I N hN]
  exact Gains.hsBound_spectralGain _ I symmetric

end
end InexactRealizations.Balanced
