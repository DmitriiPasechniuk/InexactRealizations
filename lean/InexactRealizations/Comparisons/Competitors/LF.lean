import InexactRealizations.Channel.Roots.Actual

namespace InexactRealizations.Comparisons.Competitors.LF
noncomputable section
open InexactRealizations.Channel.Roots

/-- Literal interlaced LF steps, with unused natural indices extended by zero. -/
def config (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) : Momentum :=
  Stepsize.config (schedule I (2^k) (dyadicPermutation k))

/-- Actual N=2^k-call LF causal history. -/
def history (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) : InexactRealizations.History (2^k) :=
  (config I k).history (2^k)

/-- Every active coefficient is the printed reciprocal cosine-root step. -/
theorem coefficients (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) (s : Fin (2^k)) :
    (config I k).alpha s.val=1/((I.L+I.mu)/2-I.delta/2*
      Real.cos (angle (2^k) (dyadicPermutation k s))) ∧ (config I k).beta s.val=0 := by
  simp [config,Stepsize.config,schedule,s.isLt,steps,node]

/-- The actual LF finite terminal is exactly the normalized Chebyshev terminal. -/
theorem terminal (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) :
    (history I k).terminal=I.residual (2^k) := lfHistory_exact I k

end
end InexactRealizations.Comparisons.Competitors.LF
