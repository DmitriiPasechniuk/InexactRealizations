import InexactRealizations.Channel.Roots.Algebra
import InexactRealizations.Comparisons.Competitors.Stepsize

namespace InexactRealizations.Channel.Roots
noncomputable section
open Polynomial
open scoped BigOperators

/-- The actual causal history of a prescribed finite gradient-step schedule. -/
def history {N : ℕ} (α : Fin N → ℝ) : InexactRealizations.History N :=
  Comparisons.Competitors.Stepsize.history N (extend α)

/-- Its actual terminal is the full affine product of the prescribed steps. -/
theorem history_terminal {N : ℕ} (α : Fin N → ℝ) : (history α).terminal=terminal α := by
  rw [history,Comparisons.Competitors.Stepsize.terminal,polynomial_extend]

/-- Every permutation of the explicitly constructed Chebyshev roots is terminal-exact. -/
theorem history_exact (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (e : Equiv.Perm (Fin N)) :
    (history (steps I N e)).ChebyshevExact I := by
  rw [InexactRealizations.History.ChebyshevExact,history_terminal,terminal_steps_eq]

/-- The literal recursively interlaced LF schedule as an actual oracle history. -/
def lfHistory (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) : InexactRealizations.History (2^k) :=
  history (steps I (2^k) (dyadicPermutation k))

/-- The actual LF/fractal method has the exact desired Chebyshev terminal. -/
theorem lfHistory_exact (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) :
    (lfHistory I k).ChebyshevExact I := history_exact I (2^k) (dyadicPermutation k)

end
end InexactRealizations.Channel.Roots
