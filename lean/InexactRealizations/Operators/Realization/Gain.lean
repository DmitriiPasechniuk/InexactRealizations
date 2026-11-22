import InexactRealizations.Operators.Realization.Basic
import InexactRealizations.Operators.Chebyshev.Normalization
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The supremum over both spectral parameters, exactly.
Use: `InexactRealizations.Operators.Realization.gain` feeds `InexactRealizations.Chains.Horizon.gain_eq` (gain eq).
Proof chain: `InexactRealizations.Operators.Stepsize.gain_lower_bound` — chebyshev1,; Sharp stepsize
drift lower bound and asymptotics.
-/
namespace InexactRealizations.Operators.Realization
noncomputable section
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Euclidean norm across insertion times at one spectral pair. -/
def kernelNorm (R : Realization ι) (N : ℕ) (lam nu : ℝ) : ℝ :=
  Real.sqrt (∑ s ∈ Finset.range N, (R.kernel N s lam nu) ^ 2)

/-- Defines `gainValues` of type `Set ℝ` by `{v | ∃ lam ∈ Set.Icc I.mu I.L, ∃ nu ∈ Set.Icc I.mu
I.L, v = R.kernelNorm N lam nu}`.
-/
def gainValues (R : Realization ι) (I : SpectralInterval) (N : ℕ) : Set ℝ :=
  {v | ∃ lam ∈ Set.Icc I.mu I.L, ∃ nu ∈ Set.Icc I.mu I.L,
    v = R.kernelNorm N lam nu}

/-- The supremum over both spectral parameters, exactly. -/
def gain (R : Realization ι) (I : SpectralInterval) (N : ℕ) : ℝ :=
  sSup (R.gainValues I N)

end
end InexactRealizations.Operators.Realization
