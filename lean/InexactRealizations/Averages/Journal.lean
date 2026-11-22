import InexactRealizations.Averages.JointRange
import InexactRealizations.Averages.Minimum

/-! All clauses in the current journal article. The named
laws are actual probability measures, every energy is its literal integral,
every optimum quantifies actual histories, and the joint range has the
printed quantifiers and threshold. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Real
open scoped BigOperators
variable {N : ℕ}

theorem journal_prefix (I : InexactRealizations.Operators.SpectralInterval) (ρ : SpectralLaw I) (hN : 2 ≤ N) :
    ρ.variance (InexactRealizations.Classical.history I N) =
      (16 * I.epsilon N ^ 2 / I.delta ^ 2) *
        (moment ρ N / 4 + ∑ k ∈ Finset.Ico 1 N, I.den (N - k) ^ 2 * moment ρ k) :=
  prefix_variance ρ N (by omega)

theorem journal_named_measures (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) :
    moment (arcsine I) k = (k : ℝ) ∧ moment (uniform I) k = oddHarmonic k ∧
      (uniform I).christoffel k = (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹ ∧
      (arcsine I).christoffel k = (2 * (k : ℝ) + 1)⁻¹ :=
  ⟨arcsine_moment I k, uniform_moment I k, uniform_christoffel I k, arcsine_christoffel I k⟩

theorem journal_christoffel_lower (I : InexactRealizations.Operators.SpectralInterval) (ρ : SpectralLaw I)
    (h : InexactRealizations.History N) :
    (∑ s : Fin N, ρ.christoffel (N - 1 - s.val) * (h.response s).eval I.mu ^ 2) ≤ ρ.variance h :=
  ρ.variance_christoffel_lower h

theorem journal_additive_optimal_spectral (I : InexactRealizations.Operators.SpectralInterval) (ρ : SpectralLaw I)
    (h : InexactRealizations.History N) (he : h.ChebyshevExact I) (hN : 2 ≤ N) (ho : AdditiveOptimal h I) :
    (InexactRealizations.Lower.additiveScale I N / N) ^ 2 * (∑ k ∈ Finset.range N, ρ.christoffel k) ≤ ρ.variance h := by
  rcases ho with ⟨r, t, hr, ht, hh⟩ | ⟨r, σ, hr, hσ, hh⟩
  · exact variance_lower_of_additive_optimal ρ h he (by omega) r t hr ht hh
  · exact variance_lower_of_mse_optimal ρ h he (by omega) r σ hr hσ hh

end
end InexactRealizations.Averages
