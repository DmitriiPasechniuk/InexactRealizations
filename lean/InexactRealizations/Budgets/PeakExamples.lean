import InexactRealizations.Budgets.PeakCriterion
import InexactRealizations.Comparisons.Competitors.Prefix
import InexactRealizations.Comparisons.Competitors.Sine
import InexactRealizations.Comparisons.Classical.Bounds
import InexactRealizations.Flat.Response
import InexactRealizations.Operators.SineJacobi.Reversal

/-! The named common-peak realizations in Theorem5.1(b), using only the
specific scalar bounds asserted for the imported sine-Jacobi comparison. 
-/
namespace InexactRealizations.Budgets.PeakExamples
noncomputable section
open Polynomial PeakCriterion
open scoped ENNReal NNReal
variable {N : ℕ}

theorem prefix_responsePeaks (I : InexactRealizations.Operators.SpectralInterval) (hN : 0 < N) :
    ResponsePeaks (InexactRealizations.Comparisons.Competitors.Prefix.history I N) I := by
  intro s x hx
  rw [InexactRealizations.Comparisons.Competitors.Prefix.history_eq_classical,
    InexactRealizations.Classical.response_endpoint I N hN, neg_neg]
  exact InexactRealizations.Classical.response_bound I N hN s hx

theorem prefix_queryPeaks (I : InexactRealizations.Operators.SpectralInterval) :
    QueryPeaks (InexactRealizations.Comparisons.Competitors.Prefix.history I N) I := by
  intro s x hx
  rw [InexactRealizations.Comparisons.Competitors.Prefix.history_eq_classical, InexactRealizations.Classical.query_endpoint]
  exact InexactRealizations.Classical.query_bound I N s hx

theorem balanced_responsePeaks (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) :
    ResponsePeaks (InexactRealizations.Balanced.history I N hN) I := by
  intro s x hx
  rw [InexactRealizations.Balanced.response_endpoint I N hN, neg_neg]
  exact InexactRealizations.Balanced.response_bound I N hN s hx

theorem balanced_queryPeaks (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) :
    QueryPeaks (InexactRealizations.Balanced.history I N hN) I := by
  intro s x hx
  rw [InexactRealizations.Balanced.query_endpoint_physical]
  exact InexactRealizations.Balanced.query_bound_physical I N hN s hx

theorem flat_responsePeaks (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) :
    ResponsePeaks (InexactRealizations.Flat.history I N hN) I := by
  intro s x hx
  rw [InexactRealizations.Flat.response_mu I N hN, neg_neg]
  exact InexactRealizations.Flat.response_abs_le I N hN s hx

namespace Sine
open InexactRealizations.Operators
open InexactRealizations.Comparisons.Competitors

theorem query_eval (I : SpectralInterval) (hN : 0 < N) (s : Fin N) (x : ℝ) :
    ((Sine.history I N).query s).eval x =
      ((SineJacobi.data N).leading s).eval (I.z x) / (SineJacobi.data N).den I s := by
  rw [Sine.history, Sine.config, TwoTerm.query_eval _ N (Sine.fixed_point I N hN),
    ← JacobiData.realization,
    JacobiData.scalar_exact _ I (SineJacobi.admissible I N hN) s s.isLt.le,
    JacobiData.residual_eval]

theorem response_eval (I : SpectralInterval) (hN : 0 < N) (s : Fin N) (x : ℝ) :
    ((Sine.history I N).response s).eval x =
      -(2 / (I.delta * (SineJacobi.data N).den I N)) *
        ((SineJacobi.data N).block (s + 1) (N - (s + 1))).eval (I.z x) *
          (SineJacobi.data N).den I s := by
  have hh := Sine.realization_kernel I N hN s x 0
  rw [InexactRealizations.History.realization_kernel, InexactRealizations.History.query_eval_zero, mul_one,
    JacobiData.kernel_eq _ I (SineJacobi.admissible I N hN) s s.isLt x 0] at hh
  have hz : I.z 0 = I.eta := by rw [I.z_eq]; ring
  rw [hz] at hh
  exact hh

theorem responsePeaks (I : SpectralInterval) (hN : 0 < N) : ResponsePeaks (Sine.history I N) I := by
  intro s x hx
  have hn := SineJacobi.admissible I N hN N le_rfl
  have hs := SineJacobi.admissible I N hN s s.isLt.le
  have hc : 0 < 2 / (I.delta * (SineJacobi.data N).den I N) :=
    div_pos (by norm_num) (mul_pos I.delta_pos hn)
  have hb := SineJacobi.tail_endpoint_max N (s + 1) (N - (s + 1)) (by omega) (by omega)
    (I.z x) (I.z_mem hx)
  rw [response_eval I hN s x, response_eval I hN s I.mu, I.z_mu,
    abs_mul, abs_mul, abs_neg, abs_of_pos hc, abs_of_pos hs, neg_mul, neg_mul, neg_neg]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hc.le) hs.le

theorem queryPeaks (I : SpectralInterval) (hN : 0 < N) : QueryPeaks (Sine.history I N) I := by
  intro s x hx
  have hs := SineJacobi.admissible I N hN s s.isLt.le
  rw [query_eval I hN s x, query_eval I hN s I.mu, I.z_mu, abs_div, abs_of_pos hs]
  exact div_le_div_of_nonneg_right (SineJacobi.leading_endpoint_max N s s.isLt (I.z x) (I.z_mem hx)) hs.le

end Sine

theorem prefix_perCall_optima (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (r : ℝ) (hr : 0 < r) :
    PerCallOptimal (InexactRealizations.Comparisons.Competitors.Prefix.history I N) I ∧
      localRelativeGain ∞ (InexactRealizations.Comparisons.Competitors.Prefix.history I N) I r = InexactRealizations.Lower.derivativeScale I N := by
  have he : (InexactRealizations.Comparisons.Competitors.Prefix.history I N).ChebyshevExact I := by
    rw [InexactRealizations.Comparisons.Competitors.Prefix.history_eq_classical]
    exact InexactRealizations.Classical.history_exact I N
  exact ⟨responsePeaks_optimal _ I he (by omega) (prefix_responsePeaks I (by omega)),
    commonPeaks_relative _ I he (by omega) (prefix_responsePeaks I (by omega)) (prefix_queryPeaks I) r hr⟩

theorem balanced_perCall_optima (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (r : ℝ) (hr : 0 < r) :
    PerCallOptimal (InexactRealizations.Balanced.history I N hN) I ∧
      localRelativeGain ∞ (InexactRealizations.Balanced.history I N hN) I r = InexactRealizations.Lower.derivativeScale I N :=
  ⟨responsePeaks_optimal _ I (InexactRealizations.Balanced.history_exact I N hN) (by omega) (balanced_responsePeaks I hN),
    commonPeaks_relative _ I (InexactRealizations.Balanced.history_exact I N hN) (by omega)
      (balanced_responsePeaks I hN) (balanced_queryPeaks I hN) r hr⟩

theorem sine_perCall_optima (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (r : ℝ) (hr : 0 < r) :
    PerCallOptimal (InexactRealizations.Comparisons.Competitors.Sine.history I N) I ∧
      localRelativeGain ∞ (InexactRealizations.Comparisons.Competitors.Sine.history I N) I r = InexactRealizations.Lower.derivativeScale I N :=
  ⟨responsePeaks_optimal _ I (InexactRealizations.Comparisons.Competitors.Sine.terminal I N (by omega)) (by omega)
    (Sine.responsePeaks I (by omega)),
    commonPeaks_relative _ I (InexactRealizations.Comparisons.Competitors.Sine.terminal I N (by omega)) (by omega)
      (Sine.responsePeaks I (by omega)) (Sine.queryPeaks I (by omega)) r hr⟩

theorem flat_perCall_optimal (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) :
    PerCallOptimal (InexactRealizations.Flat.history I N hN) I :=
  responsePeaks_optimal _ I (InexactRealizations.Flat.history_exact I N hN) (by omega) (flat_responsePeaks I hN)

end
end InexactRealizations.Budgets.PeakExamples
