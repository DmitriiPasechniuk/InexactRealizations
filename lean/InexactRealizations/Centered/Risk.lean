import InexactRealizations.Centered.WitnessValue
import Mathlib.Topology.Order.LiminfLimsup

/-! The literal supremum over actual centered relative-noise executions,
followed by its positive-scale limit, has the printed spectral coefficient. 
-/
namespace InexactRealizations.Centered
noncomputable section
open Polynomial MeasureTheory Filter Topology
open scoped BigOperators
variable {N : ℕ}

inductive Value (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r t : ℝ) : ℝ → Prop where
  | model (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
      (Ω : Type) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (𝓕 : Filtration ℕ mΩ)
      (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (initial : E) (w : ℕ → Ω → E)
      (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ) (hi : ‖initial‖ ≤ r)
      (hvar : RelativeVariance h H initial w 𝓕 μ t) :
      Value h I r t (∫ ω, ‖deviation h H initial w ω‖ ^ 2 ∂μ)

def values (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r t : ℝ) : Set ℝ :=
  {v | Value h I r t v}

def risk (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r t : ℝ) : ℝ :=
  sSup (values h I r t)

theorem exact_coefficient_mem (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t : ℝ) (hr : 0 ≤ r) : t ^ 2 * r ^ 2 * centeredCoefficient h I ∈ values h I r t := by
  obtain ⟨lambda, nu, hlam, hnu, he⟩ := Witness.attained_mse h I r t
  rw [← he]
  exact Value.model (Witness.Space N) (Fin N → Bool) (InexactRealizations.Probability.Signs.law N)
    (InexactRealizations.Probability.Signs.past N 1) (Witness.hessian lambda nu)
    (Witness.hessian_admissible I lambda nu hlam hnu) (Witness.initial N r) (Witness.stream h nu r t)
    (Witness.martingale h nu r t) (Witness.initial_norm r hr).le (Witness.relative_variance h lambda nu r t)

theorem values_bddAbove (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t : ℝ) (hr : 0 ≤ r) : BddAbove (values h I r t) := by
  refine ⟨|t| ^ 2 * r ^ 2 * centeredCoefficient h I + |t| ^ 4 * r ^ 2 * varianceRemainder h I |t|, ?_⟩
  intro v hv
  cases hv with
  | model E Ω μ 𝓕 H hH initial w hw hi hvar =>
    have hvabs : RelativeVariance h H initial w 𝓕 μ |t| := by
      intro s
      simpa only [sq_abs] using hvar s
    exact finite_upper h I H hH initial hw r |t| |t| hr (abs_nonneg _) le_rfl hi hvabs

theorem risk_lower (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t : ℝ) (hr : 0 ≤ r) : t ^ 2 * r ^ 2 * centeredCoefficient h I ≤ risk h I r t :=
  le_csSup (values_bddAbove h I r t hr) (exact_coefficient_mem h I r t hr)

theorem risk_upper (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t t0 : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) (htt0 : t ≤ t0) :
    risk h I r t ≤ t ^ 2 * r ^ 2 * centeredCoefficient h I + t ^ 4 * r ^ 2 * varianceRemainder h I t0 := by
  apply csSup_le ⟨_, exact_coefficient_mem h I r t hr⟩
  intro v hv
  cases hv with
  | model E Ω μ 𝓕 H hH initial w hw hi hvar =>
    exact finite_upper h I H hH initial hw r t t0 hr ht htt0 hi hvar

theorem normalized_risk_bounds (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t t0 : ℝ) (hr : 0 < r) (ht : 0 < t) (htt0 : t ≤ t0) :
    centeredCoefficient h I ≤ risk h I r t / (t ^ 2 * r ^ 2) ∧
      risk h I r t / (t ^ 2 * r ^ 2) ≤ centeredCoefficient h I + t ^ 2 * varianceRemainder h I t0 := by
  have hden : 0 < t ^ 2 * r ^ 2 := mul_pos (sq_pos_of_pos ht) (sq_pos_of_pos hr)
  constructor
  · apply (le_div_iff₀ hden).mpr
    simpa only [mul_comm] using risk_lower h I r t hr.le
  · apply (div_le_iff₀ hden).mpr
    exact (risk_upper h I r t t0 hr.le ht.le htt0).trans_eq (by ring)

theorem normalized_risk_tendsto (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r : ℝ) (hr : 0 < r) :
    Tendsto (fun t : ℝ ↦ risk h I r t / (t ^ 2 * r ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 (centeredCoefficient h I)) := by
  have hup : Tendsto (fun t : ℝ ↦ centeredCoefficient h I + t ^ 2 * varianceRemainder h I 1)
      (𝓝[>] (0 : ℝ)) (𝓝 (centeredCoefficient h I)) := by
    have hh : Continuous (fun t : ℝ ↦ centeredCoefficient h I + t ^ 2 * varianceRemainder h I 1) := by fun_prop
    have ht := (hh.tendsto (0 : ℝ)).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero] using ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
    exact ⟨1, by norm_num, fun t ht ↦ (normalized_risk_bounds h I r t 1 hr ht.1 ht.2.le).1⟩
  · apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
    exact ⟨1, by norm_num, fun t ht ↦ (normalized_risk_bounds h I r t 1 hr ht.1 ht.2.le).2⟩

theorem centered_risk_limsup (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r : ℝ) (hr : 0 < r) :
    Filter.limsup (fun t : ℝ ↦ risk h I r t / (t ^ 2 * r ^ 2)) (𝓝[>] (0 : ℝ)) = centeredCoefficient h I :=
  (normalized_risk_tendsto h I r hr).limsup_eq

end
end InexactRealizations.Centered
