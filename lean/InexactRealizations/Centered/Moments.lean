import InexactRealizations.Centered.LpExecution

/-! Conditional relative variance controls actual-query second moments.
The constants are chosen uniformly before dimension and error stream. 
-/
namespace InexactRealizations.Centered
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Filter InexactRealizations.Analysis
open scoped BigOperators
variable {N : ℕ} {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}

def RelativeVariance (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (w : ℕ → Ω → E) (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) (t : ℝ) : Prop :=
  ∀ s : Fin N, μ[fun ω ↦ ‖w s.val ω‖ ^ 2 | 𝓕 s.val] ≤ᵐ[μ]
    fun ω ↦ t ^ 2 * ‖randomQuery h H initial w s ω‖ ^ 2

omit [IsProbabilityMeasure μ] [CompleteSpace E] in
theorem liftedH_bound (I : InexactRealizations.Operators.SpectralInterval) (H : E →ₗ[ℝ] E)
    (hH : Admissible I H) (v : Lp E 2 μ) : ‖liftedH H v‖ ≤ I.L * ‖v‖ := by
  have hL : 0 ≤ I.L := (I.mu_pos.trans I.mu_lt_L).le
  have hh : ‖H.toContinuousLinearMap‖ ≤ I.L :=
    ContinuousLinearMap.opNorm_le_bound _ hL (hessian_action_bound I H hH)
  exact ((H.toContinuousLinearMap.compLpL 2 μ).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right ((H.toContinuousLinearMap.norm_compLpL_le).trans hh) (norm_nonneg v))

theorem lp_query_deviation (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (initial : E)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ)
    (r t t0 : ℝ) (ht : 0 ≤ t) (htt0 : t ≤ t0) (hi : ‖initial‖ ≤ r)
    (hvar : RelativeVariance h H initial w 𝓕 μ t) (s : Fin N) :
    ‖((randomQuery_memLp h H initial hw s).sub
      (memLp_const (μ := μ) (p := 2) ((aeval H (h.query s)) initial))).toLp
      (fun ω ↦ randomQuery h H initial w s ω - (aeval H (h.query s)) initial)‖ ≤
      t * r * deviationMajorant h I.L t0 s := by
  let u := lpExecution h H initial hw
  have hnoise (j : Fin N) : ‖(hw.squareIntegrable j.val j.isLt).toLp (w j.val)‖ ≤ t * ‖u.query j‖ :=
    l2_relative_bound (𝓕.le j.val) (hw.squareIntegrable j.val j.isLt)
      (randomQuery_memLp h H initial hw j) t ht (hvar j)
  have hinit : ‖Lp.const 2 μ initial‖ ≤ r := by
    change ‖(memLp_const (μ := μ) (p := 2) initial).toLp (fun _ : Ω ↦ initial)‖ ≤ r
    rw [l2_const_norm]
    exact hi
  have hh := deviation_envelope h (liftedH H) I.L (I.mu_pos.trans I.mu_lt_L).le
    (liftedH_bound I H hH) (Lp.const 2 μ initial) _ u r t t0 ht htt0 hinit hnoise s
  rw [lifted_polynomial_const] at hh
  have he : ((randomQuery_memLp h H initial hw s).sub
      (memLp_const (μ := μ) (p := 2) ((aeval H (h.query s)) initial))).toLp
      (fun ω ↦ randomQuery h H initial w s ω - (aeval H (h.query s)) initial) =
      u.query s - Lp.const 2 μ ((aeval H (h.query s)) initial) :=
    MemLp.toLp_sub (randomQuery_memLp h H initial hw s)
      (memLp_const (μ := μ) (p := 2) ((aeval H (h.query s)) initial))
  exact (congrArg norm he).trans_le hh

theorem query_deviation_second (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (initial : E)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ)
    (r t t0 : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) (htt0 : t ≤ t0) (hi : ‖initial‖ ≤ r)
    (hvar : RelativeVariance h H initial w 𝓕 μ t) (s : Fin N) :
    (∫ ω, ‖randomQuery h H initial w s ω - (aeval H (h.query s)) initial‖ ^ 2 ∂μ) ≤
      t ^ 2 * r ^ 2 * deviationMajorant h I.L t0 s ^ 2 := by
  have hh := lp_query_deviation h I H hH initial hw r t t0 ht htt0 hi hvar s
  have hnonneg : 0 ≤ t * r * deviationMajorant h I.L t0 s :=
    mul_nonneg (mul_nonneg ht hr) (deviationMajorant_nonneg h (I.mu_pos.trans I.mu_lt_L).le (ht.trans htt0) s)
  have hs := (sq_le_sq₀ (norm_nonneg _) hnonneg).mpr hh
  rw [l2_norm_sq] at hs
  simpa only [mul_pow] using hs

theorem query_second_bound (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (initial : E)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ)
    (r t t0 : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) (htt0 : t ≤ t0) (hi : ‖initial‖ ≤ r)
    (hvar : RelativeVariance h H initial w 𝓕 μ t) (s : Fin N) :
    (∫ ω, ‖randomQuery h H initial w s ω‖ ^ 2 ∂μ) ≤
      ‖(aeval H (h.query s)) initial‖ ^ 2 + t ^ 2 * r ^ 2 * deviationMajorant h I.L t0 s ^ 2 := by
  rw [randomQuery_second_moment h H initial hw s]
  exact add_le_add le_rfl (query_deviation_second h I H hH initial hw r t t0 hr ht htt0 hi hvar s)

theorem noise_second_bound (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (initial : E)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ)
    (r t t0 : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) (htt0 : t ≤ t0) (hi : ‖initial‖ ≤ r)
    (hvar : RelativeVariance h H initial w 𝓕 μ t) (s : Fin N) :
    (∫ ω, ‖w s.val ω‖ ^ 2 ∂μ) ≤ t ^ 2 * ‖(aeval H (h.query s)) initial‖ ^ 2 +
      t ^ 4 * r ^ 2 * deviationMajorant h I.L t0 s ^ 2 := by
  have hh := integral_mono_ae integrable_condExp
    (((randomQuery_memLp h H initial hw s).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul (t ^ 2)) (hvar s)
  rw [integral_condExp (𝓕.le s.val), integral_const_mul] at hh
  exact (hh.trans (mul_le_mul_of_nonneg_left
    (query_second_bound h I H hH initial hw r t t0 hr ht htt0 hi hvar s) (sq_nonneg t))).trans_eq (by ring)

end
end InexactRealizations.Centered
