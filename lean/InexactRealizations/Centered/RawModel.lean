import InexactRealizations.Centered.Risk
import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner

/-! The stated conditional second-moment law implies square integrability
causally. The public model therefore requires no additional L2 hypothesis. 
-/
namespace InexactRealizations.Centered
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators ENNReal
variable {N : ℕ} {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}

structure RawLaw (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (w : ℕ → Ω → E) (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) (t : ℝ) : Prop where
  adapted : ∀ s, s < N → StronglyMeasurable[𝓕 (s + 1)] (w s)
  centered : ∀ s, s < N → μ[w s | 𝓕 s] =ᵐ[μ] 0
  variance : ∀ s : Fin N,
    μ⁻[fun ω ↦ ENNReal.ofReal (‖w s.val ω‖ ^ 2) | 𝓕 s.val] ≤ᵐ[μ]
      fun ω ↦ ENNReal.ofReal (t ^ 2 * ‖randomQuery h H initial w s ω‖ ^ 2)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem memLp_of_conditional_second_moment {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {f g : Ω → E} (hf : AEStronglyMeasurable[mΩ] f μ) (hg : MemLp g 2 μ) (t : ℝ)
    (hv : μ⁻[fun ω ↦ ENNReal.ofReal (‖f ω‖ ^ 2) | m] ≤ᵐ[μ]
      fun ω ↦ ENNReal.ofReal (t ^ 2 * ‖g ω‖ ^ 2)) : MemLp f 2 μ := by
  have hright : Integrable (fun ω ↦ t ^ 2 * ‖g ω‖ ^ 2) μ :=
    (hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _
  have hfin : (∫⁻ ω, ENNReal.ofReal (‖f ω‖ ^ 2) ∂μ) < ∞ := by
    rw [← lintegral_condLExp hm μ]
    exact (lintegral_mono_ae hv).trans_lt
      ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω ↦ mul_nonneg (sq_nonneg t) (sq_nonneg ‖g ω‖))).mp
        hright.hasFiniteIntegral)
  apply (memLp_two_iff_integrable_sq_norm hf).mpr
  exact ⟨hf.norm.pow 2,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω ↦ sq_nonneg ‖f ω‖)).mpr hfin⟩

omit [CompleteSpace E] in
theorem RawLaw.squareIntegrable (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    {t : ℝ} (hw : RawLaw h H initial w 𝓕 μ t) : ∀ s, s < N → MemLp (w s) 2 μ := by
  have hall : ∀ n, (hn : n < N) →
      MemLp (w n) 2 μ ∧ MemLp (randomAnswer h H initial w ⟨n, hn⟩) 2 μ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      let s : Fin N := ⟨n, hn⟩
      have hsummand (j : Fin N) : MemLp (fun ω ↦ h.a s j • randomAnswer h H initial w j ω) 2 μ := by
        by_cases hj : j.val < n
        · exact ((ih j.val hj j.isLt).2).const_smul _
        · have ha : h.a s j = 0 := h.triangular s j (by simpa only [Fin.le_def] using Nat.le_of_not_gt hj)
          simpa only [ha, zero_smul] using (memLp_const (μ := μ) (p := 2) (0 : E))
      have hq : MemLp (randomQuery h H initial w s) 2 μ := by
        have he : randomQuery h H initial w s =
            (fun _ : Ω ↦ initial) - (fun ω ↦ ∑ j, h.a s j • randomAnswer h H initial w j ω) := by
          funext ω
          exact (h.run H initial (fun j ↦ w j.val ω)).query_eq s
        rw [he]
        exact (memLp_const (μ := μ) (p := 2) initial).sub
          (memLp_finsetSum Finset.univ (fun j _ ↦ hsummand j))
      have hw2 := memLp_of_conditional_second_moment (𝓕.le n)
        ((hw.adapted n hn).mono (𝓕.le (n + 1))).aestronglyMeasurable hq t (hw.variance s)
      refine ⟨hw2, ?_⟩
      have he : randomAnswer h H initial w s = (fun ω ↦ H (randomQuery h H initial w s ω)) + w n := by
        funext ω
        exact (h.run H initial (fun j ↦ w j.val ω)).answer_eq s
      rw [he]
      exact (hq.continuousLinearMap_comp H.toContinuousLinearMap).add hw2
  intro s hs
  exact (hall s hs).1

omit [CompleteSpace E] in
theorem RawLaw.martingale (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    {t : ℝ} (hw : RawLaw h H initial w 𝓕 μ t) :
    InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ where
  adapted := hw.adapted
  centered := hw.centered
  squareIntegrable := hw.squareIntegrable h H initial

omit [CompleteSpace E] in
theorem RawLaw.relativeVariance (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    {t : ℝ} (hw : RawLaw h H initial w 𝓕 μ t) : RelativeVariance h H initial w 𝓕 μ t := by
  intro s
  have hi := (hw.squareIntegrable h H initial s.val s.isLt).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hc := condLExp_ofReal (𝓕 s.val) hi (Eventually.of_forall fun ω ↦ sq_nonneg ‖w s.val ω‖)
  filter_upwards [hc, hw.variance s] with ω he hv
  rw [he] at hv
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg t) (sq_nonneg _))).mp hv

omit [IsProbabilityMeasure μ] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem rawLawOfMartingale (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ) {t : ℝ}
    (hv : RelativeVariance h H initial w 𝓕 μ t) : RawLaw h H initial w 𝓕 μ t where
  adapted := hw.adapted
  centered := hw.centered
  variance s := by
    have hi := (hw.squareIntegrable s.val s.isLt).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have hc := condLExp_ofReal (𝓕 s.val) hi (Eventually.of_forall fun ω ↦ sq_nonneg ‖w s.val ω‖)
    filter_upwards [hc, hv s] with ω he hle
    exact he.trans_le (ENNReal.ofReal_le_ofReal hle)

inductive RawValue (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r t : ℝ) : ℝ → Prop where
  | model (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
      (Ω : Type) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (𝓕 : Filtration ℕ mΩ)
      (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (initial : E) (w : ℕ → Ω → E)
      (hw : RawLaw h H initial w 𝓕 μ t) (hi : ‖initial‖ ≤ r) :
      RawValue h I r t (∫ ω, ‖deviation h H initial w ω‖ ^ 2 ∂μ)

def rawValues (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r t : ℝ) : Set ℝ :=
  {v | RawValue h I r t v}

def rawRisk (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r t : ℝ) : ℝ :=
  sSup (rawValues h I r t)

theorem rawValues_eq (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r t : ℝ) :
    rawValues h I r t = values h I r t := by
  ext v
  constructor
  · intro hv
    cases hv with
    | model E Ω μ 𝓕 H hH initial w hw hi =>
      exact Value.model E Ω μ 𝓕 H hH initial w (hw.martingale h H initial) hi (hw.relativeVariance h H initial)
  · intro hv
    cases hv with
    | model E Ω μ 𝓕 H hH initial w hw hi hv =>
      exact RawValue.model E Ω μ 𝓕 H hH initial w (rawLawOfMartingale h H initial hw hv) hi

theorem rawRisk_eq (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r t : ℝ) :
    rawRisk h I r t = risk h I r t := by
  unfold rawRisk risk
  rw [rawValues_eq]

end
end InexactRealizations.Centered
