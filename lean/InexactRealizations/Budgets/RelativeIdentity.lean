import InexactRealizations.Budgets.RelativeRisk

/-! The actual relative-error upper limit equals the unrestricted operator
first-variation supremum for every lp call budget. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial Filter Topology InexactRealizations.Analysis
open scoped BigOperators ENNReal NNReal
variable {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]

include q in
theorem relativeRisk_linearized_bound (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (t t0 : ℝ) (ht : 0 < t) (htt0 : t ≤ t0) (P : Fin N → ℝ)
    (hP : InexactRealizations.Risk.ResponseBounds h I P) :
    relativeRisk p h I 1 t ≤ t * operatorGain p h I false +
      t ^ 2 * ∑ s, P s * deviationMajorant h I.L t0 s := by
  apply csSup_le ⟨0, zero_mem_relativeValues (p := p) (q := q) h I 1 t zero_le_one⟩
  intro v hv
  cases hv with
  | execution E H hH initial noise u delta hi hw =>
    obtain ⟨D, hD, hrem⟩ := relative_linearization (p := p) (q := q)
      h I H hH initial noise u t t0 ht htt0 hi delta hw P hP
    have hop : ‖h.firstVariation H D initial‖ ≤ operatorGain p h I false :=
      le_csSup (operatorValues_bddAbove (p := p) (q := q) h I false)
        (OperatorValue.execution E H hH D delta ⟨hw.1, hw.2.1⟩ hD (by simp) initial hi)
    have htri := norm_add_le
      ((u.output - (aeval H h.terminal) initial) - t • h.firstVariation H D initial)
      (t • h.firstVariation H D initial)
    rw [sub_add_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at htri
    exact htri.trans (by nlinarith [mul_le_mul_of_nonneg_left hop ht.le])

include q in
theorem localRelativeGain_one_le_operatorGain (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) : localRelativeGain p h I 1 ≤ operatorGain p h I false := by
  simp only [localRelativeGain, mul_one]
  apply (Filter.limsup_le_iff' (normalizedRisk_cobounded (p := p) (q := q) h I)
    (normalizedRisk_bounded (p := p) (q := q) h I)).mpr
  intro y hy
  obtain ⟨P, hP⟩ := InexactRealizations.Risk.exists_responseBounds h I
  let B := ∑ s, P s * deviationMajorant h I.L 1 s
  have hB : 0 ≤ B := Finset.sum_nonneg (fun s _ ↦ mul_nonneg (hP.1 s)
    (deviationMajorant_nonneg h (lt_trans I.mu_pos I.mu_lt_L).le zero_le_one s))
  apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
  refine ⟨min 1 ((y - operatorGain p h I false) / (B + 1)),
    lt_min zero_lt_one (div_pos (sub_pos.mpr hy) (by positivity)), fun t ht ↦ ?_⟩
  have ht1 := ht.2.trans_le (min_le_left _ _)
  have hte := (lt_div_iff₀ (by positivity : 0 < B + 1)).mp
    (ht.2.trans_le (min_le_right _ _))
  have hb := relativeRisk_linearized_bound (p := p) (q := q) h I t 1 ht.1 ht1.le P hP
  apply (div_le_iff₀ ht.1).mpr
  change relativeRisk p h I 1 t ≤ t * operatorGain p h I false + t ^ 2 * B at hb
  nlinarith [mul_pos ht.1 (sub_pos.mpr hy)]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

include q in
theorem firstVariation_le_localRelativeGain (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (H : E →ₗ[ℝ] E) (hH : Admissible I H)
    (D : Fin N → E →ₗ[ℝ] E) (delta : Fin N → ℝ) (hd : Budget p delta)
    (hD : ∀ s, ‖(D s).toContinuousLinearMap‖ ≤ delta s) (initial : E) (hi : ‖initial‖ ≤ 1) :
    ‖h.firstVariation H D initial‖ ≤ localRelativeGain p h I 1 := by
  let noise (t : ℝ) (s : Fin N) := t • D s
    (h.oracleQuery initial (InexactRealizations.History.perturbedOracle H D t) s)
  let u (t : ℝ) : h.Execution H initial (noise t) := {
    query := h.oracleQuery initial (InexactRealizations.History.perturbedOracle H D t)
    answer := h.oracleAnswers initial (InexactRealizations.History.perturbedOracle H D t)
    query_eq := fun _ ↦ rfl
    answer_eq := fun s ↦ h.oracleAnswers_eq initial _ s }
  let f (t : ℝ) := h.oracleOutput initial (InexactRealizations.History.perturbedOracle H D t)
  have huoutput (t : ℝ) : (u t).output = f t := rfl
  have hzero : f 0 = (aeval H h.terminal) initial := by
    have hn : noise 0 = fun _ ↦ 0 := by funext s; simp [noise]
    have hz := h.physical_response H initial (noise 0) (u 0)
    rw [huoutput, hn] at hz
    simpa only [map_zero, Finset.sum_const_zero, add_zero] using hz
  have hlimit := (h.hasDerivAt_perturbed_output H D initial).tendsto_slope_zero_right.norm
  change Tendsto (fun t ↦ ‖t⁻¹ • (f (0 + t) - f 0)‖)
    (𝓝[>] (0 : ℝ)) (𝓝 ‖h.firstVariation H D initial‖) at hlimit
  simp only [localRelativeGain, mul_one]
  apply Filter.le_limsup_of_le (normalizedRisk_bounded (p := p) (q := q) h I)
  intro b hb
  apply le_of_tendsto hlimit
  filter_upwards [self_mem_nhdsWithin, hb] with t ht hb
  have ht : 0 < t := ht
  have hw : RelativeErrors p h H initial (noise t) (u t) t delta := by
    refine ⟨hd.1, hd.2, fun s ↦ ?_⟩
    change ‖t • D s ((u t).query s)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hh := ((D s).toContinuousLinearMap.le_opNorm ((u t).query s)).trans
      (mul_le_mul_of_nonneg_right (hD s) (norm_nonneg _))
    exact (mul_le_mul_of_nonneg_left hh ht.le).trans_eq (by ring)
  have hout : ‖(u t).output - (aeval H h.terminal) initial‖ ≤ relativeRisk p h I 1 t :=
    le_csSup (relativeValues_bddAbove (p := p) (q := q) h I 1 t zero_le_one)
      (RelativeValue.execution E H hH initial (noise t) (u t) delta hi hw)
  rw [huoutput] at hout
  simp only [zero_add, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, hzero]
  calc
    _ ≤ t⁻¹ * relativeRisk p h I 1 t :=
      mul_le_mul_of_nonneg_left hout (inv_pos.mpr ht).le
    _ = relativeRisk p h I 1 t / t := by ring
    _ ≤ b := hb

include q in
theorem localRelativeGain_one_eq_operatorGain (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) : localRelativeGain p h I 1 = operatorGain p h I false := by
  apply le_antisymm (localRelativeGain_one_le_operatorGain (p := p) (q := q) h I)
  apply csSup_le (operatorValues_nonempty (p := p) (q := q) h I false)
  intro v hv
  cases hv with
  | execution E H hH D delta hd hD hsym initial hi =>
    exact firstVariation_le_localRelativeGain (p := p) (q := q) h I H hH D delta hd hD initial hi

end
end InexactRealizations.Budgets
