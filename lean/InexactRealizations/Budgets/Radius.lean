import InexactRealizations.Budgets.RelativeRisk

/-! Exact radial homogeneity of the actual relative-error supremum. -/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial Filter Topology
open scoped ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem relativeErrors_scale (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise)
    (t : ℝ) (delta : Fin N → ℝ) (hw : RelativeErrors p h H initial noise u t delta)
    (c : ℝ) (hc : 0 ≤ c) :
    RelativeErrors p h H (c • initial) (fun s ↦ c • noise s)
      (InexactRealizations.Gains.scaleExecution h H initial noise u c) t delta := by
  refine ⟨hw.1, hw.2.1, fun s ↦ ?_⟩
  change ‖c • noise s‖ ≤ t * delta s * ‖c • u.query s‖
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  nlinarith [mul_le_mul_of_nonneg_left (hw.2.2 s) hc]

include q in
theorem relativeRisk_radius (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t : ℝ) (hr : 0 < r) : relativeRisk p h I r t = r * relativeRisk p h I 1 t := by
  apply le_antisymm
  · apply csSup_le ⟨0, zero_mem_relativeValues (p := p) (q := q) h I r t hr.le⟩
    intro v hv
    cases hv with
    | execution E H hH initial noise u delta hi hw =>
      let z := InexactRealizations.Gains.scaleExecution h H initial noise u r⁻¹
      have hz : ‖r⁻¹ • initial‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
        exact (mul_le_mul_of_nonneg_left hi (inv_pos.mpr hr).le).trans_eq (inv_mul_cancel₀ hr.ne')
      have hmem : ‖z.output - (aeval H h.terminal) (r⁻¹ • initial)‖ ∈
          relativeValues p h I 1 t :=
        RelativeValue.execution E H hH (r⁻¹ • initial) (fun s ↦ r⁻¹ • noise s) z delta hz
          (relativeErrors_scale h H initial noise u t delta hw r⁻¹ (inv_pos.mpr hr).le)
      have hb := le_csSup (relativeValues_bddAbove (p := p) (q := q) h I 1 t zero_le_one) hmem
      rw [InexactRealizations.Gains.scaleExecution_error, abs_of_pos (inv_pos.mpr hr)] at hb
      have hh := mul_le_mul_of_nonneg_left hb hr.le
      simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, relativeRisk] using hh
  · rw [mul_comm r]
    apply (le_div_iff₀ hr).mp
    apply csSup_le ⟨0, zero_mem_relativeValues (p := p) (q := q) h I 1 t zero_le_one⟩
    intro v hv
    cases hv with
    | execution E H hH initial noise u delta hi hw =>
      let z := InexactRealizations.Gains.scaleExecution h H initial noise u r
      have hz : ‖r • initial‖ ≤ r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hi hr.le
      have hmem : ‖z.output - (aeval H h.terminal) (r • initial)‖ ∈
          relativeValues p h I r t :=
        RelativeValue.execution E H hH (r • initial) (fun s ↦ r • noise s) z delta hz
          (relativeErrors_scale h H initial noise u t delta hw r hr.le)
      have hb := le_csSup (relativeValues_bddAbove (p := p) (q := q) h I r t hr.le) hmem
      rw [InexactRealizations.Gains.scaleExecution_error, abs_of_pos hr] at hb
      exact (le_div_iff₀ hr).mpr (by simpa only [mul_comm, relativeRisk] using hb)

include q in
theorem localRelativeGain_radius (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r : ℝ) (hr : 0 < r) : localRelativeGain p h I r = localRelativeGain p h I 1 := by
  unfold localRelativeGain
  apply Filter.limsup_congr
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht : 0 < t := ht
  rw [relativeRisk_radius (p := p) (q := q) h I r t hr, mul_one]
  field_simp

end
end InexactRealizations.Budgets
