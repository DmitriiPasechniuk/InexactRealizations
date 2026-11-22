import InexactRealizations.Budgets.Interpolation
import InexactRealizations.Gains.RelativeRisk

/-! Literal finite-scale suprema for every call exponent. In particular the
dimension and error suprema precede the positive-scale upper limit. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial Filter Topology InexactRealizations.Analysis
open scoped BigOperators ENNReal NNReal
variable {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]

inductive RelativeValue (p : ℝ≥0∞) (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t : ℝ) : ℝ → Prop where
  | execution (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E) (hH : Admissible I H)
      (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise)
      (delta : Fin N → ℝ) (hi : ‖initial‖ ≤ r)
      (hw : RelativeErrors p h H initial noise u t delta) :
      RelativeValue p h I r t ‖u.output - (aeval H h.terminal) initial‖

def relativeValues (p : ℝ≥0∞) (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t : ℝ) : Set ℝ := {v | RelativeValue p h I r t v}

def relativeRisk (p : ℝ≥0∞) (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t : ℝ) : ℝ := sSup (relativeValues p h I r t)

def localRelativeGain (p : ℝ≥0∞) (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (r : ℝ) : ℝ :=
  Filter.limsup (fun t ↦ relativeRisk p h I r t / (t * r)) (𝓝[>] (0 : ℝ))

include q in
theorem zero_mem_relativeValues (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t : ℝ) (hr : 0 ≤ r) : 0 ∈ relativeValues p h I r t := by
  let : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  let H := InexactRealizations.History.scalarOperator I.mu
  let u := h.run H 0 (fun _ ↦ 0)
  have hbudget : callNorm p (fun _ : Fin N ↦ 0) ≤ 1 := by
    change ‖(0 : PiLp p (fun _ : Fin N ↦ ℝ))‖ ≤ 1
    simp
  have hu : ‖u.output - (aeval H h.terminal) 0‖ = 0 := by rw [h.nominal_output]; simp
  rw [← hu]
  exact RelativeValue.execution ℝ H
    (scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩) 0 (fun _ ↦ 0) u
    (fun _ ↦ 0) (by simpa using hr) ⟨by simp, hbudget, by simp⟩

theorem relativeValues_product_bound (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t t0 : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) (htt0 : t ≤ t0)
    (P Q : Fin N → ℝ) (hP : InexactRealizations.Risk.ResponseBounds h I P) (hQ : ∀ s, 0 ≤ Q s)
    (hq : ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s) :
    ∀ v ∈ relativeValues p h I r t, v ≤
      t * r * callNorm q (fun s ↦ P s * Q s) +
        t ^ 2 * r * callNorm q (fun s ↦ P s * deviationMajorant h I.L t0 s) := by
  intro v hv
  cases hv with
  | execution E H hH initial noise u delta hi hw =>
    exact relative_response_bound h I H hH initial noise u r t t0 hr ht htt0 hi delta hw P Q hP hQ hq

include q in
theorem relativeValues_bddAbove (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t : ℝ) (hr : 0 ≤ r) : BddAbove (relativeValues p h I r t) := by
  obtain ⟨P, Q, hP, hQ, hq⟩ := InexactRealizations.Gains.exists_product_bounds h I
  refine ⟨|t| * r * callNorm q (fun s ↦ P s * Q s) +
    |t| ^ 2 * r * callNorm q (fun s ↦ P s * deviationMajorant h I.L |t| s), ?_⟩
  intro v hv
  cases hv with
  | execution E H hH initial noise u delta hi hw =>
    have hwabs : RelativeErrors p h H initial noise u |t| delta := by
      refine ⟨hw.1, hw.2.1, fun s ↦ (hw.2.2 s).trans ?_⟩
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self t) (hw.1 s)) (norm_nonneg _)
    exact relative_response_bound h I H hH initial noise u r |t| |t| hr
      (abs_nonneg t) le_rfl hi delta hwabs P Q hP hQ hq

include q in
theorem relativeRisk_nonneg (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t : ℝ) (hr : 0 ≤ r) : 0 ≤ relativeRisk p h I r t :=
  le_csSup (relativeValues_bddAbove (p := p) (q := q) h I r t hr)
    (zero_mem_relativeValues (p := p) (q := q) h I r t hr)

theorem relativeRisk_product_bound (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t t0 : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) (htt0 : t ≤ t0)
    (P Q : Fin N → ℝ) (hP : InexactRealizations.Risk.ResponseBounds h I P) (hQ : ∀ s, 0 ≤ Q s)
    (hq : ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s) :
    relativeRisk p h I r t ≤ t * r * callNorm q (fun s ↦ P s * Q s) +
      t ^ 2 * r * callNorm q (fun s ↦ P s * deviationMajorant h I.L t0 s) :=
  csSup_le ⟨0, zero_mem_relativeValues (p := p) (q := q) h I r t hr⟩
    (relativeValues_product_bound h I r t t0 hr ht htt0 P Q hP hQ hq)

include q in
theorem normalizedRisk_bounded (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) :
    (𝓝[>] (0 : ℝ)).IsBoundedUnder (· ≤ ·) (fun t ↦ relativeRisk p h I 1 t / t) := by
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  obtain ⟨P, Q, hP, hQ, hq⟩ := InexactRealizations.Gains.exists_product_bounds h I
  let A := callNorm q (fun s ↦ P s * Q s)
  let B := callNorm q (fun s ↦ P s * deviationMajorant h I.L 1 s)
  apply Filter.isBoundedUnder_of_eventually_le (a := A + B)
  apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
  refine ⟨1, by norm_num, fun t ht ↦ ?_⟩
  have hb := relativeRisk_product_bound (p := p) (q := q) h I 1 t 1 zero_le_one
    ht.1.le ht.2.le P Q hP hQ hq
  have hB : 0 ≤ B := callNorm_nonneg _
  apply (div_le_iff₀ ht.1).mpr
  change relativeRisk p h I 1 t ≤ (A + B) * t
  change relativeRisk p h I 1 t ≤ t * 1 * A + t ^ 2 * 1 * B at hb
  have hterm : t ^ 2 * B ≤ t * B :=
    mul_le_mul_of_nonneg_right (by nlinarith [ht.1, ht.2]) hB
  nlinarith

include q in
theorem normalizedRisk_cobounded (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) :
    (𝓝[>] (0 : ℝ)).IsCoboundedUnder (· ≤ ·) (fun t ↦ relativeRisk p h I 1 t / t) := by
  apply Filter.isCoboundedUnder_le_of_eventually_le (𝓝[>] (0 : ℝ)) (x := 0)
  apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
  exact ⟨1, by norm_num, fun t ht ↦
    div_nonneg (relativeRisk_nonneg (p := p) (q := q) h I 1 t zero_le_one) ht.1.le⟩

end
end InexactRealizations.Budgets
