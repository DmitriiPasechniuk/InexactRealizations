import InexactRealizations.Budgets.Exponents
import InexactRealizations.Lower.PhysicalCorners
import InexactRealizations.Risk.Lower

/-! The all-exponent signed endpoint lower bounds in Theorem2.2. -/
namespace InexactRealizations.Budgets
noncomputable section
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι]

theorem callNorm_abs {p : ℝ≥0∞} [Fact (1 ≤ p)] (v : ι → ℝ) :
    callNorm p (fun i ↦ |v i|) = callNorm p v := by
  by_cases hp : p = ∞
  · rw [hp, callNorm_top, callNorm_top]
    simp only [abs_abs]
  · have hpr : 0 < p.toReal := ENNReal.toReal_pos_iff.mpr
      ⟨zero_lt_one.trans_le (Fact.out : 1 ≤ p), lt_top_iff_ne_top.mpr hp⟩
    rw [callNorm_finite hpr, callNorm_finite hpr]
    simp only [abs_abs]

theorem signed_sum_bound [Nonempty ι] {p q : ℝ≥0∞} [p.HolderConjugate q] (v : ι → ℝ) :
    (Fintype.card ι : ℝ) ^ (-(1 / p).toReal) * |∑ i, v i| ≤ callNorm q v := by
  let : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hh := holder_budget (p := p) (q := q) (fun i ↦ |v i|)
    (fun _ : ι ↦ (Fintype.card ι : ℝ) ^ (-(1 / p).toReal)) (fun i ↦ abs_nonneg _) uniform_budget
  rw [← Finset.mul_sum, callNorm_abs] at hh
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have htri := Finset.abs_sum_le_sum_abs v Finset.univ
  exact (mul_le_mul_of_nonneg_left htri (Real.rpow_nonneg hn _)).trans hh

theorem constant_signed_profile [Nonempty ι] {p q : ℝ≥0∞} [p.HolderConjugate q]
    {S : ℝ} (hS : 0 ≤ S) :
    callNorm q (fun _ : ι ↦ -S / Fintype.card ι) =
      (Fintype.card ι : ℝ) ^ (-(1 / p).toReal) * S := by
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have habs : |-S / (Fintype.card ι : ℝ)| = S / Fintype.card ι := by
    rw [neg_div, abs_neg, abs_of_nonneg (div_nonneg hS hn.le)]
  rw [callNorm_const, habs]
  have hexp : (1 / q).toReal = 1 + (-(1 / p).toReal) := by nlinarith [inverse_conjugates (p := p) (q := q)]
  rw [hexp, Real.rpow_add hn, Real.rpow_one]
  field_simp [hn.ne']

theorem additive_endpoint_lower {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]
    (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (he : h.ChebyshevExact I) (hN : 0 < N) :
    (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.additiveScale I N ≤
      callNorm q (fun s : Fin N ↦ (h.response s).eval I.mu) := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hh := signed_sum_bound (p := p) (q := q) (fun s : Fin N ↦ (h.response s).eval I.mu)
  rw [InexactRealizations.Lower.response_sum_mu h I he, abs_neg,
    abs_of_nonneg (InexactRealizations.Risk.additiveScale_nonneg I N)] at hh
  simpa only [Fintype.card_fin] using hh

theorem relative_endpoint_lower {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]
    (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (he : h.ChebyshevExact I) (hN : 0 < N) :
    (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.derivativeScale I N ≤
      callNorm q (fun s : Fin N ↦ (h.response s).eval I.mu * (h.query s).eval I.mu) := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hh := signed_sum_bound (p := p) (q := q)
    (fun s : Fin N ↦ (h.response s).eval I.mu * (h.query s).eval I.mu)
  have hD : 0 ≤ InexactRealizations.Lower.derivativeScale I N := by
    unfold InexactRealizations.Lower.derivativeScale
    have heps := (one_div_pos.mpr (I.den_pos N)).le
    have hDelta := I.delta_pos.le
    positivity
  change (Fintype.card (Fin N) : ℝ) ^ (-(1 / p).toReal) *
    |∑ s : Fin N, InexactRealizations.Lower.physicalKernel h s I.mu I.mu| ≤ _ at hh
  rw [InexactRealizations.Lower.kernel_sum_mu h I he, abs_neg, abs_of_nonneg hD] at hh
  simpa only [Fintype.card_fin] using hh

end
end InexactRealizations.Budgets
