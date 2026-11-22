import InexactRealizations.Budgets.Corners
import InexactRealizations.Budgets.Additive
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Equality in the signed endpoint norm bound for every finite gamma.
The additive chain requires t>0; the zero-noise counterexample is
recorded separately in CornerBoundary. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem profile_unique_of_top_norm {v : ι → ℝ} {S : ℝ}
    (hsum : (∑ i, v i) = -S) (hnorm : callNorm ∞ v = S / Fintype.card ι) :
    ∀ i, v i = -S / Fintype.card ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hlower (i : ι) : 0 ≤ v i + S / Fintype.card ι := by
    have hh := coordinate_le_norm (p := ∞) v i
    rw [hnorm] at hh
    linarith [(abs_le.mp hh).1]
  have hcancel : (Fintype.card ι : ℝ) * (S / Fintype.card ι) = S := by field_simp
  have hz : (∑ i, (v i + S / Fintype.card ι)) = 0 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum, hcancel]
    ring
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hlower i)).mp hz
  intro i
  have hi := hall i (Finset.mem_univ _)
  rw [neg_div]
  linarith

set_option maxHeartbeats 1000000 in
theorem signed_mean_norm_unique {p q : ℝ≥0∞} [p.HolderConjugate q]
    (hp : p ≠ ∞) {v : ι → ℝ} {S : ℝ} (hS : 0 ≤ S) (hsum : (∑ i, v i) = -S)
    (hnorm : callNorm q v = callNorm q (fun _ : ι ↦ -S / Fintype.card ι)) :
    ∀ i, v i = -S / Fintype.card ι := by
  let : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hmean : 0 ≤ S / (Fintype.card ι : ℝ) := div_nonneg hS hn.le
  by_cases hq : q = ∞
  · apply profile_unique_of_top_norm hsum
    rw [hq] at hnorm
    have hconst : callNorm ∞ (fun _ : ι ↦ -S / Fintype.card ι) = S / Fintype.card ι := by
      rw [callNorm_top]
      simp only [ciSup_const, neg_div, abs_neg, abs_of_nonneg hmean]
    exact hnorm.trans hconst
  · have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
    let c := (Fintype.card ι : ℝ) ^ (-(1 / p).toReal)
    have hc : 0 < c := Real.rpow_pos_of_pos hn _
    have hvalue : callNorm q v = c * S := hnorm.trans (constant_signed_profile (p := p) (q := q) hS)
    have hholder := holder_budget (p := p) (q := q) (fun i ↦ |v i|) (fun _ : ι ↦ c)
      (fun i ↦ abs_nonneg _) uniform_budget
    rw [← Finset.mul_sum, callNorm_abs, hvalue] at hholder
    have htri := Finset.abs_sum_le_sum_abs v Finset.univ
    rw [hsum, abs_neg, abs_of_nonneg hS] at htri
    have habs : (∑ i, |v i|) = S := by nlinarith
    have hnormsum : (∑ i, |v i| ^ q.toReal) =
        ∑ _ : ι, (S / Fintype.card ι) ^ q.toReal := by
      rw [callNorm_finite hpq.symm.pos, callNorm_finite hpq.symm.pos] at hnorm
      simp only [neg_div, abs_neg, abs_of_nonneg hmean] at hnorm
      exact (Real.rpow_left_inj (Finset.sum_nonneg (fun i _ ↦ Real.rpow_nonneg (abs_nonneg _) _))
        (Finset.sum_nonneg (fun _ _ ↦ Real.rpow_nonneg hmean _))
          (one_div_ne_zero hpq.symm.ne_zero)).mp hnorm
    let w : ι → ℝ := fun _ ↦ 1 / Fintype.card ι
    have hwpos (i : ι) : 0 < w i := one_div_pos.mpr hn
    have hwsum : (∑ i, w i) = 1 := by simp [w, hn.ne']
    have haverage : (∑ i, w i * |v i|) = S / Fintype.card ι := by
      dsimp only [w]
      rw [← Finset.mul_sum, habs]
      ring
    have hpower : (∑ i, w i * |v i| ^ q.toReal) = (S / Fintype.card ι) ^ q.toReal := by
      dsimp only [w]
      rw [← Finset.mul_sum, hnormsum]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [hn.ne']
    have hjensen : (∑ i, w i • |v i|) ^ q.toReal = ∑ i, w i • (|v i| ^ q.toReal) := by
      simp only [smul_eq_mul]
      rw [haverage, hpower]
    have hall := ((strictConvexOn_rpow hpq.symm.lt).map_sum_eq_iff_of_pos
      (fun i _ ↦ hwpos i) hwsum (fun i _ ↦ abs_nonneg (v i))).mp hjensen
    have hneg (i : ι) : |v i| + v i = 0 := by
      have hz : (∑ j, (|v j| + v j)) = 0 := by rw [Finset.sum_add_distrib, habs, hsum]; ring
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ by linarith [neg_le_abs (v j)])).mp hz i (Finset.mem_univ _)
    intro i
    have hconstant : (∑ j, |v j|) = (Fintype.card ι : ℝ) * |v i| := by
      calc
        _ = ∑ _ : ι, |v i| := Finset.sum_congr rfl (fun j _ ↦ hall (Finset.mem_univ j) (Finset.mem_univ i))
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [habs] at hconstant
    have hi : |v i| = S / Fintype.card ι := (eq_div_iff hn.ne').mpr (by nlinarith)
    have hvi := hneg i
    rw [neg_div]
    linarith

set_option maxHeartbeats 1000000 in
theorem signed_mean_norm_iff {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞)
    {v : ι → ℝ} {S : ℝ} (hS : 0 ≤ S) (hsum : (∑ i, v i) = -S) :
    callNorm q v = (Fintype.card ι : ℝ) ^ (-(1 / p).toReal) * S ↔
      ∀ i, v i = -S / Fintype.card ι := by
  constructor
  · intro hnorm
    apply signed_mean_norm_unique (p := p) (q := q) hp hS hsum
    rw [hnorm, constant_signed_profile (p := p) (q := q) hS]
  · intro hall
    have hv : v = (fun _ : ι ↦ -S / Fintype.card ι) := funext hall
    rw [hv]
    exact constant_signed_profile (p := p) (q := q) hS

theorem scaled_signed_mean_norm_iff {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞)
    {v : ι → ℝ} {S : ℝ} (hS : 0 ≤ S) (hsum : (∑ i, v i) = -S) {a t : ℝ} (ht : 0 < t) :
    a + t * callNorm q v = a + t * (Fintype.card ι : ℝ) ^ (-(1 / p).toReal) * S ↔
      ∀ i, v i = -S / Fintype.card ι := by
  rw [← signed_mean_norm_iff (p := p) (q := q) hp hS hsum]
  constructor <;> intro hh <;> nlinarith

theorem additive_corner_equality {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞)
    (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (he : h.ChebyshevExact I) (hN : 0 < N)
    {a t : ℝ} (ht : 0 < t) :
    a + t * callNorm q (fun s : Fin N ↦ (h.response s).eval I.mu) =
      a + t * (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.additiveScale I N ↔
      ∀ s : Fin N, (h.response s).eval I.mu = -InexactRealizations.Lower.additiveScale I N / N := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  simpa only [Fintype.card_fin] using scaled_signed_mean_norm_iff (p := p) (q := q) hp
    (InexactRealizations.Risk.additiveScale_nonneg I N) (InexactRealizations.Lower.response_sum_mu h I he) (a := a) ht

theorem relative_corner_equality {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q] (hp : p ≠ ∞)
    (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (he : h.ChebyshevExact I) (hN : 0 < N) :
    callNorm q (fun s : Fin N ↦ InexactRealizations.Lower.physicalKernel h s I.mu I.mu) =
      (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.derivativeScale I N ↔
      ∀ s : Fin N, InexactRealizations.Lower.physicalKernel h s I.mu I.mu = -InexactRealizations.Lower.derivativeScale I N / N := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hD : 0 ≤ InexactRealizations.Lower.derivativeScale I N := by
    unfold InexactRealizations.Lower.derivativeScale
    have heps := (one_div_pos.mpr (I.den_pos N)).le
    have hDelta := I.delta_pos.le
    positivity
  simpa only [Fintype.card_fin] using signed_mean_norm_iff (p := p) (q := q) hp hD
    (InexactRealizations.Lower.kernel_sum_mu h I he)

end
end InexactRealizations.Budgets
