import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.MeanInequalities
import Mathlib.Basic.Real.ConjExponents

/-! The literal finite-call lp budget for every exponent in [1,infinity],
with both endpoints and a nonnegative Holder maximizer. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι]

def callNorm (p : ℝ≥0∞) (f : ι → ℝ) : ℝ := ‖WithLp.toLp p f‖
def Budget (p : ℝ≥0∞) (delta : ι → ℝ) : Prop := (∀ i, 0 ≤ delta i) ∧ callNorm p delta ≤ 1

theorem callNorm_one (f : ι → ℝ) : callNorm 1 f = ∑ i, |f i| := by
  simpa only [callNorm, Real.norm_eq_abs] using PiLp.norm_eq_of_L1 (WithLp.toLp 1 f)

theorem callNorm_top (f : ι → ℝ) : callNorm ∞ f = ⨆ i, |f i| := by
  simpa only [callNorm, Real.norm_eq_abs] using PiLp.norm_eq_ciSup (WithLp.toLp ∞ f)

theorem callNorm_finite {p : ℝ≥0∞} (hp : 0 < p.toReal) (f : ι → ℝ) :
    callNorm p f = (∑ i, |f i| ^ p.toReal) ^ (1 / p.toReal) := by
  simpa only [callNorm, Real.norm_eq_abs] using PiLp.norm_eq_sum hp (WithLp.toLp p f)

theorem callNorm_nonneg {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ι → ℝ) : 0 ≤ callNorm p f := norm_nonneg _

theorem coordinate_le_norm {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ι → ℝ) (i : ι) : |f i| ≤ callNorm p f := by
  simpa only [callNorm, Real.norm_eq_abs] using PiLp.norm_apply_le (WithLp.toLp p f) i

theorem Budget.coordinate {p : ℝ≥0∞} [Fact (1 ≤ p)] {delta : ι → ℝ} (h : Budget p delta) (i : ι) :
    delta i ≤ 1 := (le_abs_self _).trans ((coordinate_le_norm delta i).trans h.2)

set_option maxHeartbeats 1000000 in
theorem holder_budget {p q : ℝ≥0∞} [p.HolderConjugate q] (f delta : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hd : Budget p delta) : (∑ i, delta i * f i) ≤ callNorm q f := by
  let : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  by_cases hp : p = ∞
  · have hq : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one p q).mp hp
    rw [hq, callNorm_one]
    apply Finset.sum_le_sum
    intro i _
    simpa only [one_mul, abs_of_nonneg (hf i)] using mul_le_mul_of_nonneg_right (hd.coordinate i) (hf i)
  · by_cases hq : q = ∞
    · have hp1 : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q p).mp hq
      have hsum : (∑ i, delta i) ≤ 1 := by
        have hh := hd.2
        rw [hp1, callNorm_one] at hh
        simpa only [abs_of_nonneg (hd.1 _)] using hh
      have hmax (i : ι) : f i ≤ callNorm q f := (le_abs_self _).trans (coordinate_le_norm f i)
      have hh := Finset.sum_le_sum (s := Finset.univ)
        (fun i _ ↦ mul_le_mul_of_nonneg_left (hmax i) (hd.1 i))
      rw [← Finset.sum_mul] at hh
      nlinarith [mul_le_mul_of_nonneg_right hsum (callNorm_nonneg (p := q) f)]
    · have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
      have hh := Real.inner_le_Lp_mul_Lq Finset.univ delta f hpq
      have hh' : (∑ i, delta i * f i) ≤ callNorm p delta * callNorm q f := by
        simpa only [callNorm_finite hpq.pos, callNorm_finite hpq.symm.pos, Finset.mem_univ, true_and] using hh
      exact hh'.trans (by
        have hb := mul_le_mul_of_nonneg_right hd.2 (callNorm_nonneg (p := q) f)
        simpa only [one_mul] using hb)

set_option maxHeartbeats 1000000 in
theorem exists_holder_budget [Nonempty ι] {p q : ℝ≥0∞} [p.HolderConjugate q]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∃ delta : ι → ℝ, Budget p delta ∧ (∑ i, delta i * f i) = callNorm q f := by
  classical
  let : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  by_cases hp : p = ∞
  · have hq : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one p q).mp hp
    refine ⟨fun _ ↦ 1, ⟨fun _ ↦ zero_le_one, ?_⟩, ?_⟩
    · rw [hp, callNorm_top]
      simp only [abs_one, ciSup_const, le_refl]
    · rw [hq, callNorm_one]
      apply Finset.sum_congr rfl
      intro i _
      simp only [one_mul, abs_of_nonneg (hf i)]
  · by_cases hq : q = ∞
    · have hp1 : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q p).mp hq
      obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
      have hnorm : callNorm q f = f j := by
        apply le_antisymm
        · rw [hq, callNorm_top]
          exact ciSup_le (fun i ↦ by rw [abs_of_nonneg (hf i)]; exact hj i (Finset.mem_univ _))
        · exact (le_abs_self _).trans (coordinate_le_norm f j)
      refine ⟨fun i ↦ if i = j then 1 else 0, ⟨fun i ↦ by
        change 0 ≤ if i = j then (1 : ℝ) else 0
        split_ifs <;> positivity, ?_⟩, ?_⟩
      · rw [hp1, callNorm_one]
        simp only [apply_ite abs, abs_one, abs_zero]
        simp
      · rw [hnorm]
        simp
    · have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
      let fn : ι → ℝ≥0 := fun i ↦ ⟨f i, hf i⟩
      obtain ⟨delta, hdelta, hvalue⟩ := (NNReal.isGreatest_Lp Finset.univ fn hpq.symm).1
      refine ⟨fun i ↦ (delta i : ℝ), ⟨fun i ↦ (delta i).coe_nonneg, ?_⟩, ?_⟩
      · have hpower : (∑ i, (delta i : ℝ) ^ p.toReal) ≤ 1 := by exact_mod_cast hdelta
        rw [callNorm_finite hpq.pos]
        simp only [abs_of_nonneg (delta _).coe_nonneg]
        exact Real.rpow_le_one (Finset.sum_nonneg (fun i _ ↦ Real.rpow_nonneg (delta i).coe_nonneg _))
          hpower (by positivity)
      · have heq : (∑ i, f i * (delta i : ℝ)) = (∑ i, f i ^ q.toReal) ^ (1 / q.toReal) := by
          dsimp only [fn] at hvalue
          have hcast := congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) hvalue
          push_cast at hcast
          exact hcast
        rw [callNorm_finite hpq.symm.pos]
        simp only [abs_of_nonneg (hf _)]
        convert heq using 1
        apply Finset.sum_congr rfl
        intro i _
        ring

end
end InexactRealizations.Budgets
