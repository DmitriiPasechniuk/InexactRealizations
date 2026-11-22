import InexactRealizations.Budgets.FlatGain
import InexactRealizations.Comparisons.Classical.Gains
import InexactRealizations.Comparisons.Competitors.Prefix
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Theorem5.1(c): exact parity means and strict all-finite-gamma comparison, for every N>=4. -/

namespace InexactRealizations.Budgets.PrefixComparison
noncomputable section
open scoped BigOperators

theorem even_index_sum (N : ℕ) :
    (∑ s ∈ Finset.range N, if Even s then (s : ℝ) else 0) =
      (((N + 1) / 2 : ℕ) : ℝ) * ((((N + 1) / 2 : ℕ) : ℝ) - 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : Even N
    · have hp := Nat.even_iff.mp h
      have hc : (N + 1 + 1) / 2 = (N + 1) / 2 + 1 := by omega
      have hn : 2 * ((N + 1) / 2) = N := by omega
      have hnr : 2 * (((N + 1) / 2 : ℕ) : ℝ) = N := by exact_mod_cast hn
      simp only [h, ite_true, hc, Nat.cast_add, Nat.cast_one]
      nlinarith
    · have hp := Nat.not_even_iff.mp h
      have hc : (N + 1 + 1) / 2 = (N + 1) / 2 := by omega
      simp only [h, ite_false, hc, add_zero]

theorem odd_index_sum (N : ℕ) :
    (∑ s ∈ Finset.range N, if Even s then 0 else (s : ℝ)) =
      ((N / 2 : ℕ) : ℝ) ^ 2 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : Even N
    · have hp := Nat.even_iff.mp h
      have hc : (N + 1) / 2 = N / 2 := by omega
      simp only [h, ite_true, hc, add_zero]
    · have hp := Nat.not_even_iff.mp h
      have hc : (N + 1) / 2 = N / 2 + 1 := by omega
      have hn : 2 * (N / 2) + 1 = N := by omega
      have hnr : 2 * ((N / 2 : ℕ) : ℝ) + 1 = N := by exact_mod_cast hn
      simp only [h, ite_false, hc, Nat.cast_add, Nat.cast_one]
      nlinarith

def profile (N s : ℕ) : ℝ := if s = 0 then N / 2 else (N : ℝ) - s

theorem even_profile_sum (N : ℕ) (hN : 0 < N) :
    (∑ s ∈ Finset.range N, if Even s then profile N s else 0) =
      (((N + 1) / 2 : ℕ) : ℝ) * (N : ℝ) -
        (((N + 1) / 2 : ℕ) : ℝ) * ((((N + 1) / 2 : ℕ) : ℝ) - 1) - N / 2 := by
  have he (s : ℕ) : (if Even s then profile N s else 0) =
      (if Even s then (N : ℝ) else 0) - (if Even s then (s : ℝ) else 0) -
        (if s = 0 then (N : ℝ) / 2 else 0) := by
    by_cases hs : s = 0
    · subst s; simp [profile]; ring
    · simp only [profile, hs, ite_false, sub_zero]
      split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, even_index_sum,
    InexactRealizations.Balanced.sum_parity]
  simp [(show 0 ∈ Finset.range N from Finset.mem_range.mpr hN)]

theorem odd_profile_sum (N : ℕ) :
    (∑ s ∈ Finset.range N, if Even s then 0 else profile N s) =
      ((N / 2 : ℕ) : ℝ) * (N : ℝ) - ((N / 2 : ℕ) : ℝ) ^ 2 := by
  have he (s : ℕ) : (if Even s then 0 else profile N s) =
      (if Even s then 0 else (N : ℝ)) - (if Even s then 0 else (s : ℝ)) := by
    by_cases hs : s = 0
    · subst s; simp
    · simp only [profile, hs, ite_false]
      split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, odd_index_sum, InexactRealizations.Balanced.sum_parity]
  simp

def evenCalls (N : ℕ) := (Finset.range N).filter Even
def oddCalls (N : ℕ) := (Finset.range N).filter (fun s ↦ ¬ Even s)

theorem evenCalls_card (N : ℕ) : (evenCalls N).card = (N + 1) / 2 := by
  have hh := InexactRealizations.Balanced.sum_parity N (1 : ℝ) 0
  have he : ((evenCalls N).card : ℝ) = (((N + 1) / 2 : ℕ) : ℝ) := by
    simpa [evenCalls, ← Finset.sum_filter] using hh
  exact_mod_cast he

theorem oddCalls_card (N : ℕ) : (oddCalls N).card = N / 2 := by
  have hh := InexactRealizations.Balanced.sum_parity N (0 : ℝ) 1
  have he : ((oddCalls N).card : ℝ) = ((N / 2 : ℕ) : ℝ) := by
    calc
      _ = ∑ s ∈ oddCalls N, (1 : ℝ) := by simp
      _ = ∑ s ∈ Finset.range N, if Even s then (0 : ℝ) else 1 := by
        rw [oddCalls, Finset.sum_filter]
        simp only [ite_not]
      _ = _ := by simpa only [mul_zero, zero_add, mul_one] using hh
  exact_mod_cast he

theorem even_profile_mean (N : ℕ) (hN : 2 ≤ N) :
    (∑ s ∈ evenCalls N, profile N s) =
      (evenCalls N).card * InexactRealizations.Balanced.classMass N 0 := by
  rw [evenCalls_card, evenCalls, Finset.sum_filter, even_profile_sum N (by omega)]
  by_cases h : Even N
  · have hp := Nat.even_iff.mp h
    have hn : 2 * ((N + 1) / 2) = N := by omega
    have hnr : 2 * (((N + 1) / 2 : ℕ) : ℝ) = N := by exact_mod_cast hn
    simp only [InexactRealizations.Balanced.classMass, h, ite_true]
    nlinarith
  · have hp := Nat.not_even_iff.mp h
    have hn : 2 * ((N + 1) / 2) = N + 1 := by omega
    have hnr : 2 * (((N + 1) / 2 : ℕ) : ℝ) = (N : ℝ) + 1 := by exact_mod_cast hn
    simp only [InexactRealizations.Balanced.classMass, h, ite_false, show Even (0 : ℕ) by decide, ite_true]
    have hmean : (((N + 1) / 2 : ℕ) : ℝ) = ((N : ℝ) + 1) / 2 := by linarith
    rw [hmean]
    field_simp
    ring

theorem odd_profile_mean (N : ℕ) (_hN : 2 ≤ N) :
    (∑ s ∈ oddCalls N, profile N s) =
      (oddCalls N).card * InexactRealizations.Balanced.classMass N 1 := by
  have hs : (∑ s ∈ oddCalls N, profile N s) =
      (∑ s ∈ Finset.range N, if Even s then 0 else profile N s) := by
    rw [oddCalls, Finset.sum_filter]
    simp only [ite_not]
  rw [hs, odd_profile_sum, oddCalls_card]
  by_cases h : Even N
  · have hp := Nat.even_iff.mp h
    have hn : 2 * (N / 2) = N := by omega
    have hnr : 2 * ((N / 2 : ℕ) : ℝ) = N := by exact_mod_cast hn
    simp only [InexactRealizations.Balanced.classMass, h, ite_true]
    nlinarith
  · have hp := Nat.not_even_iff.mp h
    have hn : 2 * (N / 2) + 1 = N := by omega
    have hnr : 2 * ((N / 2 : ℕ) : ℝ) + 1 = N := by exact_mod_cast hn
    simp only [InexactRealizations.Balanced.classMass, h, ite_false, show ¬Even (1 : ℕ) by decide]
    nlinarith

theorem mean_power_le (S : Finset ℕ) (hS : S.Nonempty) (f : ℕ → ℝ) (hf : ∀ i ∈ S, 0 ≤ f i)
    (a : ℝ) (ha : 1 < a) (m : ℝ) (hm : (∑ i ∈ S, f i) = S.card * m) :
    S.card * m ^ a ≤ ∑ i ∈ S, f i ^ a := by
  have hc : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  let w : ℕ → ℝ := fun _ ↦ 1 / S.card
  have hw : (∑ i ∈ S, w i) = 1 := by simp [w, hc.ne']
  have hmean : (∑ i ∈ S, w i • f i) = m := by
    simp only [w, smul_eq_mul, ← Finset.mul_sum, hm]
    field_simp
  have hh := (strictConvexOn_rpow ha).convexOn.map_sum_le
    (fun i (_ : i ∈ S) ↦ (one_div_pos.mpr hc).le) hw hf
  rw [hmean] at hh
  simp only [smul_eq_mul, ← Finset.mul_sum] at hh
  have he : (1 / (S.card : ℝ)) * (∑ i ∈ S, f i ^ a) = (∑ i ∈ S, f i ^ a) / S.card := by ring
  rw [he] at hh
  simpa only [mul_comm] using (le_div_iff₀ hc).mp hh

theorem mean_power_lt (S : Finset ℕ) (hS : S.Nonempty) (f : ℕ → ℝ) (hf : ∀ i ∈ S, 0 ≤ f i)
    (a : ℝ) (ha : 1 < a) (m : ℝ) (hm : (∑ i ∈ S, f i) = S.card * m)
    (hne : ∃ i ∈ S, ∃ j ∈ S, f i ≠ f j) :
    S.card * m ^ a < ∑ i ∈ S, f i ^ a := by
  have hc : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  let w : ℕ → ℝ := fun _ ↦ 1 / S.card
  have hw : (∑ i ∈ S, w i) = 1 := by simp [w, hc.ne']
  have hmean : (∑ i ∈ S, w i • f i) = m := by
    simp only [w, smul_eq_mul, ← Finset.mul_sum, hm]
    field_simp
  have hh := (strictConvexOn_rpow ha).map_sum_lt
    (fun i (_ : i ∈ S) ↦ one_div_pos.mpr hc) hw hf hne
  rw [hmean] at hh
  simp only [smul_eq_mul, ← Finset.mul_sum] at hh
  have he : (1 / (S.card : ℝ)) * (∑ i ∈ S, f i ^ a) = (∑ i ∈ S, f i ^ a) / S.card := by ring
  rw [he] at hh
  simpa only [mul_comm] using (lt_div_iff₀ hc).mp hh

theorem profile_nonneg (N s : ℕ) (hs : s < N) : 0 ≤ profile N s := by
  unfold profile
  split_ifs
  · positivity
  · exact sub_nonneg.mpr (by exact_mod_cast hs.le)

theorem classMass_parity (N s : ℕ) : InexactRealizations.Balanced.classMass N s =
    if Even s then InexactRealizations.Balanced.classMass N 0 else InexactRealizations.Balanced.classMass N 1 := by
  by_cases hN : Even N <;> by_cases hs : Even s <;>
    simp only [InexactRealizations.Balanced.classMass, hN, hs, ite_true, ite_false,
      show Even (0 : ℕ) by decide, show ¬Even (1 : ℕ) by decide]

theorem classMass_power_sum (N : ℕ) (a : ℝ) :
    (∑ s ∈ Finset.range N, InexactRealizations.Balanced.classMass N s ^ a) =
      (evenCalls N).card * InexactRealizations.Balanced.classMass N 0 ^ a +
        (oddCalls N).card * InexactRealizations.Balanced.classMass N 1 ^ a := by
  rw [evenCalls_card, oddCalls_card]
  have he (s : ℕ) : InexactRealizations.Balanced.classMass N s ^ a =
      if Even s then InexactRealizations.Balanced.classMass N 0 ^ a else InexactRealizations.Balanced.classMass N 1 ^ a := by
    rw [classMass_parity N s]
    split_ifs <;> rfl
  calc
    _ = ∑ s ∈ Finset.range N, if Even s then InexactRealizations.Balanced.classMass N 0 ^ a else
        InexactRealizations.Balanced.classMass N 1 ^ a := Finset.sum_congr rfl (fun s _ ↦ he s)
    _ = _ := InexactRealizations.Balanced.sum_parity N _ _

theorem balanced_power_sum_lt_prefix (N : ℕ) (hN : 4 ≤ N) (a : ℝ) (ha : 1 < a) :
    (∑ s ∈ Finset.range N, InexactRealizations.Balanced.classMass N s ^ a) <
      ∑ s ∈ Finset.range N, profile N s ^ a := by
  have he0 : 0 ∈ evenCalls N := by simp [evenCalls, show 0 < N by omega]
  have ho1 : 1 ∈ oddCalls N := by simp [oddCalls, show 1 < N by omega]
  have ho3 : 3 ∈ oddCalls N := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by decide⟩
  have he := mean_power_le (evenCalls N) ⟨0, he0⟩ (profile N)
    (fun i hi ↦ profile_nonneg N i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))
    a ha (InexactRealizations.Balanced.classMass N 0) (even_profile_mean N (by omega))
  have ho := mean_power_lt (oddCalls N) ⟨1, ho1⟩ (profile N)
    (fun i hi ↦ profile_nonneg N i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))
    a ha (InexactRealizations.Balanced.classMass N 1) (odd_profile_mean N (by omega))
    ⟨1, ho1, 3, ho3, by simp only [profile, Nat.one_ne_zero, ite_false, show (3 : ℕ) ≠ 0 by decide]; norm_num⟩
  rw [classMass_power_sum, ← Finset.sum_filter_add_sum_filter_not (Finset.range N) Even]
  exact add_lt_add_of_le_of_lt he ho

open scoped ENNReal NNReal

theorem balanced_finite_norm_lt_prefix {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (N : ℕ) (hN : 4 ≤ N) (hq : 1 < q.toReal) :
    callNorm q (fun s : Fin N ↦ InexactRealizations.Balanced.classMass N s) <
      callNorm q (fun s : Fin N ↦ profile N s) := by
  rw [callNorm_finite (zero_lt_one.trans hq), callNorm_finite (zero_lt_one.trans hq)]
  simp only [abs_of_nonneg (InexactRealizations.Balanced.classMass_pos (by omega : 2 ≤ N)).le,
    abs_of_nonneg (profile_nonneg N _ (Fin.isLt _))]
  apply Real.rpow_lt_rpow (Finset.sum_nonneg (fun s _ ↦ Real.rpow_nonneg
    (InexactRealizations.Balanced.classMass_pos (by omega : 2 ≤ N)).le _))
    ?_ (one_div_pos.mpr (zero_lt_one.trans hq))
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ ↦ InexactRealizations.Balanced.classMass N s ^ q.toReal) N,
    Fin.sum_univ_eq_sum_range (fun s : ℕ ↦ profile N s ^ q.toReal) N]
  exact balanced_power_sum_lt_prefix N hN q.toReal hq

theorem classMass_le (N s : ℕ) (_hN : 2 ≤ N) :
    InexactRealizations.Balanced.classMass N s ≤ ((N : ℝ) + 1) / 2 := by
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  unfold InexactRealizations.Balanced.classMass
  split_ifs
  · linarith
  · apply (div_le_iff₀ (by positivity : 0 < 2 * ((N : ℝ) + 1))).mpr
    nlinarith
  · exact le_rfl

theorem balanced_top_norm_lt_prefix (N : ℕ) (hN : 4 ≤ N) :
    callNorm ∞ (fun s : Fin N ↦ InexactRealizations.Balanced.classMass N s) <
      callNorm ∞ (fun s : Fin N ↦ profile N s) := by
  let : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hb : callNorm ∞ (fun s : Fin N ↦ InexactRealizations.Balanced.classMass N s) ≤ ((N : ℝ) + 1) / 2 := by
    rw [callNorm_top]
    apply ciSup_le
    intro s
    rw [abs_of_pos (InexactRealizations.Balanced.classMass_pos (by omega : 2 ≤ N))]
    exact classMass_le N s (by omega)
  have hp := coordinate_le_norm (p := ∞) (fun s : Fin N ↦ profile N s) ⟨1, by omega⟩
  have hn : (3 : ℝ) < N := by exact_mod_cast (show 3 < N by omega)
  have hp1 : profile N 1 = (N : ℝ) - 1 := by simp [profile]
  change |profile N 1| ≤ callNorm ∞ (fun s : Fin N ↦ profile N s) at hp
  rw [hp1, abs_of_pos (by linarith : 0 < (N : ℝ) - 1)] at hp
  linarith

theorem prefix_gain_profile {p q : ℝ≥0∞} [p.HolderConjugate q]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N) (symmetric : Bool) :
    operatorGain p (InexactRealizations.Classical.history I N) I symmetric =
      (4 * I.epsilon N / I.delta) * callNorm q (fun s : Fin N ↦ profile N s) := by
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hc : 0 < 4 * I.epsilon N / I.delta :=
    div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos
  have he := operatorGain_of_common_peaks (p := p) (q := q)
    (InexactRealizations.Classical.history I N) I hN symmetric
    (fun s ↦ InexactRealizations.Classical.responseBound I N s) (fun s ↦ InexactRealizations.Classical.queryBound I s)
    (InexactRealizations.Classical.responseBounds I N hN) (fun s ↦ (InexactRealizations.Classical.queryBound_pos I s).le)
    (fun s _ hx ↦ InexactRealizations.Classical.query_bound I N s hx)
    I.mu I.mu ⟨le_rfl, I.mu_lt_L.le⟩ ⟨le_rfl, I.mu_lt_L.le⟩
    (fun s ↦ by rw [InexactRealizations.Classical.response_endpoint I N hN,
      abs_neg, abs_of_pos (InexactRealizations.Classical.responseBound_pos I s)])
    (fun s ↦ by rw [InexactRealizations.Classical.query_endpoint, abs_of_pos (InexactRealizations.Classical.queryBound_pos I s)])
  have hf : (fun s : Fin N ↦ InexactRealizations.Classical.responseBound I N s * InexactRealizations.Classical.queryBound I s) =
      (fun s : Fin N ↦ (4 * I.epsilon N / I.delta) * profile N s) := by
    funext s
    rw [InexactRealizations.Classical.bound_product]
    by_cases hs : s.val = 0 <;> simp only [profile, InexactRealizations.Classical.initialWeight, hs, ite_true, ite_false] <;> ring
  rw [he, hf, callNorm_mul, abs_of_pos hc]

theorem balanced_gain_normalized {p q : ℝ≥0∞} [p.HolderConjugate q]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (symmetric : Bool) :
    operatorGain p (InexactRealizations.Balanced.history I N hN) I symmetric =
      (4 * I.epsilon N / I.delta) * callNorm q (fun s : Fin N ↦ InexactRealizations.Balanced.classMass N s) := by
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hc : 0 < 4 * I.epsilon N / I.delta :=
    div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos
  rw [balanced_gain_profile (p := p) (q := q) I hN symmetric]
  have hf : (fun s : Fin N ↦ InexactRealizations.Balanced.responseBound I N s * InexactRealizations.Balanced.queryBound I N s) =
      (fun s : Fin N ↦ (4 * I.epsilon N / I.delta) * InexactRealizations.Balanced.classMass N s) := by
    funext s
    exact InexactRealizations.Balanced.bound_product I hN s.isLt
  rw [hf, callNorm_mul, abs_of_pos hc]

theorem balanced_lt_prefix_all_finite_gamma (p : ℝ≥0∞) (hp : 1 ≤ p) (hpf : p ≠ ∞)
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 4 ≤ N) (r : ℝ) (hr : 0 < r) :
    localRelativeGain p (InexactRealizations.Balanced.history I N (by omega)) I r <
      localRelativeGain p (InexactRealizations.Comparisons.Competitors.Prefix.history I N) I r := by
  let q := dualExponent p
  let : p.HolderConjugate q := holder_dualExponent p hp
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  rw [InexactRealizations.Comparisons.Competitors.Prefix.history_eq_classical,
    localRelativeGain_eq_operatorGain p hp _ I r hr,
    localRelativeGain_eq_operatorGain p hp _ I r hr,
    balanced_gain_normalized (p := p) (q := q), prefix_gain_profile (p := p) (q := q) I N (by omega)]
  apply mul_lt_mul_of_pos_left _
    (div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos)
  by_cases hq : q = ∞
  · rw [hq]
    exact balanced_top_norm_lt_prefix N hN
  · have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hpf hq
    exact balanced_finite_norm_lt_prefix N hN hpq.symm.lt

end
end InexactRealizations.Budgets.PrefixComparison
