import InexactRealizations.Budgets.PrefixComparison
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Theorem5.1(e): a uniform strict gap over all odd-horizon Chebyshev-exact histories. -/

namespace InexactRealizations.Budgets.OddGap
noncomputable section
open Polynomial Filter Topology
open scoped BigOperators ENNReal NNReal
variable {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]

theorem callNorm_neg {J : Type*} [Fintype J] [Fact (1 ≤ q)] (v : J → ℝ) :
    callNorm q (fun i ↦ -v i) = callNorm q v := by
  simpa only [neg_one_mul, abs_neg, abs_one, one_mul] using callNorm_mul (p := q) (-1) v

theorem constant_positive_norm (hN : 0 < N) {S : ℝ} (hS : 0 ≤ S) :
    callNorm q (fun _ : Fin N ↦ S / N) = (N : ℝ) ^ (-(1 / p).toReal) * S := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hh := constant_signed_profile (ι := Fin N) (p := p) (q := q) hS
  simp only [Fintype.card_fin] at hh
  rw [neg_div, callNorm_neg] at hh
  exact hh

include p in
theorem abs_sum_le_of_norm_const (hN : 0 < N) (v : Fin N → ℝ) {S : ℝ} (hS : 0 ≤ S)
    (hv : callNorm q v ≤ callNorm q (fun _ : Fin N ↦ S / N)) : (∑ i, |v i|) ≤ S := by
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hc : 0 < (N : ℝ) ^ (-(1 / p).toReal) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  have hh := holder_budget (p := p) (q := q) (fun i ↦ |v i|)
    (fun _ : Fin N ↦ (N : ℝ) ^ (-(1 / p).toReal)) (fun _ ↦ abs_nonneg _)
      (by simpa only [Fintype.card_fin] using (uniform_budget (p := p) (ι := Fin N)))
  rw [← Finset.mul_sum, callNorm_abs] at hh
  rw [constant_positive_norm (p := p) hN hS] at hv
  exact (mul_le_mul_iff_right₀ hc).mp (hh.trans hv)

theorem positive_mean_unique (hN : 0 < N) (hp : p ≠ ∞) (v : Fin N → ℝ)
    {S : ℝ} (hS : 0 ≤ S) (hs : (∑ i, v i) = S)
    (hv : callNorm q v ≤ callNorm q (fun _ : Fin N ↦ S / N)) : ∀ i, v i = S / N := by
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hh := signed_sum_bound (p := p) (q := q) v
  rw [Fintype.card_fin, hs, abs_of_nonneg hS] at hh
  rw [constant_positive_norm (p := p) hN hS] at hv
  have hn : callNorm q (fun i ↦ -v i) = callNorm q (fun _ : Fin N ↦ -S / N) := by
    rw [callNorm_neg, neg_div, callNorm_neg, constant_positive_norm (p := p) hN hS]
    exact le_antisymm hv hh
  have hsum : (∑ i, -v i) = -S := by rw [Finset.sum_neg_distrib, hs]
  have he := signed_mean_norm_unique (p := p) (q := q) hp hS hsum (by simpa only [Fintype.card_fin] using hn)
  intro i
  have hi := he i
  simp only [Fintype.card_fin] at hi
  rw [neg_div] at hi
  linarith

theorem product_abs_constant (c : ℝ) (hc : 0 < c) (a b : Fin N → ℝ)
    (hab : ∀ i, a i * b i = c ^ 2)
    (ha : (∑ i, |a i|) ≤ N * c) (hb : (∑ i, |b i|) ≤ N * c) :
    ∀ i, |a i| = c ∧ |b i| = c := by
  have hp (i : Fin N) : |a i| * |b i| = c ^ 2 := by
    rw [← abs_mul, hab i, abs_of_nonneg (sq_nonneg c)]
  have hge (i : Fin N) : 0 ≤ |a i| + |b i| - 2 * c := by
    have hsq := sq_nonneg (|a i| - |b i|)
    have hsum : 0 ≤ |a i| + |b i| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    nlinarith [hp i]
  have hz : (∑ i, (|a i| + |b i| - 2 * c)) = 0 := by
    have hn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦ hge i)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hn ⊢
    nlinarith
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) ↦ hge j)).mp hz i (Finset.mem_univ _)
  constructor <;> nlinarith [hp i, sq_nonneg (|a i| - c), sq_nonneg (|b i| - c)]

abbrev CornerArray (N : ℕ) := Fin 4 → Fin N → ℝ

def energy (X : CornerArray N) : ℝ :=
  3 / 8 * ((∑ i, X 0 i ^ 2) + ∑ i, X 3 i ^ 2) +
    1 / 8 * ((∑ i, X 1 i ^ 2) + ∑ i, X 2 i ^ 2)

def Feasible (X : CornerArray N) : Prop :=
  (∑ i, X 0 i) = (N : ℝ) ^ 2 / 2 ∧
  (∑ i, X 3 i) = (N : ℝ) ^ 2 / 2 ∧
  (∀ i, X 0 i * X 3 i = X 1 i * X 2 i) ∧
  InexactRealizations.Lower.oddEnergy N ≤ energy X

def objective (q : ℝ≥0∞) (X : CornerArray N) : ℝ :=
  max (max (callNorm q (X 0)) (callNorm q (X 1))) (max (callNorm q (X 2)) (callNorm q (X 3)))

theorem norm_le_objective (q : ℝ≥0∞) (X : CornerArray N) (j : Fin 4) :
    callNorm q (X j) ≤ objective q X := by
  fin_cases j
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem feasible_objective_gt (hN : 3 ≤ N) (hp : p ≠ ∞) (X : CornerArray N) (hX : Feasible X) :
    callNorm q (fun _ : Fin N ↦ (N : ℝ) / 2) < objective q X := by
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hS : 0 ≤ (N : ℝ) ^ 2 / 2 := by positivity
  by_contra hle
  have hcap := le_of_not_gt hle
  have hbase : (N : ℝ) ^ 2 / 2 / N = (N : ℝ) / 2 := by field_simp
  have hd0 := positive_mean_unique (p := p) (q := q) (by omega) hp (X 0) hS hX.1
    (by rw [hbase]; exact (norm_le_objective q X 0).trans hcap)
  have hd3 := positive_mean_unique (p := p) (q := q) (by omega) hp (X 3) hS hX.2.1
    (by rw [hbase]; exact (norm_le_objective q X 3).trans hcap)
  simp only [hbase] at hd0 hd3
  have hpairs (i : Fin N) : X 1 i * X 2 i = ((N : ℝ) / 2) ^ 2 := by
    rw [← hX.2.2.1 i, hd0, hd3, pow_two]
  have hab (j : Fin 4) : (∑ i, |X j i|) ≤ N * ((N : ℝ) / 2) := by
    have hh := abs_sum_le_of_norm_const (p := p) (q := q) (by omega) (X j) hS
      (by rw [hbase]; exact (norm_le_objective q X j).trans hcap)
    nlinarith
  have hoff := product_abs_constant ((N : ℝ) / 2) (by positivity) (X 1) (X 2) hpairs (hab 1) (hab 2)
  have hs (j : Fin 4) : (∑ i, X j i ^ 2) = N * ((N : ℝ) / 2) ^ 2 := by
    have he (i : Fin N) : X j i ^ 2 = ((N : ℝ) / 2) ^ 2 := by
      fin_cases j
      · change X 0 i ^ 2 = _
        rw [hd0]
      · change X 1 i ^ 2 = _
        rw [← sq_abs, (hoff i).1]
      · change X 2 i ^ 2 = _
        rw [← sq_abs, (hoff i).2]
      · change X 3 i ^ 2 = _
        rw [hd3]
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have he : energy X = (N : ℝ) ^ 3 / 4 := by rw [energy, hs, hs, hs, hs]; ring
  have hstrict : (N : ℝ) ^ 3 / 4 < InexactRealizations.Lower.oddEnergy N := by
    unfold InexactRealizations.Lower.oddEnergy
    have hnm : 0 < (N : ℝ) - 1 := by
      have hnr : (3 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hg : 0 < (N : ℝ) * ((N : ℝ) - 1) / (4 * ((N : ℝ) + 1)) := by positivity
    linarith
  exact (hstrict.trans_le (he ▸ hX.2.2.2)).false

theorem continuous_objective (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    Continuous (objective q : CornerArray N → ℝ) := by
  have hc (j : Fin 4) : Continuous (fun X : CornerArray N ↦ callNorm q (X j)) :=
    continuous_norm.comp ((PiLp.continuous_toLp q (fun _ : Fin N ↦ ℝ)).comp (continuous_apply j))
  exact ((hc 0).max (hc 1)).max ((hc 2).max (hc 3))

theorem closed_feasible : IsClosed {X : CornerArray N | Feasible X} := by
  unfold Feasible
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (isClosed_eq (by fun_prop) continuous_const).inter
    ((isClosed_eq (by fun_prop) continuous_const).inter (?_))
  exact (isClosed_iInter (fun i ↦ isClosed_eq (by fun_prop) (by fun_prop))).inter
    (isClosed_le continuous_const (by unfold energy; fun_prop))

theorem norm_le_objective_value (q : ℝ≥0∞) [Fact (1 ≤ q)] (X : CornerArray N) :
    ‖X‖ ≤ objective q X := by
  have h0 : 0 ≤ objective q X := (callNorm_nonneg (X 0)).trans (norm_le_objective q X 0)
  apply (pi_norm_le_iff_of_nonneg h0).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg h0).mpr
  intro i
  rw [Real.norm_eq_abs]
  exact (coordinate_le_norm (p := q) (X j) i).trans (norm_le_objective q X j)

theorem compact_sublevel (q : ℝ≥0∞) [Fact (1 ≤ q)] (B : ℝ) :
    IsCompact {X : CornerArray N | Feasible X ∧ objective q X ≤ B} := by
  have hclosed : IsClosed {X : CornerArray N | Feasible X ∧ objective q X ≤ B} :=
    closed_feasible.inter (isClosed_le (continuous_objective q) continuous_const)
  apply (isCompact_closedBall (0 : CornerArray N) B).of_isClosed_subset hclosed
  intro X hX
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_objective_value q X).trans hX.2

theorem exists_uniform_gap (hN : 3 ≤ N) (hp : p ≠ ∞)
    (X0 : CornerArray N) (hX0 : Feasible X0) :
    ∃ m : ℝ, callNorm q (fun _ : Fin N ↦ (N : ℝ) / 2) < m ∧
      ∀ X : CornerArray N, Feasible X → m ≤ objective q X := by
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let S := {X : CornerArray N | Feasible X ∧ objective q X ≤ objective q X0}
  obtain ⟨Y, hY, hmin⟩ := (compact_sublevel q (objective q X0)).exists_isMinOn
    (show S.Nonempty from ⟨X0, hX0, le_rfl⟩) (continuous_objective q).continuousOn
  refine ⟨objective q Y, feasible_objective_gt (p := p) (q := q) hN hp Y hY.1, ?_⟩
  intro X hX
  by_cases hx : objective q X ≤ objective q X0
  · exact hmin ⟨hX, hx⟩
  · exact hY.2.trans (le_of_not_ge hx)

def chartArray (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) : CornerArray N :=
  ![fun i ↦ (h.chartFactor I i).eval 1 * (h.chartQuery I i).eval 1,
    fun i ↦ (h.chartFactor I i).eval 1 * (h.chartQuery I i).eval (-1),
    fun i ↦ (h.chartFactor I i).eval (-1) * (h.chartQuery I i).eval 1,
    fun i ↦ (h.chartFactor I i).eval (-1) * (h.chartQuery I i).eval (-1)]

theorem chartArray_feasible (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 3 ≤ N) (hodd : Odd N) : Feasible (chartArray h I) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (∑ i, (h.chartFactor I i).eval 1 * (h.chartQuery I i).eval 1) = _
    rw [h.chart_factorization I he, InexactRealizations.Lower.chebyshevBezout_one_one]
  · change (∑ i, (h.chartFactor I i).eval (-1) * (h.chartQuery I i).eval (-1)) = _
    rw [h.chart_factorization I he, InexactRealizations.Lower.chebyshevBezout_neg_one_neg_one N hodd]
  · intro i
    change (h.chartFactor I i).eval 1 * (h.chartQuery I i).eval 1 *
        ((h.chartFactor I i).eval (-1) * (h.chartQuery I i).eval (-1)) =
      (h.chartFactor I i).eval 1 * (h.chartQuery I i).eval (-1) *
        ((h.chartFactor I i).eval (-1) * (h.chartQuery I i).eval 1)
    ring
  · have hh := InexactRealizations.Lower.history_chart_four_corner_lower h I he hN hodd
    simpa [energy, chartArray, InexactRealizations.Lower.fourCornerEnergy, Finset.sum_add_distrib] using hh

theorem chart_pair_norm_bound (hN : 0 < N) (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (x y : ℝ)
    (hx : (InexactRealizations.GradedFamily.chart I).eval x ∈ Set.Icc I.mu I.L)
    (hy : (InexactRealizations.GradedFamily.chart I).eval y ∈ Set.Icc I.mu I.L) :
    callNorm q (fun i : Fin N ↦ (h.chartFactor I i).eval x * (h.chartQuery I i).eval y) ≤
      (I.delta / (4 * I.epsilon N)) * operatorGain p h I false := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hc : 0 < I.delta / (4 * I.epsilon N) :=
    div_pos I.delta_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N)))
  have hp : (fun i : Fin N ↦ (h.chartFactor I i).eval x * (h.chartQuery I i).eval y) =
      (fun i : Fin N ↦ (-I.delta / (4 * I.epsilon N)) *
        InexactRealizations.Lower.physicalKernel h i ((InexactRealizations.GradedFamily.chart I).eval x)
          ((InexactRealizations.GradedFamily.chart I).eval y)) := by
    funext i
    simp only [InexactRealizations.History.chartFactor, InexactRealizations.History.chartQuery, eval_mul, eval_C, eval_comp,
      InexactRealizations.Lower.physicalKernel]
    ring
  rw [hp, callNorm_mul, neg_div, abs_neg, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left (operator_kernel_lower (p := p) (q := q) h I false _ _ hx hy) hc.le

theorem chart_objective_bound (hN : 0 < N) (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) : objective q (chartArray h I) ≤
      (I.delta / (4 * I.epsilon N)) * operatorGain p h I false := by
  have hp : (InexactRealizations.GradedFamily.chart I).eval 1 ∈ Set.Icc I.mu I.L := by
    rw [InexactRealizations.Lower.chart_eval_one]; exact ⟨le_rfl, I.mu_lt_L.le⟩
  have hm : (InexactRealizations.GradedFamily.chart I).eval (-1) ∈ Set.Icc I.mu I.L := by
    rw [InexactRealizations.Lower.chart_eval_neg_one]; exact ⟨I.mu_lt_L.le, le_rfl⟩
  exact max_le (max_le (chart_pair_norm_bound (p := p) (q := q) hN h I 1 1 hp hp)
    (chart_pair_norm_bound (p := p) (q := q) hN h I 1 (-1) hp hm))
    (max_le (chart_pair_norm_bound (p := p) (q := q) hN h I (-1) 1 hm hp)
      (chart_pair_norm_bound (p := p) (q := q) hN h I (-1) (-1) hm hm))

theorem exists_history_gap (p : ℝ≥0∞) (hp : 1 ≤ p) (hpf : p ≠ ∞)
    (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (hodd : Odd N) :
    ∃ G : ℝ, (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.derivativeScale I N < G ∧
      ∀ h : InexactRealizations.History N, h.ChebyshevExact I → ∀ r : ℝ, 0 < r → G ≤ localRelativeGain p h I r := by
  let q := dualExponent p
  let : p.HolderConjugate q := holder_dualExponent p hp
  have hN3 : 3 ≤ N := by have hn := Nat.odd_iff.mp hodd; omega
  let H0 := InexactRealizations.Balanced.history I N hN
  have hH0 := chartArray_feasible H0 I (InexactRealizations.Balanced.history_exact I N hN) hN3 hodd
  obtain ⟨m, hm, hmin⟩ := exists_uniform_gap (p := p) (q := q) hN3 hpf (chartArray H0 I) hH0
  let c := 4 * I.epsilon N / I.delta
  have hc : 0 < c := div_pos (mul_pos (by norm_num) (one_div_pos.mpr (I.den_pos N))) I.delta_pos
  have hbase : c * callNorm q (fun _ : Fin N ↦ (N : ℝ) / 2) =
      (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.derivativeScale I N := by
    have he : (N : ℝ) ^ 2 / 2 / N = (N : ℝ) / 2 := by field_simp
    rw [← he, constant_positive_norm (p := p) (q := q) (by omega) (by positivity)]
    dsimp only [c]
    unfold InexactRealizations.Lower.derivativeScale
    ring
  refine ⟨c * m, ?_, ?_⟩
  · rw [← hbase]
    exact mul_lt_mul_of_pos_left hm hc
  · intro h he r hr
    rw [localRelativeGain_eq_operatorGain p hp h I r hr]
    have hh := (hmin _ (chartArray_feasible h I he hN3 hodd)).trans
      (chart_objective_bound (p := p) (q := q) (by omega) h I)
    have hmul := mul_le_mul_of_nonneg_left hh hc.le
    have heq : c * (I.delta / (4 * I.epsilon N)) = 1 := by
      have heps : I.epsilon N ≠ 0 := (one_div_pos.mpr (I.den_pos N)).ne'
      dsimp only [c]
      field_simp [I.delta_pos.ne', heps]
    simpa only [← mul_assoc, heq, one_mul] using hmul

def historyValues (p : ℝ≥0∞) (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (r : ℝ) : Set ℝ :=
  {v | ∃ h : InexactRealizations.History N, h.ChebyshevExact I ∧ v = localRelativeGain p h I r}

theorem odd_infimum_gap (p : ℝ≥0∞) (hp : 1 ≤ p) (hpf : p ≠ ∞)
    (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (hodd : Odd N) (r : ℝ) (hr : 0 < r) :
    (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.derivativeScale I N <
      sInf (historyValues p I N r) := by
  obtain ⟨G, hG, hbound⟩ := exists_history_gap p hp hpf I hN hodd
  apply hG.trans_le
  apply le_csInf (s := historyValues p I N r)
    ⟨localRelativeGain p (InexactRealizations.Balanced.history I N hN) I r,
    InexactRealizations.Balanced.history I N hN, InexactRealizations.Balanced.history_exact I N hN, rfl⟩
  rintro v ⟨h, he, rfl⟩
  exact hbound h he r hr

end
end InexactRealizations.Budgets.OddGap
