import InexactRealizations.Budgets.JournalDuality
import InexactRealizations.Budgets.Flat
import InexactRealizations.Budgets.PeakProfiles
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Polynomial.Roots
import InexactRealizations.Synthesis.Normalized

/-! Theorem5.1(b): the exact per-call peak criterion, including necessity at zero endpoint responses. -/

namespace InexactRealizations.Budgets.PeakCriterion
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Filter Topology
open scoped BigOperators ENNReal NNReal
variable {N : ℕ}

def mixtureNorm (a b : Fin N → ℝ) (u : ℝ) (s : Fin N) : ℝ :=
  Real.sqrt ((1 - u) * a s ^ 2 + u * b s ^ 2)

theorem mixture_lower (a b u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 - u) * |a| ≤ Real.sqrt ((1 - u) * a ^ 2 + u * b ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, sq_abs]
  have h₁ := mul_nonneg (mul_nonneg hu (sub_nonneg.mpr hu1)) (sq_nonneg a)
  have h₂ := mul_nonneg hu (sq_nonneg b)
  nlinarith

theorem zero_coordinate_grows (a b : Fin N → ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hs : (∑ s, |a s|) = S) (j : Fin N) (ha : a j = 0) (hb : b j ≠ 0) :
    ∃ u : ℝ, 0 < u ∧ u < 1 ∧ S < ∑ s, mixtureNorm a b u s := by
  classical
  let B := |b j|
  have hB : 0 < B := abs_pos.mpr hb
  let k := B / (S + B + 1)
  have hden : 0 < S + B + 1 := by positivity
  have hk : 0 < k := div_pos hB hden
  have hk1 : k < 1 := (div_lt_one hden).mpr (by linarith)
  have he : k * (S + B + 1) = B := div_mul_cancel₀ _ hden.ne'
  have hks : k * S < B := by nlinarith [mul_pos hk (by linarith : 0 < B + 1)]
  refine ⟨k ^ 2, sq_pos_of_pos hk, by nlinarith, ?_⟩
  have hpoint (s : Fin N) : (1 - k ^ 2) * |a s| + (if s = j then k * B else 0) ≤
      mixtureNorm a b (k ^ 2) s := by
    by_cases hsj : s = j
    · subst s
      simp only [ha, abs_zero, mul_zero, ite_true, zero_add, mixtureNorm, zero_pow (by norm_num : 2 ≠ 0)]
      rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk.le, Real.sqrt_sq_eq_abs]
    · simp only [hsj, ite_false, add_zero, mixtureNorm]
      exact mixture_lower _ _ _ (sq_nonneg k) (by nlinarith)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun s _ ↦ hpoint s)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
  have hstrict : S < (1 - k ^ 2) * S + k * B := by
    nlinarith [mul_pos hk (sub_pos.mpr hks)]
  exact hstrict.trans_le hsum

theorem mixture_derivative (a b : Fin N → ℝ) (ha : ∀ s, a s ≠ 0) :
    HasDerivAt (fun u ↦ ∑ s, mixtureNorm a b u s)
      (∑ s, (b s ^ 2 - a s ^ 2) / (2 * |a s|)) 0 := by
  apply HasDerivAt.fun_sum
  intro s _
  have h₁ := ((hasDerivAt_const (0 : ℝ) 1).sub (hasDerivAt_id 0)).mul_const (a s ^ 2)
  have h₂ := (hasDerivAt_id (0 : ℝ)).mul_const (b s ^ 2)
  have hd := h₁.add h₂
  change HasDerivAt (fun u : ℝ ↦ (1 - u) * a s ^ 2 + u * b s ^ 2)
    ((0 - 1) * a s ^ 2 + 1 * b s ^ 2) 0 at hd
  simp only [zero_sub, one_mul, neg_one_mul] at hd
  have hh := hd.sqrt (by simpa using pow_ne_zero 2 (ha s))
  simpa [mixtureNorm, Real.sqrt_sq_eq_abs, sub_eq_add_neg, add_comm] using hh

theorem mixture_peak_inequality (a b : Fin N → ℝ) (ha : ∀ s, a s ≠ 0)
    (hbound : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → (∑ s, mixtureNorm a b u s) ≤ ∑ s, |a s|) :
    (∑ s, b s ^ 2 / |a s|) ≤ ∑ s, |a s| := by
  have hd := (mixture_derivative a b ha).tendsto_slope_zero_right
  have hder : (∑ s, (b s ^ 2 - a s ^ 2) / (2 * |a s|)) ≤ 0 := by
    apply le_of_tendsto hd
    have ht : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), u < 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, ht] with u hu hu1
    have hu : 0 < u := hu
    have hf0 : (∑ s, mixtureNorm a b 0 s) = ∑ s, |a s| := by
      simp only [mixtureNorm, sub_zero, one_mul, zero_mul, add_zero, Real.sqrt_sq_eq_abs]
    simp only [zero_add, smul_eq_mul, hf0]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hu).le (sub_nonpos.mpr (hbound u hu.le hu1.le))
  have he (s : Fin N) : (b s ^ 2 - a s ^ 2) / (2 * |a s|) =
      (b s ^ 2 / |a s| - |a s|) / 2 := by
    have hn : |a s| ≠ 0 := abs_ne_zero.mpr (ha s)
    have hs := sq_abs (a s)
    field_simp
    nlinarith
  simp_rw [he] at hder
  rw [← Finset.sum_div, Finset.sum_sub_distrib] at hder
  linarith

theorem sqrt_tangent (x a : ℝ) (hx : 0 ≤ x) (ha : 0 < a) :
    Real.sqrt x ≤ (x / a + a) / 2 := by
  have hh : a * (x / a) = x := mul_div_cancel₀ _ ha.ne'
  have hs := Real.sq_sqrt hx
  have hsq := sq_nonneg (Real.sqrt x - a)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply (mul_le_mul_iff_right₀ ha).mp
  nlinarith

def SupportBound (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) : Prop :=
  ∀ alpha : FiniteSpectrum I, (∑ s, alpha.polynomialNorm (h.response s)) ≤ InexactRealizations.Lower.additiveScale I N

def Criterion (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) : Prop :=
  (∀ s, (h.response s).eval I.mu < 0) ∧
    ∀ x ∈ Set.Icc I.mu I.L, (∑ s, (h.response s).eval x ^ 2 / |(h.response s).eval I.mu|) ≤
      InexactRealizations.Lower.additiveScale I N

def twoPoint (I : InexactRealizations.Operators.SpectralInterval) (x : ℝ) (hx : x ∈ Set.Icc I.mu I.L)
    (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) : FiniteSpectrum I where
  size := 2
  point := ![I.mu, x]
  point_mem i := by
    fin_cases i
    · exact ⟨le_rfl, I.mu_lt_L.le⟩
    · exact hx
  weight := ![1 - u, u]
  nonneg i := by fin_cases i <;> simp <;> linarith
  total := by simp [Fin.sum_univ_two]

theorem twoPoint_norm (I : InexactRealizations.Operators.SpectralInterval) (x : ℝ) (hx : x ∈ Set.Icc I.mu I.L)
    (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) (p : ℝ[X]) :
    (twoPoint I x hx u hu hu1).polynomialNorm p = Real.sqrt ((1 - u) * p.eval I.mu ^ 2 + u * p.eval x ^ 2) := by
  simp [FiniteSpectrum.polynomialNorm, FiniteSpectrum.moment, twoPoint, Fin.sum_univ_two]

theorem pointMass_norm (I : InexactRealizations.Operators.SpectralInterval) (p : ℝ[X]) :
    (FiniteSpectrum.pointMass I).polynomialNorm p = |p.eval I.mu| := by
  simp [FiniteSpectrum.polynomialNorm, FiniteSpectrum.moment, FiniteSpectrum.pointMass, Real.sqrt_sq_eq_abs]

theorem response_nonzero_on_interval (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (s : Fin N) :
    ∃ x ∈ Set.Icc I.mu I.L, (h.response s).eval x ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz : h.response s = 0 := (h.response s).eq_zero_of_infinite_isRoot
    ((Set.Icc_infinite I.mu_lt_L).mono (fun x hx ↦ by exact hn x hx))
  have hd := h.response_degree_eq hN (h.exact_terminal_natDegree I he) s
  rw [hz, degree_zero] at hd
  exact WithBot.coe_ne_bot hd.symm

theorem support_endpoint (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hbound : SupportBound h I) :
    (∀ s, (h.response s).eval I.mu ≤ 0) ∧
      (∑ s, |(h.response s).eval I.mu|) = InexactRealizations.Lower.additiveScale I N := by
  have hb := hbound (FiniteSpectrum.pointMass I)
  simp_rw [pointMass_norm] at hb
  have hs := InexactRealizations.Lower.response_sum_mu h I he
  have ht := Finset.abs_sum_le_sum_abs (fun s : Fin N ↦ (h.response s).eval I.mu) Finset.univ
  rw [hs, abs_neg, abs_of_nonneg (InexactRealizations.Risk.additiveScale_nonneg I N)] at ht
  have heq := le_antisymm hb ht
  refine ⟨?_, heq⟩
  intro s
  have hz : (∑ s : Fin N, (|(h.response s).eval I.mu| + (h.response s).eval I.mu)) = 0 := by
    rw [Finset.sum_add_distrib, heq, hs]; ring
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) ↦
    by linarith [neg_le_abs ((h.response j).eval I.mu)])).mp hz s (Finset.mem_univ _)
  linarith [abs_nonneg ((h.response s).eval I.mu)]

theorem support_implies_criterion (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (hbound : SupportBound h I) : Criterion h I := by
  have hend := support_endpoint h I he hbound
  have hmix (x : ℝ) (hx : x ∈ Set.Icc I.mu I.L) (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
      (∑ s, mixtureNorm (fun s ↦ (h.response s).eval I.mu) (fun s ↦ (h.response s).eval x) u s) ≤
        InexactRealizations.Lower.additiveScale I N := by
    have hh := hbound (twoPoint I x hx u hu hu1)
    simpa only [twoPoint_norm, mixtureNorm] using hh
  have hnegative (s : Fin N) : (h.response s).eval I.mu < 0 := by
    apply lt_of_le_of_ne (hend.1 s)
    intro hz
    have hz : (h.response s).eval I.mu = 0 := hz
    obtain ⟨x, hx, hxs⟩ := response_nonzero_on_interval h I he hN s
    obtain ⟨u, hu, hu1, hstrict⟩ := zero_coordinate_grows
      (fun j : Fin N ↦ (h.response j).eval I.mu) (fun j ↦ (h.response j).eval x)
      (InexactRealizations.Lower.additiveScale I N) (InexactRealizations.Risk.additiveScale_nonneg I N) hend.2 s hz hxs
    exact (hstrict.trans_le (hmix x hx u hu.le hu1.le)).false
  refine ⟨hnegative, ?_⟩
  intro x hx
  have hh := mixture_peak_inequality
    (fun s : Fin N ↦ (h.response s).eval I.mu) (fun s ↦ (h.response s).eval x)
    (fun s ↦ (hnegative s).ne) (fun u hu hu1 ↦ (hmix x hx u hu hu1).trans_eq hend.2.symm)
  exact hh.trans_eq hend.2

theorem criterion_implies_support (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hcrit : Criterion h I) : SupportBound h I := by
  intro alpha
  have hsum : (∑ s, |(h.response s).eval I.mu|) = InexactRealizations.Lower.additiveScale I N := by
    simp_rw [abs_of_neg (hcrit.1 _)]
    rw [Finset.sum_neg_distrib, InexactRealizations.Lower.response_sum_mu h I he, neg_neg]
  have hm : (∑ s, alpha.moment (h.response s) / |(h.response s).eval I.mu|) ≤
      InexactRealizations.Lower.additiveScale I N := by
    have heq : (∑ s, alpha.moment (h.response s) / |(h.response s).eval I.mu|) =
        ∑ i, alpha.weight i * (∑ s, (h.response s).eval (alpha.point i) ^ 2 / |(h.response s).eval I.mu|) := by
      simp only [FiniteSpectrum.moment, Finset.sum_div, Finset.mul_sum, mul_div_assoc]
      rw [Finset.sum_comm]
    rw [heq]
    calc
      _ ≤ ∑ i, alpha.weight i * InexactRealizations.Lower.additiveScale I N :=
        Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hcrit.2 _ (alpha.point_mem i)) (alpha.nonneg i))
      _ = _ := by rw [← Finset.sum_mul, alpha.total, one_mul]
  calc
    _ ≤ ∑ s, (alpha.moment (h.response s) / |(h.response s).eval I.mu| + |(h.response s).eval I.mu|) / 2 :=
      Finset.sum_le_sum (fun s _ ↦ sqrt_tangent _ _ (alpha.moment_nonneg _)
        (abs_pos.mpr (hcrit.1 s).ne))
    _ = ((∑ s, alpha.moment (h.response s) / |(h.response s).eval I.mu|) +
        ∑ s, |(h.response s).eval I.mu|) / 2 := by rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ _ := by rw [hsum]; linarith

def PerCallOptimal (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) : Prop :=
  ∀ r t : ℝ, 0 ≤ r → 0 ≤ t → additiveRisk ∞ h I r t =
    I.epsilon N * r + t * InexactRealizations.Lower.additiveScale I N

theorem perCallOptimal_implies_support (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (hopt : PerCallOptimal h I) : SupportBound h I := by
  intro alpha
  have hh := additiveSpectralValue_le_risk (p := ∞) (q := 1) h I he hN 0 1 le_rfl zero_le_one alpha
  rw [hopt 0 1 le_rfl zero_le_one] at hh
  simpa only [additiveSpectralValue, zero_mul, mul_zero, zero_add, add_zero, one_mul,
    callNorm_one, abs_of_nonneg (alpha.polynomialNorm_nonneg _)] using hh

theorem support_implies_perCallOptimal (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (hbound : SupportBound h I) : PerCallOptimal h I := by
  intro r t hr ht
  have hlo := additive_corner_chain (p := ∞) (q := 1) h I he hN hr ht
  have hlow : I.epsilon N * r + t * InexactRealizations.Lower.additiveScale I N ≤ additiveRisk ∞ h I r t := by
    have hh := hlo.1.trans hlo.2
    simpa only [ENNReal.div_top, ENNReal.toReal_zero, neg_zero, Real.rpow_zero, mul_one] using hh
  apply le_antisymm ?_ hlow
  rw [additive_spectral_duality (p := ∞) (q := 1) h I he hN r t hr ht]
  apply csSup_le (s := additiveSpectralValues 1 h I r t)
    ⟨additiveSpectralValue 1 h r t (FiniteSpectrum.pointMass I), ⟨FiniteSpectrum.pointMass I, rfl⟩⟩
  rintro v ⟨alpha, rfl⟩
  have hterm : alpha.polynomialNorm h.terminal ≤ I.epsilon N := by
    rw [alpha.polynomialNorm_eq_action, he]
    have hh := InexactRealizations.Analysis.residual_action_bound I (FiniteSpectrum.diagonal alpha.point)
      (FiniteSpectrum.diagonal_admissible alpha.point alpha.point_mem) N alpha.vector
    simpa only [alpha.vector_norm, mul_one] using hh
  simp only [additiveSpectralValue, callNorm_one, abs_of_nonneg (alpha.polynomialNorm_nonneg _)]
  nlinarith [mul_le_mul_of_nonneg_left hterm hr, mul_le_mul_of_nonneg_left (hbound alpha) ht]

theorem perCallOptimal_iff_criterion (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) : PerCallOptimal h I ↔ Criterion h I := by
  constructor
  · intro hopt
    exact support_implies_criterion h I he hN (perCallOptimal_implies_support h I he hN hopt)
  · intro hcrit
    exact support_implies_perCallOptimal h I he hN (criterion_implies_support h I he hcrit)

def ResponsePeaks (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) : Prop :=
  ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.response s).eval x| ≤ -(h.response s).eval I.mu

def QueryPeaks (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) : Prop :=
  ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ (h.query s).eval I.mu

theorem responsePeaks_criterion (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (hpeak : ResponsePeaks h I) : Criterion h I := by
  have hneg (s : Fin N) : (h.response s).eval I.mu < 0 := by
    have hh := hpeak s I.mu ⟨le_rfl, I.mu_lt_L.le⟩
    have hn : (h.response s).eval I.mu ≤ 0 := by linarith [abs_nonneg ((h.response s).eval I.mu)]
    apply lt_of_le_of_ne hn
    intro hz
    obtain ⟨x, hx, hxs⟩ := response_nonzero_on_interval h I he hN s
    have hb := hpeak s x hx
    rw [hz, neg_zero] at hb
    exact hxs (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))
  refine ⟨hneg, ?_⟩
  intro x hx
  have hsum : (∑ s, |(h.response s).eval I.mu|) = InexactRealizations.Lower.additiveScale I N := by
    simp_rw [abs_of_neg (hneg _)]
    rw [Finset.sum_neg_distrib, InexactRealizations.Lower.response_sum_mu h I he, neg_neg]
  rw [← hsum]
  apply Finset.sum_le_sum
  intro s _
  have hp := abs_pos.mpr (hneg s).ne
  have hh := hpeak s x hx
  rw [← abs_of_neg (hneg s)] at hh
  have hs := (sq_le_sq₀ (abs_nonneg ((h.response s).eval x)) hp.le).mpr hh
  rw [sq_abs] at hs
  exact (div_le_iff₀ hp).mpr (by simpa only [pow_two] using hs)

theorem responsePeaks_optimal (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (hpeak : ResponsePeaks h I) : PerCallOptimal h I :=
  (perCallOptimal_iff_criterion h I he hN).mpr (responsePeaks_criterion h I he hN hpeak)

theorem commonPeaks_relative (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) (hpeak : ResponsePeaks h I) (hqpeak : QueryPeaks h I)
    (r : ℝ) (hr : 0 < r) : localRelativeGain ∞ h I r = InexactRealizations.Lower.derivativeScale I N := by
  have hneg := (responsePeaks_criterion h I he hN hpeak).1
  have hQ (s : Fin N) : 0 ≤ (h.query s).eval I.mu :=
    (abs_nonneg _).trans (hqpeak s I.mu ⟨le_rfl, I.mu_lt_L.le⟩)
  rw [localRelativeGain_eq_operatorGain ∞ le_top h I r hr]
  rw [operatorGain_of_common_peaks (p := ∞) (q := 1) h I hN false
    (fun s ↦ -(h.response s).eval I.mu) (fun s ↦ (h.query s).eval I.mu)
    ⟨fun s ↦ (neg_pos.mpr (hneg s)).le, hpeak⟩ hQ hqpeak
    I.mu I.mu ⟨le_rfl, I.mu_lt_L.le⟩ ⟨le_rfl, I.mu_lt_L.le⟩
    (fun s ↦ abs_of_neg (hneg s)) (fun s ↦ abs_of_nonneg (hQ s))]
  rw [callNorm_one]
  calc
    _ = ∑ s : Fin N, -((h.response s).eval I.mu * (h.query s).eval I.mu) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [abs_of_nonneg (mul_nonneg (neg_pos.mpr (hneg s)).le (hQ s))]
      ring
    _ = -(∑ s : Fin N, (h.response s).eval I.mu * (h.query s).eval I.mu) :=
      Finset.sum_neg_distrib (fun s : Fin N ↦ (h.response s).eval I.mu * (h.query s).eval I.mu)
    _ = _ := by
      change -(∑ s : Fin N, InexactRealizations.Lower.physicalKernel h s I.mu I.mu) = _
      rw [InexactRealizations.Lower.kernel_sum_mu h I he, neg_neg]

end
end InexactRealizations.Budgets.PeakCriterion
