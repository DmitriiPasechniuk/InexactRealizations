import InexactRealizations.Budgets.JournalDuality
import InexactRealizations.Balanced.Gains

/-! Exact all-gamma gains whenever the physical response and query peaks
are simultaneously attained, and the even-horizon Balanced optimum. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial
open scoped BigOperators ENNReal NNReal
variable {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]

theorem operatorGain_of_common_peaks (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (hN : 0 < N) (symmetric : Bool) (P Q : Fin N → ℝ)
    (hP : InexactRealizations.Risk.ResponseBounds h I P) (hQ : ∀ s, 0 ≤ Q s)
    (hq : ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s)
    (x y : ℝ) (hx : x ∈ Set.Icc I.mu I.L) (hy : y ∈ Set.Icc I.mu I.L)
    (hp : ∀ s, |(h.response s).eval x| = P s) (hqp : ∀ s, |(h.query s).eval y| = Q s) :
    operatorGain p h I symmetric = callNorm q (fun s ↦ P s * Q s) := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  apply le_antisymm (operatorGain_upper h I symmetric P Q hP hQ hq)
  have hh := operator_kernel_lower (p := p) (q := q) h I symmetric x y hx hy
  rw [← callNorm_abs] at hh
  simp only [InexactRealizations.Lower.physicalKernel, abs_mul, hp, hqp] at hh
  exact hh

theorem balanced_gain_profile (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (symmetric : Bool) :
    operatorGain p (InexactRealizations.Balanced.history I N hN) I symmetric =
      callNorm q (fun s : Fin N ↦ InexactRealizations.Balanced.responseBound I N s * InexactRealizations.Balanced.queryBound I N s) := by
  apply operatorGain_of_common_peaks (p := p) (q := q)
    (h := InexactRealizations.Balanced.history I N hN) (I := I) (symmetric := symmetric)
    (hN := by omega)
    (hP := InexactRealizations.Balanced.responseBounds I N hN)
    (hQ := fun s ↦ (InexactRealizations.Balanced.queryBound_pos I hN s.isLt).le)
    (hq := fun s _ hx ↦ InexactRealizations.Balanced.query_bound_physical I N hN s hx)
    (x := I.mu) (y := I.mu) (hx := ⟨le_rfl, I.mu_lt_L.le⟩) (hy := ⟨le_rfl, I.mu_lt_L.le⟩)
  · intro s
    rw [InexactRealizations.Balanced.response_endpoint, abs_neg,
      abs_of_pos (InexactRealizations.Balanced.responseBound_pos I hN s.isLt)]
  · intro s
    rw [InexactRealizations.Balanced.query_endpoint_physical,
      abs_of_pos (InexactRealizations.Balanced.queryBound_pos I hN s.isLt)]

theorem balanced_even_all_gamma (p : ℝ≥0∞) (hp : 1 ≤ p) (I : InexactRealizations.Operators.SpectralInterval)
    (hN : 2 ≤ N) (heven : Even N) (r : ℝ) (hr : 0 < r) :
    localRelativeGain p (InexactRealizations.Balanced.history I N hN) I r =
      (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.derivativeScale I N := by
  let : p.HolderConjugate (dualExponent p) := holder_dualExponent p hp
  let : Fact (1 ≤ dualExponent p) := ⟨ENNReal.HolderConjugate.one_le (dualExponent p) p⟩
  let : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  rw [localRelativeGain_eq_operatorGain p hp _ I r hr,
    balanced_gain_profile (p := p) (q := dualExponent p) I hN false]
  have hD : 0 ≤ InexactRealizations.Lower.derivativeScale I N := by
    unfold InexactRealizations.Lower.derivativeScale
    have := I.delta_pos
    have := one_div_pos.mpr (I.den_pos N)
    positivity
  have heq : (fun s : Fin N ↦ InexactRealizations.Balanced.responseBound I N s *
      InexactRealizations.Balanced.queryBound I N s) =
      (fun _ : Fin N ↦ |(-InexactRealizations.Lower.derivativeScale I N) / (N : ℝ)|) := by
    funext s
    rw [InexactRealizations.Balanced.bound_product I hN s.isLt]
    simp only [InexactRealizations.Balanced.classMass, heven, ite_true]
    rw [neg_div, abs_neg, abs_of_nonneg (div_nonneg hD (Nat.cast_nonneg _))]
    unfold InexactRealizations.Lower.derivativeScale
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp
    ring
  rw [heq, callNorm_abs]
  simpa only [Fintype.card_fin] using
    (constant_signed_profile (ι := Fin N) (p := p) (q := dualExponent p) hD)

end
end InexactRealizations.Budgets
