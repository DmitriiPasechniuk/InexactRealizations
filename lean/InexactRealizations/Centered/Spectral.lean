import InexactRealizations.Budgets.Support
import InexactRealizations.Analysis.Spectral
import InexactRealizations.Risk.Bounds

/-! Actual scalar response peaks and the exact spectral coefficient in
Proposition5.2. All maxima are over the complete closed spectral interval. 
-/
namespace InexactRealizations.Centered
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ}

def polynomialPeak (I : InexactRealizations.Operators.SpectralInterval) (p : ℝ[X]) : ℝ :=
  sSup ((fun x : ℝ ↦ |p.eval x|) '' Set.Icc I.mu I.L)

theorem polynomialPeak_attained (I : InexactRealizations.Operators.SpectralInterval) (p : ℝ[X]) :
    ∃ x ∈ Set.Icc I.mu I.L, polynomialPeak I p = |p.eval x| := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (show (Set.Icc I.mu I.L).Nonempty from
    ⟨I.mu, le_rfl, I.mu_lt_L.le⟩) p.continuous.abs.continuousOn
  refine ⟨x, hx, le_antisymm ?_ ?_⟩
  · apply csSup_le (s := (fun x : ℝ ↦ |p.eval x|) '' Set.Icc I.mu I.L)
      ⟨|p.eval I.mu|, I.mu, ⟨le_rfl, I.mu_lt_L.le⟩, rfl⟩
    rintro v ⟨y, hy, rfl⟩
    exact hmax hy
  · exact le_csSup (isCompact_Icc.image p.continuous.abs).bddAbove ⟨x, hx, rfl⟩

theorem polynomialPeak_bound (I : InexactRealizations.Operators.SpectralInterval) (p : ℝ[X])
    (x : ℝ) (hx : x ∈ Set.Icc I.mu I.L) : |p.eval x| ≤ polynomialPeak I p :=
  le_csSup (isCompact_Icc.image p.continuous.abs).bddAbove ⟨x, hx, rfl⟩

theorem polynomialPeak_nonneg (I : InexactRealizations.Operators.SpectralInterval) (p : ℝ[X]) : 0 ≤ polynomialPeak I p :=
  (abs_nonneg _).trans (polynomialPeak_bound I p I.mu ⟨le_rfl, I.mu_lt_L.le⟩)

def responsePeak (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (s : Fin N) : ℝ :=
  polynomialPeak I (h.response s)

theorem responsePeak_bounds (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) :
    InexactRealizations.Risk.ResponseBounds h I (responsePeak h I) :=
  ⟨fun s ↦ polynomialPeak_nonneg I (h.response s), fun s x hx ↦ polynomialPeak_bound I (h.response s) x hx⟩

theorem responsePeak_attained (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (s : Fin N) :
    ∃ x ∈ Set.Icc I.mu I.L, responsePeak h I s = |(h.response s).eval x| :=
  polynomialPeak_attained I (h.response s)

def variancePolynomial (h : InexactRealizations.History N) (P : Fin N → ℝ) : ℝ[X] :=
  ∑ s, C (P s ^ 2) * (h.query s) ^ 2

theorem variancePolynomial_eval (h : InexactRealizations.History N) (P : Fin N → ℝ) (x : ℝ) :
    (variancePolynomial h P).eval x = ∑ s, P s ^ 2 * (h.query s).eval x ^ 2 := by
  simp only [variancePolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow]

theorem variancePolynomial_nonneg (h : InexactRealizations.History N) (P : Fin N → ℝ) (x : ℝ) :
    0 ≤ (variancePolynomial h P).eval x := by
  rw [variancePolynomial_eval]
  exact Finset.sum_nonneg (fun s _ ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))

def centeredCoefficient (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) : ℝ :=
  polynomialPeak I (variancePolynomial h (responsePeak h I))

theorem centeredCoefficient_nonneg (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) :
    0 ≤ centeredCoefficient h I := polynomialPeak_nonneg _ _

theorem centeredCoefficient_attained (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) :
    ∃ x ∈ Set.Icc I.mu I.L, centeredCoefficient h I =
      ∑ s, responsePeak h I s ^ 2 * (h.query s).eval x ^ 2 := by
  obtain ⟨x, hx, he⟩ := polynomialPeak_attained I (variancePolynomial h (responsePeak h I))
  refine ⟨x, hx, ?_⟩
  rw [abs_of_nonneg (variancePolynomial_nonneg _ _ x), variancePolynomial_eval] at he
  exact he

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem weighted_query_energy (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (P : Fin N → ℝ) (v : E) :
    (∑ s, P s ^ 2 * ‖(aeval H (h.query s)) v‖ ^ 2) = inner ℝ v ((aeval H (variancePolynomial h P)) v) := by
  have he (s : Fin N) : inner ℝ v ((aeval H (C (P s ^ 2) * (h.query s) ^ 2)) v) =
      P s ^ 2 * ‖(aeval H (h.query s)) v‖ ^ 2 := by
    rw [map_mul (aeval H) (C (P s ^ 2)) ((h.query s) ^ 2),
      map_pow (aeval H) (h.query s) 2, aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply,
      inner_smul_right, pow_two (aeval H (h.query s)), Module.End.mul_apply]
    rw [← InexactRealizations.Budgets.polynomial_symmetric H hH (h.query s) v, real_inner_self_eq_norm_sq]
  rw [variancePolynomial, map_sum, LinearMap.sum_apply, inner_sum]
  simp_rw [he]

theorem weighted_query_energy_le (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (v : E) :
    (∑ s, responsePeak h I s ^ 2 * ‖(aeval H (h.query s)) v‖ ^ 2) ≤
      centeredCoefficient h I * ‖v‖ ^ 2 := by
  rw [weighted_query_energy h H hH.1]
  have hh := InexactRealizations.Analysis.polynomial_action_bound I H hH _ (centeredCoefficient h I)
    (centeredCoefficient_nonneg h I) (fun x hx ↦ polynomialPeak_bound I _ x hx) v
  exact (real_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left hh (norm_nonneg v)).trans_eq (by ring))

end
end InexactRealizations.Centered
