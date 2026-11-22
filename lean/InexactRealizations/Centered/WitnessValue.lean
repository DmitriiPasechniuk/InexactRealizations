import InexactRealizations.Centered.WitnessData
import InexactRealizations.Centered.Upper

/-! The centered relative-error witness attains the exact leading
coefficient at every noise scale, using admissible actual queries. 
-/
namespace InexactRealizations.Centered.Witness
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators
variable {N : ℕ}

theorem axis_polynomial (lambda : Fin N → ℝ) (nu : ℝ) (p : ℝ[X]) (i : Fin (N + 1)) :
    (aeval (hessian lambda nu) p) (axis i) = p.eval ((Fin.snoc lambda nu : Fin (N + 1) → ℝ) i) • axis i := by
  ext j
  rw [hessian, InexactRealizations.Budgets.FiniteSpectrum.diagonal_polynomial]
  by_cases hji : j = i
  · subst j
    simp [axis]
  · simp [axis, hji]

theorem response_norm_sq (h : InexactRealizations.History N) (lambda : Fin N → ℝ) (nu r t : ℝ)
    (s : Fin N) (ω : Fin N → Bool) :
    ‖h.responseOperator (hessian lambda nu) s (stream h nu r t s.val ω)‖ ^ 2 =
      (h.response s).eval (lambda s) ^ 2 * amplitude h nu r t s ^ 2 := by
  rw [InexactRealizations.History.responseOperator_apply, stream_at, map_smul, map_smul, axis_polynomial, Fin.snoc_castSucc]
  simp only [norm_smul, axis_norm, mul_one, mul_pow]
  rw [InexactRealizations.Probability.Signs.error_norm_sq (N := N) 1 s ω]
  simp only [Real.norm_eq_abs, sq_abs, one_pow, one_mul]
  ring

theorem exact_mse (h : InexactRealizations.History N) (lambda : Fin N → ℝ) (nu r t : ℝ) :
    (∫ ω, ‖deviation h (hessian lambda nu) (initial N r) (stream h nu r t) ω‖ ^ 2
      ∂InexactRealizations.Probability.Signs.law N) =
      t ^ 2 * r ^ 2 * ∑ s : Fin N, (h.response s).eval (lambda s) ^ 2 * (h.query s).eval nu ^ 2 := by
  rw [deviation_second h _ _ (martingale h nu r t)]
  simp_rw [response_norm_sq]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, amplitude, mul_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem attained_mse (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r t : ℝ) :
    ∃ (lambda : Fin N → ℝ) (nu : ℝ), (∀ s, lambda s ∈ Set.Icc I.mu I.L) ∧
      nu ∈ Set.Icc I.mu I.L ∧
      (∫ ω, ‖deviation h (hessian lambda nu) (initial N r) (stream h nu r t) ω‖ ^ 2
        ∂InexactRealizations.Probability.Signs.law N) = t ^ 2 * r ^ 2 * centeredCoefficient h I := by
  classical
  choose lambda hlam he using responsePeak_attained h I
  obtain ⟨nu, hnu, hmax⟩ := centeredCoefficient_attained h I
  refine ⟨lambda, nu, hlam, hnu, ?_⟩
  rw [exact_mse, hmax]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [he s, sq_abs]

end
end InexactRealizations.Centered.Witness
