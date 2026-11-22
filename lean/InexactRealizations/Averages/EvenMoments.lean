import InexactRealizations.Averages.ArcsineChristoffel

/-! Integrals of U_(2n), sufficient for both printed squared-U moments. -/
namespace InexactRealizations.Averages
noncomputable section
open Polynomial Polynomial.Chebyshev MeasureTheory Real

theorem even_second_arcsine (n : ℕ) : (∫ x, (U ℝ (2 * (n : ℤ))).eval x ∂measureT) = π := by
  induction n with
  | zero => simpa only [Nat.cast_zero, mul_zero, U_zero, T_zero, eval_one] using integral_eval_T_real_measureT_zero
  | succ n ih =>
    have he : U ℝ (2 * ((n + 1 : ℕ) : ℤ)) = 2 * T ℝ (2 * ((n + 1 : ℕ) : ℤ)) + U ℝ (2 * (n : ℤ)) := by
      simpa only [Nat.cast_add, Nat.cast_one, mul_add, mul_one] using U_eq_two_mul_T_add_U ℝ (2 * (n : ℤ))
    simp_rw [he, eval_add, eval_mul, eval_ofNat]
    rw [integral_add (integrable_measureT (by fun_prop)) (integrable_measureT (by fun_prop)),
      integral_const_mul, integral_eval_T_real_measureT_of_ne_zero (by omega), mul_zero, zero_add, ih]

theorem even_second_uniform (n : ℕ) :
    (∫ u in (0 : ℝ)..1, (U ℝ (2 * (n : ℤ))).eval (1 - 2 * u)) = 1 / (2 * (n : ℝ) + 1) := by
  let P : ℝ[X] := (T ℝ (2 * (n : ℤ) + 1)).comp (1 - Polynomial.C 2 * X)
  have hd : P.derivative = Polynomial.C (-2 * (2 * (n : ℝ) + 1)) *
      (U ℝ (2 * (n : ℤ))).comp (1 - Polynomial.C 2 * X) := by
    have hcast : (((2 * (n : ℤ) + 1 : ℤ) : ℝ[X])) = Polynomial.C (2 * (n : ℝ) + 1) := by
      rw [← Polynomial.C_eq_intCast]
      congr 1
      push_cast
      rfl
    simp only [P, derivative_comp, T_derivative_eq_U, add_sub_cancel_right, hcast,
      derivative_sub, derivative_one, derivative_mul, derivative_C, zero_mul, zero_add, derivative_X,
      mul_one, zero_sub, mul_comp, C_comp]
    rw [← Polynomial.C_neg]
    rw [← mul_assoc, ← Polynomial.C_mul]

  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ P.hasDerivAt u) (P.derivative.continuous.intervalIntegrable (μ := volume) 0 1)
  have h0 : P.eval 0 = 1 := by simp [P]
  have h1 : P.eval 1 = -1 := by
    simp only [P, eval_comp, eval_sub, eval_one, eval_mul, eval_C, eval_X]
    norm_num only [mul_one, show (1 : ℝ) - 2 = -1 by norm_num]
    rw [T_eval_neg_one, Int.negOnePow_odd _ (odd_two_mul_add_one (n : ℤ))]
    norm_num
  rw [h0, h1] at hi
  simp_rw [hd, eval_mul, eval_C, eval_comp, eval_sub, eval_one, eval_mul, eval_C, eval_X] at hi
  rw [intervalIntegral.integral_const_mul] at hi
  have hc : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  apply (eq_div_iff hc).mpr
  nlinarith

theorem uniform_z (I : InexactRealizations.Operators.SpectralInterval) (u : ℝ) :
    I.z (I.mu + I.delta * u) = 1 - 2 * u := by
  unfold InexactRealizations.Operators.SpectralInterval.z
  field_simp [I.delta_pos.ne']
  dsimp only [InexactRealizations.Operators.SpectralInterval.delta]
  ring

theorem even_second_uniform_physical (I : InexactRealizations.Operators.SpectralInterval) (n : ℕ) :
    (∫ x, (U ℝ (2 * (n : ℤ))).eval (I.z x) ∂(uniform I).measure) = 1 / (2 * (n : ℝ) + 1) := by
  rw [integral_uniform I (by unfold InexactRealizations.Operators.SpectralInterval.z; fun_prop)]
  simp_rw [uniform_z]
  exact even_second_uniform n

theorem even_second_arcsine_physical (I : InexactRealizations.Operators.SpectralInterval) (n : ℕ) :
    (∫ x, (U ℝ (2 * (n : ℤ))).eval (I.z x) ∂(arcsine I).measure) = 1 := by
  rw [integral_arcsine I (by unfold InexactRealizations.Operators.SpectralInterval.z; fun_prop)]
  simp_rw [arcsine_coordinate]
  rw [even_second_arcsine, inv_mul_cancel₀ pi_ne_zero]

end
end InexactRealizations.Averages
