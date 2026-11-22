import InexactRealizations.Flat.Response
import InexactRealizations.Operators.Chebyshev.Normalization

/-! The exact Flat query maximum in Theorem5.1(d), attained at L. -/
namespace InexactRealizations.Budgets.FlatQuery
noncomputable section
open Polynomial Polynomial.Chebyshev InexactRealizations.Flat
variable {N : ℕ}

def peak (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ :=
  (1 + tau I N s) * (s + 1) / u I s + tau I N s * s / u I (s - 1)

theorem peak_nonneg (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (s : Fin N) :
    0 ≤ peak I N s := by
  have ht := tau_nonneg I N (by omega) s s.isLt
  have hu := u_pos I s
  have hup := u_pos I (s - 1)
  unfold peak
  positivity

theorem peak_zero (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) : peak I N 0 = 1 := by
  simp [peak, tau_zero I N (by omega)]

theorem chart_query_bound (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N)
    (s : Fin N) (x : ℝ) (hx : |x| ≤ 1) :
    |(queryPolynomial I N s).eval x| ≤ peak I N s := by
  have ht := tau_nonneg I N (by omega) s s.isLt
  by_cases hs : s.val = 0
  · simp only [hs, queryPolynomial, tau_zero I N (by omega), add_zero, C_1,
      normalizedU_zero, mul_one, C_0, zero_mul, sub_zero, eval_one, abs_one]
    rw [peak_zero I hN]
  have hsub : ((s.val - 1 : ℕ) : ℝ) + 1 = s.val := by
    rw [Nat.cast_sub (by omega : 1 ≤ s.val), Nat.cast_one]; ring
  have hU := InexactRealizations.Operators.abs_U_eval_le s.val hx
  have hUp := InexactRealizations.Operators.abs_U_eval_le (s.val - 1) hx
  rw [hsub] at hUp
  simp only [queryPolynomial, normalizedU, eval_sub, eval_mul, eval_C]
  have h1 : |(1 + tau I N s) * ((1 / u I s) * (U ℝ s.val).eval x)| ≤
      (1 + tau I N s) * (s.val + 1) / u I s := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 + tau I N s),
      abs_of_pos (one_div_pos.mpr (u_pos I s))]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU
      (one_div_pos.mpr (u_pos I s)).le) (by linarith)).trans_eq (by ring)
  have h2 : |tau I N s * ((1 / u I (s.val - 1)) * (U ℝ ((s.val - 1 : ℕ) : ℤ)).eval x)| ≤
      tau I N s * s.val / u I (s.val - 1) := by
    rw [abs_mul, abs_mul, abs_of_nonneg ht,
      abs_of_pos (one_div_pos.mpr (u_pos I (s.val - 1)))]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hUp
      (one_div_pos.mpr (u_pos I (s.val - 1))).le) ht).trans_eq (by ring)
  exact (abs_sub _ _).trans (add_le_add h1 h2)

theorem chart_query_neg_one (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (s : Fin N) :
    (queryPolynomial I N s).eval (-1) = (-1 : ℝ) ^ s.val * peak I N s := by
  by_cases hs : s.val = 0
  · simp [hs, queryPolynomial, tau_zero I N (by omega), peak_zero I hN]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs
  have hu (j : ℕ) : (U ℝ (j : ℤ)).eval (-1) = (-1 : ℝ) ^ j * (j + 1) := by
    simp only [U_eval_neg_one, Int.cast_negOnePow_natCast, Int.cast_natCast]
  simp only [queryPolynomial, normalizedU, eval_sub, eval_mul, eval_C, hk,
    Nat.succ_sub_one, hu, peak]
  simp only [Nat.cast_succ, pow_succ]
  ring

theorem history_query_eval (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N)
    (s : Fin N) (x : ℝ) : ((history I N hN).query s).eval x = (queryPolynomial I N s).eval (I.z x) := by
  rw [← InexactRealizations.History.chartQuery_physical_eval, history_chartQuery]

theorem query_bound (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N)
    (s : Fin N) (x : ℝ) (hx : x ∈ Set.Icc I.mu I.L) :
    |((history I N hN).query s).eval x| ≤ peak I N s := by
  rw [history_query_eval]
  exact chart_query_bound I hN s _ (abs_le.mpr (I.z_mem hx))

theorem query_at_L (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (s : Fin N) :
    |((history I N hN).query s).eval I.L| = peak I N s := by
  have hz : I.z I.L = -1 := by
    unfold InexactRealizations.Operators.SpectralInterval.z InexactRealizations.Operators.SpectralInterval.delta
    field_simp [sub_ne_zero.mpr I.mu_lt_L.ne']
    ring
  rw [history_query_eval, hz, chart_query_neg_one I hN s, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul, abs_of_nonneg (peak_nonneg I hN s)]

end
end InexactRealizations.Budgets.FlatQuery
