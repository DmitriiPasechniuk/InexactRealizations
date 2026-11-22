import InexactRealizations.History.Basic

namespace InexactRealizations.History

open scoped BigOperators Polynomial Matrix
noncomputable section
variable {N : ℕ}

/-- The triangular polynomial matrix vanishes on and above its diagonal. Use: remove causal filters from row sums. -/
theorem coefficient_zero (h : InexactRealizations.History N) (s j : Fin N) (hsj : s ≤ j) :
    h.coefficient s j = 0 := by
  simp [coefficient, h.triangular s j hsj]

/-- The exact row equation of the polynomial causal inverse. Use: prove the inverse identity. -/
theorem resolvent_row (h : InexactRealizations.History N) (s j : Fin N) :
    h.resolvent s j = (if s = j then 1 else 0) -
      ∑ k : Fin N, h.coefficient s k * h.resolvent k j := by
  rw [resolvent, lowerSolve_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k < s
  · simp [hk, resolvent]
  · simp [hk, h.coefficient_zero s k (le_of_not_gt hk)]

/-- The polynomial pencil of the gradient equations. Use: polynomial and evaluated inverse identities. -/
def pencil (h : InexactRealizations.History N) : Matrix (Fin N) (Fin N) ℝ[X] :=
  1 + Matrix.of h.coefficient

/-- The recursively constructed causal inverse is a right inverse. Use: response and query row identities. -/
theorem pencil_mul_resolvent (h : InexactRealizations.History N) :
    h.pencil * Matrix.of h.resolvent = 1 := by
  unfold pencil
  rw [Matrix.add_mul, Matrix.one_mul]
  apply Matrix.ext
  intro s j
  change h.resolvent s j + ∑ k, h.coefficient s k * h.resolvent k j = _
  simpa only [Matrix.one_apply] using (eq_sub_iff_add_eq.mp (h.resolvent_row s j))

/-- The causal inverse is also a left inverse. Use: transfer and Bezoutian identities. -/
theorem resolvent_mul_pencil (h : InexactRealizations.History N) :
    Matrix.of h.resolvent * h.pencil = 1 :=
  mul_eq_one_comm.mp h.pencil_mul_resolvent

/-- Nominal query polynomials satisfy the actual physical query recurrence. Use: unique synthesis from a graded basis. -/
theorem query_recurrence (h : InexactRealizations.History N) (s : Fin N) :
    h.query s = 1 - Polynomial.X *
      ∑ j : Fin N, if j < s then Polynomial.C (h.a s j) * h.query j else 0 := by
  have hr : h.query s = ∑ j : Fin N, ((if s = j then 1 else 0) -
      ∑ k : Fin N, h.coefficient s k * h.resolvent k j) := by
    apply Finset.sum_congr rfl
    intro j _
    exact h.resolvent_row s j
  rw [hr, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < s
  · simp [hj, coefficient, query]
    ring
  · simp [hj, h.coefficient_zero s j (le_of_not_gt hj)]

/-- The query family is the causal solve with constant right-hand side one. Use: uniqueness of the synthesized query basis. -/
theorem query_eq_lowerSolve (h : InexactRealizations.History N) :
    h.query = lowerSolve (fun s j => h.coefficient s j) (fun _ => 1) := by
  apply lowerSolve_unique
  intro s
  rw [h.query_recurrence, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < s
  · simp [hj, coefficient]
    ring
  · simp [hj]

/-- The physical response row solves the adjoint gradient equations. Use: backward causality and sharp response degrees. -/
theorem response_pencil (h : InexactRealizations.History N) :
    (fun j => h.response j) ᵥ* h.pencil = fun j => -Polynomial.C (h.b j) := by
  change (-((fun j => Polynomial.C (h.b j)) ᵥ* Matrix.of h.resolvent)) ᵥ* h.pencil = _
  rw [Matrix.neg_vecMul, Matrix.vecMul_vecMul,
    h.resolvent_mul_pencil, Matrix.vecMul_one]
  rfl

/-- Backward causal recurrence for the physical oracle response. Use: maximal-path response degree and uniqueness. -/
theorem response_recurrence (h : InexactRealizations.History N) (j : Fin N) :
    h.response j = -Polynomial.C (h.b j) - Polynomial.X *
      ∑ s : Fin N, if j < s then Polynomial.C (h.a s j) * h.response s else 0 := by
  have hr := congrFun h.response_pencil j
  rw [pencil, Matrix.vecMul_add, Matrix.vecMul_one] at hr
  change h.response j + ∑ s, h.response s * h.coefficient s j = _ at hr
  have hs : (∑ s, h.response s * h.coefficient s j) = Polynomial.X *
      ∑ s : Fin N, if j < s then Polynomial.C (h.a s j) * h.response s else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hj : j < s
    · simp only [ite_eq_left hj, coefficient]
      ring
    · simp [hj, h.coefficient_zero s j (le_of_not_gt hj)]
  rw [hs] at hr
  exact eq_sub_of_add_eq hr

/-- Every nominal query equals the initial point at zero curvature. Use: normalized polynomial bases. -/
theorem query_eval_zero (h : InexactRealizations.History N) (s : Fin N) :
    (h.query s).eval 0 = 1 := by
  rw [h.query_recurrence]
  simp

/-- The sum of physical responses determines the terminal residual. Use: the exact additive-error response identity. -/
theorem terminal_eq_one_add_X_sum_response (h : InexactRealizations.History N) :
    h.terminal = 1 + Polynomial.X * ∑ j, h.response j := by
  have hs : (∑ j, h.response j) = - ∑ s, Polynomial.C (h.b s) * h.query s := by
    simp only [response, Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_comm]
    simp only [query, Finset.mul_sum]
  rw [hs]
  simp [terminal, mul_neg, sub_eq_add_neg]

/-- The terminal has constant term one. Use: the prescribed residual comparison class. -/
theorem terminal_eval_zero (h : InexactRealizations.History N) : h.terminal.eval 0 = 1 := by
  simp [terminal]

end
end InexactRealizations.History
