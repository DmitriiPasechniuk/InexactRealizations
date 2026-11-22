import InexactRealizations.Flat.Iteration

namespace InexactRealizations.Algorithms.Flat
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The actual scalar U preparation, with its two printed startup values. -/
def preparedU (I : InexactRealizations.Operators.SpectralInterval) : ℕ → ℝ
  | 0 => 1
  | 1 => 2*I.eta
  | s+2 => 2*I.eta*preparedU I (s+1)-preparedU I s

/-- The recursive scalar preparation equals every exterior U value. -/
theorem preparedU_eq (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) :
    preparedU I s = InexactRealizations.Flat.u I s := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    match s with
    | 0 => simp [preparedU]
    | 1 => simp [preparedU]
    | s+2 => rw [preparedU, ih (s+1) (by omega), ih s (by omega), InexactRealizations.Flat.u_add_two]

/-- The article's scalar C is obtained from the final two prepared U values. -/
def preparedDen (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : ℝ :=
  I.eta * preparedU I (N-1) - preparedU I (N-2)

/-- The scalar preparation C is the prescribed terminal Chebyshev denominator. -/
theorem preparedDen_eq (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    preparedDen I N = I.den N := by
  have h := congrArg (fun p : ℝ[X] => p.eval I.eta)
    (T_eq_X_mul_U_sub_U ℝ ((N-2 : ℕ) : ℤ))
  simp only [eval_sub, eval_mul, eval_X] at h
  rw [show ((N-2 : ℕ):ℤ)+1=((N-1 : ℕ):ℤ) by omega,
    show ((N-2 : ℕ):ℤ)+2=(N:ℤ) by omega] at h
  simpa only [preparedDen, preparedU_eq, InexactRealizations.Flat.u, InexactRealizations.Operators.SpectralInterval.den] using h.symm

end
end InexactRealizations.Algorithms.Flat
