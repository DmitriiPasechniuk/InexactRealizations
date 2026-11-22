import InexactRealizations.Operators.Realization.SpectralPair

/-! First variation commutes with orthogonal changes of physical coordinates.
Use: `InexactRealizations.Operators.Realization.linearResponse_coordinates` feeds
`InexactRealizations.Operators.Realization.static_linearResponse_general` (Static shift differentiates the residual
polynomial on every eigenspace).
Proof chain: `InexactRealizations.Operators.Realization.static_shift_lower_bounds_general` — chebyshev1, Theorem
4.3; All insertion orders, partition bounds, finite/cosh bounds and attainment.
-/
namespace InexactRealizations.Operators.Realization
noncomputable section
open scoped Matrix Kronecker BigOperators
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- Exact identity `(qi * a * q) * (qi * b * q) = qi * (a * b) * q`. -/
private theorem conjugation_mul {A : Type*} [Monoid A] (q qi : A) (hr : q * qi = 1) (a b : A) :
    (qi * a * q) * (qi * b * q) = qi * (a * b) * q := by
  simp only [mul_assoc]
  rw [← mul_assoc q qi (b * q), hr, one_mul]

/-- Exact identity `orderedProduct (fun s => qi * C s * q) n = qi * orderedProduct C n * q`. -/
private theorem product_conjugation {A : Type*} [Monoid A] (C : ℕ → A)
    (q qi : A) (hl : qi * q = 1) (hr : q * qi = 1) (n : ℕ) :
    orderedProduct (fun s => qi * C s * q) n = qi * orderedProduct C n * q := by
  induction n with
  | zero => simp [hl]
  | succ n ih => rw [orderedProduct_succ, ih, conjugation_mul q qi hr, orderedProduct_succ]

/-- Exact identity `R.operatorStep s (Qᵀ * H * Q) = ((1 : Matrix ι ι ℝ) ⊗ₖ Qᵀ) * R.operatorStep s H
* ((1 : Matrix ι ι ℝ) ⊗ₖ Q)`.
-/
theorem operatorStep_coordinates (R : Realization ι) (Q H : Matrix d d ℝ)
    (hQ : Qᵀ * Q = 1) (s : ℕ) :
    R.operatorStep s (Qᵀ * H * Q) =
      ((1 : Matrix ι ι ℝ) ⊗ₖ Qᵀ) * R.operatorStep s H * ((1 : Matrix ι ι ℝ) ⊗ₖ Q) := by
  rw [operatorStep, operatorStep, Matrix.mul_sub, Matrix.sub_mul]
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hQ]

omit [DecidableEq d] in
/-- Exact identity `R.operatorInsertion s (Qᵀ * E * Q) = ((1 : Matrix ι ι ℝ) ⊗ₖ Qᵀ) *
R.operatorInsertion s E * ((1 : Matrix ι ι ℝ) ⊗ₖ Q)`.
-/
theorem operatorInsertion_coordinates (R : Realization ι) (Q E : Matrix d d ℝ) (s : ℕ) :
    R.operatorInsertion s (Qᵀ * E * Q) =
      ((1 : Matrix ι ι ℝ) ⊗ₖ Qᵀ) * R.operatorInsertion s E * ((1 : Matrix ι ι ℝ) ⊗ₖ Q) := by
  rw [operatorInsertion, operatorInsertion, Matrix.mul_neg, Matrix.neg_mul]
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- First variation commutes with orthogonal changes of physical coordinates.

Exact identity `R.linearResponse N (Qᵀ * H * Q) (fun s => Qᵀ * E s * Q) = Qᵀ * R.linearResponse
N H E * Q`.
-/
theorem linearResponse_coordinates (R : Realization ι) (Q H : Matrix d d ℝ)
    (hl : Qᵀ * Q = 1) (hr : Q * Qᵀ = 1) (N : ℕ) (E : ℕ → Matrix d d ℝ) :
    R.linearResponse N (Qᵀ * H * Q) (fun s => Qᵀ * E s * Q) =
      Qᵀ * R.linearResponse N H E * Q := by
  let q := (1 : Matrix ι ι ℝ) ⊗ₖ Q
  let qi := (1 : Matrix ι ι ℝ) ⊗ₖ Qᵀ
  have hleft : qi * q = 1 := by
    dsimp [qi, q]
    rw [← Matrix.mul_kronecker_mul, hl, Matrix.mul_one, Matrix.one_kronecker_one]
  have hright : q * qi = 1 := by
    dsimp [qi, q]
    rw [← Matrix.mul_kronecker_mul, hr, Matrix.mul_one, Matrix.one_kronecker_one]
  have hp (a n : ℕ) : orderedProduct (fun s => R.operatorStep (a + s) (Qᵀ * H * Q)) n =
      qi * orderedProduct (fun s => R.operatorStep (a + s) H) n * q := by
    simp_rw [operatorStep_coordinates R Q H hl]
    exact product_conjugation _ q qi hleft hright n
  rw [linearResponse_eq_sum, linearResponse_eq_sum, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  have hzero := hp 0 s
  simp only [Nat.zero_add] at hzero
  rw [hp (s + 1) (N - (s + 1)), hzero, operatorInsertion_coordinates]
  change R.contract ((qi * _ * q) * (qi * _ * q) * (qi * _ * q)) = _
  rw [conjugation_mul q qi hright, conjugation_mul q qi hright]
  dsimp [qi, q]
  rw [contract_kronecker_right, contract_kronecker_left]

end
end InexactRealizations.Operators.Realization
