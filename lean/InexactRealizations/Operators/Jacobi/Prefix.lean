import InexactRealizations.Operators.Jacobi.Kernel

/-! The maximum property, including empty blocks.
Use: `InexactRealizations.Operators.Prefix.jacobiBlock_endpoint_max` feeds
`InexactRealizations.Operators.Prefix.jacobi_endpointMax` (jacobi endpoint Max).
Proof chain: `InexactRealizations.Operators.Prefix.opNorm_linearResponse_le` — chebyshev1,;
Attained finite-drift bounds for the prefix recurrence.
-/
namespace InexactRealizations.Operators.Prefix
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped Matrix

/-- The Jacobi data; site zero has no left coupling. -/
def jacobiData : JacobiData where
  b := fun _ => 0
  aSq := fun s => if s = 0 then 0 else if s = 1 then 1 / 2 else 1 / 4

/-- Exact identity `jacobiData.b s = 0`. -/
@[simp] theorem jacobiData_b (s : ℕ) : jacobiData.b s = 0 := rfl
/-- Exact identity `jacobiData.aSq 1 = 1 / 2`. -/
@[simp] theorem jacobiData_aSq_one : jacobiData.aSq 1 = 1 / 2 := rfl

/-- Exact identity `jacobiData.aSq s = 1 / 4`. -/
theorem jacobiData_aSq (s : ℕ) (hs : 2 ≤ s) : jacobiData.aSq s = 1 / 4 := by simp [jacobiData, show s ≠ 0 by omega, show s ≠ 1 by omega]

/-- Exact identity `jacobiData.leading (n + 1) = C ((1 / 2 : ℝ) ^ n) * T ℝ (n + 1)`. -/
theorem jacobi_leading (n : ℕ) :
    jacobiData.leading (n + 1) = C ((1 / 2 : ℝ) ^ n) * T ℝ (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [JacobiData.leading, JacobiData.block, jacobiData]
  | one =>
    apply Polynomial.funext
    intro x
    simp [JacobiData.leading, JacobiData.block, jacobiData, T_two]
    ring_nf
  | more n ih0 ih1 =>
    have hr : jacobiData.leading (n + 3) = X * jacobiData.leading (n + 2) -
        C (1 / 4) * jacobiData.leading (n + 1) := by
      simp [JacobiData.leading, JacobiData.block, jacobiData_aSq]
    rw [hr, ih1, ih0]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    rw [show (n : ℤ) + 2 + 1 = ((n : ℤ) + 1) + 2 by omega, T_add_two]
    apply Polynomial.funext
    intro x
    simp only [eval_sub, eval_mul, eval_C, eval_X, eval_ofNat, pow_succ]
    ring_nf

/-- Exact identity `jacobiData.den I (n + 1) = (1 / 2 : ℝ) ^ n * I.den (n + 1)`. -/
theorem jacobi_den (I : SpectralInterval) (n : ℕ) :
    jacobiData.den I (n + 1) = (1 / 2 : ℝ) ^ n * I.den (n + 1) := by simp [JacobiData.den, jacobi_leading, SpectralInterval.den]

/-- The precise assertion is `jacobiData.Admissible I N`. -/
theorem jacobi_admissible (I : SpectralInterval) (N : ℕ) : jacobiData.Admissible I N := by
  intro n _
  cases n with
  | zero => simp
  | succ n => rw [jacobi_den]; exact mul_pos (by positivity) (I.den_pos (n + 1))

/-- Exact identity `(jacobiData.method I).a (n + 1) = 2 * I.eta * I.den (n + 1) / I.den (n + 2)`. -/
theorem jacobi_a_succ (I : SpectralInterval) (n : ℕ) :
    (jacobiData.method I).a (n + 1) = 2 * I.eta * I.den (n + 1) / I.den (n + 2) := by
  simp only [JacobiData.method, jacobiData_b, sub_zero, jacobi_den]
  field_simp [I.den_ne (n + 2), pow_ne_zero n (by norm_num : (1 / 2 : ℝ) ≠ 0), pow_succ]
  ring

/-- Exact identity `(jacobiData.method I).b (n + 1) = -(I.den n / I.den (n + 2))`. -/
theorem jacobi_b_succ (I : SpectralInterval) (n : ℕ) :
    (jacobiData.method I).b (n + 1) = -(I.den n / I.den (n + 2)) := by
  simp only [JacobiData.method, Nat.add_sub_cancel]
  cases n with
  | zero =>
    simp only [Nat.zero_add, jacobiData_aSq_one, JacobiData.den_zero, I.den_zero]
    rw [show (2 : ℕ) = 1 + 1 by rfl, jacobi_den]
    field_simp [I.den_ne 2]
  | succ n =>
    rw [jacobiData_aSq (n + 1 + 1) (by omega)]
    simp only [jacobi_den]
    field_simp [I.den_ne (n + 1 + 2), pow_ne_zero n (by norm_num : (1 / 2 : ℝ) ≠ 0), pow_succ]
    ring

/-- Exact identity `(jacobiData.method I).gamma n = gamma I n`. -/
theorem jacobi_gamma (I : SpectralInterval) (n : ℕ) :
    (jacobiData.method I).gamma n = gamma I n := by
  cases n with
  | zero =>
    simp only [JacobiData.method, Nat.zero_add, JacobiData.den_zero, JacobiData.den_one, jacobiData_b,
      sub_zero, mul_one, gamma]
    dsimp [SpectralInterval.eta]
    field_simp [ne_of_gt I.delta_pos, ne_of_gt I.sum_pos]
  | succ n =>
    simp only [JacobiData.method, jacobi_den, gamma]
    field_simp [I.den_ne (n + 2), ne_of_gt I.delta_pos,
      pow_ne_zero n (by norm_num : (1 / 2 : ℝ) ≠ 0), pow_succ]
    ring

/-- 4 identifies the realization itself, hence also every drift term.

Exact identity `jacobiData.realization I = realization I`.
-/
theorem jacobi_realization (I : SpectralInterval) : jacobiData.realization I = realization I := by
  unfold JacobiData.realization TwoTerm.realization realization
  congr 1
  · funext n
    cases n with
    | zero => simp
    | succ n => simp [jacobi_a_succ, jacobi_b_succ]
  · funext n
    rw [jacobi_gamma]

end
end InexactRealizations.Operators.Prefix
