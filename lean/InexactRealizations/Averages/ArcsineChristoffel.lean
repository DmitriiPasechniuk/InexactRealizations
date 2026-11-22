import InexactRealizations.Averages.UniformChristoffel

/-! The exact arcsine Christoffel value uses actual Chebyshev T
orthogonality for the literal arcsine density. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Polynomial Polynomial.Chebyshev MeasureTheory Real
open scoped BigOperators

def firstKindSequence : Polynomial.Sequence ℝ where
  elems' n := T ℝ (n : ℤ)
  degree_eq' n := by simp only [degree_T, Int.natAbs_natCast]

def arcsineSequence (I : InexactRealizations.Operators.SpectralInterval) : Polynomial.Sequence ℝ :=
  affineSequence firstKindSequence I.eta (-2 / I.delta)
    (div_ne_zero (by norm_num) I.delta_pos.ne')

theorem arcsineSequence_eval (I : InexactRealizations.Operators.SpectralInterval) (n : ℕ) (x : ℝ) :
    (arcsineSequence I n).eval x = (T ℝ (n : ℤ)).eval (I.z x) := by
  rw [arcsineSequence, affineSequence_eval]
  change (T ℝ (n : ℤ)).eval (-2 / I.delta * x + I.eta) = _
  rw [I.z_eq]
  congr 1
  ring

theorem arcsineSequence_mu (I : InexactRealizations.Operators.SpectralInterval) (n : ℕ) :
    (arcsineSequence I n).eval I.mu = 1 := by rw [arcsineSequence_eval, I.z_mu, T_eval_one]

theorem arcsineSequence_orthogonal (I : InexactRealizations.Operators.SpectralInterval) (i j : ℕ) (hij : i ≠ j) :
    (arcsine I).pairing (arcsineSequence I i) (arcsineSequence I j) = 0 := by
  change (∫ x, (arcsineSequence I i * arcsineSequence I j).eval x ∂(arcsine I).measure) = 0
  rw [integral_arcsine I (by fun_prop)]
  simp_rw [eval_mul, arcsineSequence_eval, arcsine_coordinate]
  rw [integral_eval_T_real_mul_eval_T_real_measureT_of_ne hij, mul_zero]

theorem arcsineSequence_energy (I : InexactRealizations.Operators.SpectralInterval) (j : ℕ) :
    (arcsine I).energy (arcsineSequence I j) = if j = 0 then 1 else 1 / 2 := by
  change (∫ x, (arcsineSequence I j).eval x ^ 2 ∂(arcsine I).measure) = _
  rw [integral_arcsine I (by fun_prop)]
  simp_rw [arcsineSequence_eval, arcsine_coordinate, pow_two]
  by_cases hj : j = 0
  · subst j
    simp only [Nat.cast_zero, ite_true]
    rw [integral_eval_T_real_mul_self_measureT_zero, inv_mul_cancel₀ pi_ne_zero]
  · simp only [hj, ite_false]
    rw [integral_T_real_mul_self_measureT_of_ne_zero hj]
    field_simp

def arcsineWeight (j : ℕ) : ℝ := if j = 0 then 1 else 2

theorem arcsineWeight_sum (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), arcsineWeight j) = 2 * (k : ℝ) + 1 := by
  induction k with
  | zero => simp [arcsineWeight]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [arcsineWeight, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, Nat.cast_add, Nat.cast_one]
    ring

theorem arcsine_christoffel (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) :
    (arcsine I).christoffel k = (2 * (k : ℝ) + 1)⁻¹ := by
  have hh := (arcsine I).christoffel_of_orthogonal_sequence (arcsineSequence I) arcsineWeight
    (fun j ↦ by unfold arcsineWeight; split_ifs <;> norm_num) (arcsineSequence_mu I)
    (arcsineSequence_orthogonal I)
    (fun j ↦ by rw [arcsineSequence_energy]; unfold arcsineWeight; split_ifs <;> norm_num) k
  simpa only [arcsineWeight_sum] using hh

end
end InexactRealizations.Averages
