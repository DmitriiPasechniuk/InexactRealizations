import InexactRealizations.Averages.Measures
import InexactRealizations.Chains.SineContinuum.LegendrePolynomialBasis
import InexactRealizations.Chains.SineContinuum.LegendreNorm

/-! The exact uniform Christoffel value, proved using the existing actual
shifted Legendre orthogonality and norms and the finite kernel argument. 
-/
namespace InexactRealizations.Averages
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory InexactRealizations.Chains.SineContinuum
open scoped BigOperators

def affineSequence (S : Polynomial.Sequence ℝ) (a b : ℝ) (hb : b ≠ 0) : Polynomial.Sequence ℝ where
  elems' n := (S n).comp (C b * X + C a)
  degree_eq' n := by
    have hd : (C b * X + C a : ℝ[X]).degree = 1 := by
      rw [degree_add_C (by rw [degree_C_mul_X hb]; norm_num), degree_C_mul_X hb]
    rw [degree_comp (by rw [hd]; norm_num), hd, mul_one, S.degree_eq]

theorem affineSequence_eval (S : Polynomial.Sequence ℝ) (a b : ℝ) (hb : b ≠ 0) (n : ℕ) (x : ℝ) :
    (affineSequence S a b hb n).eval x = (S n).eval (b * x + a) := by
  simp only [affineSequence, eval_comp, eval_add, eval_mul, eval_C, eval_X]

def uniformSequence (I : InexactRealizations.Operators.SpectralInterval) : Polynomial.Sequence ℝ :=
  affineSequence legendreSequence (-I.mu / I.delta) I.delta⁻¹ (inv_ne_zero I.delta_pos.ne')

theorem uniformSequence_eval (I : InexactRealizations.Operators.SpectralInterval) (n : ℕ) (x : ℝ) :
    (uniformSequence I n).eval x = (shifted n).eval ((x - I.mu) / I.delta) := by
  rw [uniformSequence, affineSequence_eval]
  congr 1
  ring

theorem uniformSequence_mu (I : InexactRealizations.Operators.SpectralInterval) (n : ℕ) :
    (uniformSequence I n).eval I.mu = 1 := by
  rw [uniformSequence_eval, sub_self, zero_div, ← coeff_zero_eq_eval_zero, shifted_coeff]
  simp

theorem uniformSequence_orthogonal (I : InexactRealizations.Operators.SpectralInterval) (i j : ℕ) (hij : i ≠ j) :
    (uniform I).pairing (uniformSequence I i) (uniformSequence I j) = 0 := by
  change (∫ x, (uniformSequence I i * uniformSequence I j).eval x ∂(uniform I).measure) = 0
  rw [integral_uniform I (by fun_prop)]
  simp_rw [eval_mul, uniformSequence_eval, uniform_coordinate]
  exact legendre_orthogonal hij

theorem uniformSequence_energy (I : InexactRealizations.Operators.SpectralInterval) (j : ℕ) :
    (uniform I).energy (uniformSequence I j) = 1 / (2 * (j : ℝ) + 1) := by
  change (∫ x, (uniformSequence I j).eval x ^ 2 ∂(uniform I).measure) = _
  rw [integral_uniform I (by fun_prop)]
  simp_rw [uniformSequence_eval, uniform_coordinate]
  exact legendre_integral_sq j

theorem odd_sum (k : ℕ) : (∑ j ∈ Finset.range k, (2 * (j : ℝ) + 1)) = (k : ℝ) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem uniform_christoffel (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) :
    (uniform I).christoffel k = (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
  have hh := (uniform I).christoffel_of_orthogonal_sequence (uniformSequence I)
    (fun j ↦ 2 * (j : ℝ) + 1) (fun j ↦ by positivity) (uniformSequence_mu I)
    (uniformSequence_orthogonal I)
    (fun j ↦ by rw [uniformSequence_energy]; exact mul_one_div_cancel (by positivity)) k
  simpa only [odd_sum] using hh

end
end InexactRealizations.Averages
