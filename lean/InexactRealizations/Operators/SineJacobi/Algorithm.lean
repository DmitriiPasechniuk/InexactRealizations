import InexactRealizations.Operators.SineJacobi.Gain

/-! Terminal exactness for the independently defined iterates.
Result: `InexactRealizations.Operators.SineJacobi.quadraticError_exact` supplies the stated article conclusion.
-/
namespace InexactRealizations.Operators.SineJacobi
noncomputable section
open Polynomial
variable (I : SpectralInterval)

/--'s initial gradient step.

Exact identity `((data N).method I).a 0 = 1 ∧ ((data N).method I).b 0 = 0 ∧ ((data N).method
I).gamma 0 = 2/(I.L+I.mu)`.
-/
theorem method_initial (N : ℕ) :
    ((data N).method I).a 0 = 1 ∧ ((data N).method I).b 0 = 0 ∧
      ((data N).method I).gamma 0 = 2/(I.L+I.mu) := by
  have heta : I.eta ≠ 0 := ne_of_gt (lt_trans zero_lt_one I.eta_gt_one)
  simp only [JacobiData.method, JacobiData.den_zero, JacobiData.den_one, data_b,
    data_aSq_zero, Nat.zero_add, sub_zero, zero_mul, zero_div, neg_zero, mul_one]
  constructor
  · field_simp
  · constructor
    · trivial
    · unfold SpectralInterval.eta
      field_simp [ne_of_gt I.delta_pos]

/--'s explicit coefficients at each used later step. -/
theorem method_coefficients (N s : ℕ) (hs : 0 < s) (hsN : s < N) :
    ((data N).method I).a s = I.eta*(data N).den I s/(data N).den I (s+1) ∧
    ((data N).method I).b s = -couplingSq N s*(data N).den I (s-1)/(data N).den I (s+1) ∧
    ((data N).method I).gamma s = 2*(data N).den I s/(I.delta*(data N).den I (s+1)) := by
  simp only [JacobiData.method, data_b, sub_zero, data_aSq N s hs hsN]
  constructor
  · ring
  · constructor <;> ring

end
end InexactRealizations.Operators.SineJacobi
