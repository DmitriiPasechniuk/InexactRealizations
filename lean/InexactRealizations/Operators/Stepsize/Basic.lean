import InexactRealizations.Operators.Realization.GainBounds
import InexactRealizations.Operators.Chebyshev.Polynomial

/-! A product of affine factors satisfies this exact diagonal-kernel identity.
Use: `InexactRealizations.Operators.Stepsize.kernel_square_sum_derivatives` feeds
`InexactRealizations.Operators.Stepsize.endpoint_square_sum` (The endpoint energy is independent of the ordering of
an exact schedule).
Proof chain: `InexactRealizations.Operators.Stepsize.endpoint_square_sum` — chebyshev1,; Sharp
stepsize drift lower bound and asymptotics.
-/
namespace InexactRealizations.Operators.Stepsize
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped Polynomial BigOperators

/-- Constructs `realization` of type `Realization Unit` by the displayed record fields. Data fields
specify the construction; proof fields discharge its required properties.
-/
def realization (gamma : ℕ → ℝ) : Realization Unit where
  b := fun _ => 1
  readout := fun _ => 1
  P := fun _ => 1
  g := fun s _ => gamma s
  q := fun _ _ => 1

/-- Defines `polynomial` by pattern matching with result type `ℕ → ℝ[X]`. The displayed branches
determine the recursive cases and their returned values.
-/
def polynomial (gamma : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => (1 - C (gamma n) * X) * polynomial gamma n

/-- Exact identity `orderedProduct (A := Matrix Unit Unit ℝ) (fun s => fun (_ _ : Unit) => c s) n
() () = orderedProduct c n`.
-/
private theorem product_entry (c : ℕ → ℝ) (n : ℕ) :
    orderedProduct (A := Matrix Unit Unit ℝ) (fun s => fun (_ _ : Unit) => c s) n () () = orderedProduct c n := by
  induction n with
  | zero => simp [orderedProduct]
  | succ n ih => simp [orderedProduct, Matrix.mul_apply, ih]

/-- Exact identity `(realization gamma).scalarContract M = M () ()`. -/
@[simp] theorem scalarContract (gamma : ℕ → ℝ) (M : Matrix Unit Unit ℝ) :
    (realization gamma).scalarContract M = M () () := by simp [Realization.scalarContract, realization]

/-- Exact identity `(realization gamma).scalarStep s lam = fun (_ _ : Unit) => 1 - gamma s * lam`. -/
theorem scalarStep_eq (gamma : ℕ → ℝ) (s : ℕ) (lam : ℝ) :
    (realization gamma).scalarStep s lam = fun (_ _ : Unit) => 1 - gamma s * lam := by
  ext i j
  cases i; cases j
  simp [Realization.scalarStep, Realization.queryFactor, realization, Matrix.vecMulVec,
    Matrix.sub_apply, mul_comm]

/-- Exact identity `(realization gamma).scalarTransfer n lam = orderedProduct (fun s => 1 - gamma s
* lam) n`.
-/
theorem scalarTransfer_eq (gamma : ℕ → ℝ) (n : ℕ) (lam : ℝ) :
    (realization gamma).scalarTransfer n lam =
      orderedProduct (fun s => 1 - gamma s * lam) n := by
  rw [Realization.scalarTransfer, scalarContract]
  simp_rw [scalarStep_eq]
  exact product_entry _ _

/-- Exact identity `(polynomial gamma n).eval lam = (realization gamma).scalarTransfer n lam`. -/
theorem polynomial_eval (gamma : ℕ → ℝ) (n : ℕ) (lam : ℝ) :
    (polynomial gamma n).eval lam = (realization gamma).scalarTransfer n lam := by
  rw [scalarTransfer_eq]
  induction n with
  | zero => simp [polynomial, orderedProduct]
  | succ n ih => simp [polynomial, orderedProduct, ih]

end
end InexactRealizations.Operators.Stepsize
