import InexactRealizations.Operators.Algebra.OrderedProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Input/output contraction is linear in the memory-space operator.
Use: `InexactRealizations.Operators.Realization.operatorTransfer` feeds
`InexactRealizations.Operators.Realization.kernel_sum_derivative` (The sum of all insertion kernels is the
derivative under a static spectral shift).
Proof chain: `InexactRealizations.Operators.Prefix.operator_exact` — chebyshev1,; Prefix-exact
recurrence and quadratic transfer.
-/
namespace InexactRealizations.Operators

noncomputable section

open scoped BigOperators Kronecker Polynomial

/-- The data `(b, ℓ, P_s, g_s, q_s)`. -/
structure Realization (ι : Type*) where
  /-- Initial memory vector multiplying the initial physical error. -/
  b : ι → ℝ
  /-- Linear functional selecting the terminal physical error from memory. -/
  readout : ι → ℝ
  /-- Unperturbed memory transition matrix at each iteration. -/
  P : ℕ → Matrix ι ι ℝ
  /-- Injection vector for the Hessian/query correction at each iteration. -/
  g : ℕ → ι → ℝ
  /-- Query vector selecting which memory combination the Hessian acts on. -/
  q : ℕ → ι → ℝ

namespace Realization

variable {ι d : Type*} [Fintype ι] [DecidableEq ι]

/-- The rank-one gradient-query factor `g_s q_sᵀ`. -/
def queryFactor (R : Realization ι) (s : ℕ) : Matrix ι ι ℝ :=
  Matrix.vecMulVec (R.g s) (R.q s)

/-- The scalar spectral pencil `C_s(lam)`. -/
def scalarStep (R : Realization ι) (s : ℕ) (lam : ℝ) : Matrix ι ι ℝ :=
  R.P s - lam • R.queryFactor s

/-- Input/output contraction in scalar spectral coordinates. -/
def scalarContract (R : Realization ι) (M : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, R.readout i * M i j * R.b j

/-- Defines `scalarTransfer` of type `ℝ` by `R.scalarContract (orderedProduct (fun s =>
R.scalarStep s lam) n)`.
-/
def scalarTransfer (R : Realization ι) (n : ℕ) (lam : ℝ) : ℝ :=
  R.scalarContract (orderedProduct (fun s => R.scalarStep s lam) n)

/-- A polynomial matrix, so terminal exactness is an equality of polynomials. -/
def polynomialStep (R : Realization ι) (s : ℕ) : Matrix ι ι ℝ[X] :=
  fun i j => Polynomial.C (R.P s i j) -
    Polynomial.X * Polynomial.C (R.g s i * R.q s j)

/-- Defines `residualPolynomial` of type `ℝ[X]` by `∑ i, ∑ j, Polynomial.C (R.readout i) *
orderedProduct R.polynomialStep n i j * Polynomial.C (R.b j)`.
-/
def residualPolynomial (R : Realization ι) (n : ℕ) : ℝ[X] :=
  ∑ i, ∑ j, Polynomial.C (R.readout i) *
    orderedProduct R.polynomialStep n i j * Polynomial.C (R.b j)

omit [Fintype ι] [DecidableEq ι] in
/-- Exact identity `(R.polynomialStep s).map (Polynomial.eval lam) = R.scalarStep s lam`. -/
theorem polynomialStep_eval (R : Realization ι) (s : ℕ) (lam : ℝ) :
    (R.polynomialStep s).map (Polynomial.eval lam) = R.scalarStep s lam := by
  ext i j
  simp [polynomialStep, scalarStep, queryFactor, Matrix.vecMulVec]

/-- Exact identity `(orderedProduct R.polynomialStep n).map (Polynomial.eval lam) = orderedProduct
(fun s => R.scalarStep s lam) n`.
-/
theorem orderedProduct_polynomialStep_eval (R : Realization ι) (n : ℕ) (lam : ℝ) :
    (orderedProduct R.polynomialStep n).map (Polynomial.eval lam) =
      orderedProduct (fun s => R.scalarStep s lam) n := by
  induction n with
  | zero => ext i j; by_cases h : i = j <;> simp [h]
  | succ n ih =>
    rw [orderedProduct_succ, orderedProduct_succ]
    rw [show (R.polynomialStep n * orderedProduct R.polynomialStep n).map
        (Polynomial.eval lam) = (R.polynomialStep n).map (Polynomial.eval lam) *
        (orderedProduct R.polynomialStep n).map (Polynomial.eval lam) from
      Matrix.map_mul (f := Polynomial.evalRingHom lam)]
    rw [polynomialStep_eval, ih]

/-- The transfer defined by the ordered realization evaluates its residual polynomial.

Exact identity `(R.residualPolynomial n).eval lam = R.scalarTransfer n lam`.
-/
theorem residualPolynomial_eval (R : Realization ι) (n : ℕ) (lam : ℝ) :
    (R.residualPolynomial n).eval lam = R.scalarTransfer n lam := by
  simp only [residualPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, scalarTransfer, scalarContract]
  have h := R.orderedProduct_polynomialStep_eval n lam
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← h]
  rfl

/-- Time-ordered two-spectral-variable kernel. -/
def kernel (R : Realization ι) (n s : ℕ) (lam nu : ℝ) : ℝ :=
  -R.scalarContract
    (orderedProduct (fun i => R.scalarStep (s + 1 + i) lam) (n - (s + 1)) *
      R.queryFactor s * orderedProduct (fun i => R.scalarStep i nu) s)

variable [Fintype d] [DecidableEq d]

/-- `P_s ⊗ I - (g_s q_sᵀ) ⊗ H`, in coordinates on memory × physical space. -/
def operatorStep (R : Realization ι) (s : ℕ) (H : Matrix d d ℝ) :
    Matrix (ι × d) (ι × d) ℝ :=
  R.P s ⊗ₖ (1 : Matrix d d ℝ) - R.queryFactor s ⊗ₖ H

/-- The signed insertion caused by a Hessian perturbation. -/
def operatorInsertion (R : Realization ι) (s : ℕ) (E : Matrix d d ℝ) :
    Matrix (ι × d) (ι × d) ℝ :=
  -(R.queryFactor s ⊗ₖ E)

/-- `(ℓᵀ ⊗ I) M (b ⊗ I)` without auxiliary singleton indices. -/
def contract (R : Realization ι) (M : Matrix (ι × d) (ι × d) ℝ) : Matrix d d ℝ :=
  fun x y => ∑ i, ∑ j, R.readout i * M (i, x) (j, y) * R.b j

/-- Input/output contraction is linear in the memory-space operator. -/
def contractLinear (R : Realization ι) :
    Matrix (ι × d) (ι × d) ℝ →ₗ[ℝ] Matrix d d ℝ where
  toFun := R.contract
  map_add' M N := by
    ext x y
    simp [contract, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    ext x y
    simp [contract, Finset.mul_sum, mul_assoc, mul_left_comm]

omit [DecidableEq ι] [Fintype d] [DecidableEq d] in
/-- Exact identity `R.contractLinear M = R.contract M`. -/
@[simp] theorem contractLinear_apply (R : Realization ι)
    (M : Matrix (ι × d) (ι × d) ℝ) : R.contractLinear M = R.contract M := rfl

end Realization
end
end InexactRealizations.Operators
