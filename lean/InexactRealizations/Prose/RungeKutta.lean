import InexactRealizations.History.Oracle
import InexactRealizations.History.Bezout
import InexactRealizations.Risk.Lower

/-! The exact Runge--Kutta identification asserted--2:
explicit tableaux and histories, actual stage/output equations, stability
polynomial, and the literal matrix internal-stability response. 
-/
namespace InexactRealizations.Prose.RungeKutta
noncomputable section
open Polynomial
open scoped BigOperators

structure ExplicitTableau (N : ℕ) where
  A : Fin N → Fin N → ℝ
  b : Fin N → ℝ
  explicit : ∀ s j, s ≤ j → A s j = 0

variable {N : ℕ}

def toHistory (T : ExplicitTableau N) : InexactRealizations.History N := ⟨T.A, T.b, T.explicit⟩

def tableauEquiv : ExplicitTableau N ≃ InexactRealizations.History N where
  toFun := toHistory
  invFun h := ⟨h.a, h.b, h.triangular⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def stage (T : ExplicitTableau N) (F : Fin N → E → E) (initial : E) (s : Fin N) : E :=
  -(toHistory T).oracleAnswers initial (fun j y ↦ -F j y) s

def output (T : ExplicitTableau N) (F : Fin N → E → E) (initial : E) : E :=
  initial + ∑ s, T.b s • stage T F initial s

theorem stage_equation (T : ExplicitTableau N) (F : Fin N → E → E) (initial : E) (s : Fin N) :
    stage T F initial s = F s (initial + ∑ j, T.A s j • stage T F initial j) := by
  rw [stage, (toHistory T).oracleAnswers_eq]
  simp only [neg_neg, stage, smul_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg,
    InexactRealizations.History.oracleQuery, toHistory]

theorem output_eq_history (T : ExplicitTableau N) (F : Fin N → E → E) (initial : E) :
    output T F initial = (toHistory T).oracleOutput initial (fun j y ↦ -F j y) := by
  simp only [output, stage, smul_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg, InexactRealizations.History.oracleOutput, toHistory]

def stability (T : ExplicitTableau N) : ℝ[X] := (toHistory T).terminal.comp (-X)

theorem test_equation (T : ExplicitTableau N) (z initial : ℝ) :
    output T (fun _ y ↦ z * y) initial = (stability T).eval z * initial := by
  rw [output_eq_history]
  have hor : (fun _ : Fin N ↦ fun y : ℝ ↦ -(z * y)) =
      (fun _ : Fin N ↦ fun y : ℝ ↦ (InexactRealizations.History.scalarOperator (-z)) y + 0) := by
    funext s y
    simp only [InexactRealizations.History.scalarOperator, Module.algebraMap_end_apply, smul_eq_mul, neg_mul, add_zero]
  rw [hor, InexactRealizations.History.oracleOutput_linear, InexactRealizations.Risk.scalar_output]
  simp only [mul_zero, Finset.sum_const_zero, add_zero, stability, eval_comp, eval_neg, eval_X]

theorem inverse_pencil (T : ExplicitTableau N) (z : ℝ) :
    (1 - z • Matrix.of T.A)⁻¹ = Matrix.of ((toHistory T).evaluated (-z)) := by
  apply Matrix.inv_eq_right_inv
  have hh := (toHistory T).scalarPencil_mul_evaluated (-z)
  simpa only [InexactRealizations.History.scalarPencil, toHistory, neg_smul, sub_eq_add_neg] using hh

def internalResponse (T : ExplicitTableau N) (z : ℝ) (j : Fin N) : ℝ :=
  z * ∑ s, T.b s * ((1 - z • Matrix.of T.A)⁻¹) s j

theorem internalResponse_physical (T : ExplicitTableau N) (lam : ℝ) (j : Fin N) :
    internalResponse T (-lam) j = lam * ((toHistory T).response j).eval lam := by
  rw [internalResponse, inverse_pencil, neg_neg, InexactRealizations.History.response_eval]
  simp only [Matrix.of_apply, toHistory]
  ring

end
end InexactRealizations.Prose.RungeKutta
