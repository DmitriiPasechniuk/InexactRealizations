import InexactRealizations.Channel.Signal

namespace InexactRealizations.Channel
noncomputable section
open scoped BigOperators
variable {N : ℕ} {J : Type*} [Fintype J]

/-- Euclidean action of a rectangular temporal channel matrix. -/
def rectangularOperator (M : Matrix J (Fin N) ℝ) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ J :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

/-- The squared Hilbert--Schmidt norm, with every actual spectral row retained. -/
def rectangularHsSq (M : Matrix J (Fin N) ℝ) : ℝ := ∑ j, ∑ s, M j s^2

/-- The actual matrix action in coordinates. -/
@[simp] theorem rectangularOperator_apply (M : Matrix J (Fin N) ℝ)
    (e : EuclideanSpace ℝ (Fin N)) (j : J) :
    rectangularOperator M e j=∑ s, M j s*e s := rfl

variable [DecidableEq J]

/-- Retain exactly the spectral rows in a chosen finite signal block. -/
def rowMask (F : Finset J) (M : Matrix J (Fin N) ℝ) : Matrix J (Fin N) ℝ :=
  fun j s => if j∈F then M j s else 0

/-- A row mask acts as the orthogonal coordinate mask after the actual channel action. -/
@[simp] theorem rowMask_action (F : Finset J) (M : Matrix J (Fin N) ℝ)
    (e : EuclideanSpace ℝ (Fin N)) (j : J) :
    rectangularOperator (rowMask F M) e j=if j∈F then rectangularOperator M e j else 0 := by
  by_cases hj : j∈F <;> simp [rectangularOperator_apply, rowMask, hj]

end
end InexactRealizations.Channel
