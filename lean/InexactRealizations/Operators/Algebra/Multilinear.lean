import InexactRealizations.Operators.Algebra.OrderedProduct
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! The affine causal product is a finite polynomial in the drift scale.
Use: `InexactRealizations.Operators.orderedProduct_affine_by_degree` feeds
`InexactRealizations.Operators.Realization.operatorTransfer_affine_by_degree` (The full output is a
degree-at-most-`n` polynomial in the scalar drift size).
Proof chain: `InexactRealizations.Operators.JacobiData.operatorTransfer_driftOrders` — chebyshev1,;
All insertion orders, partition bounds, finite/cosh bounds and attainment.
Source: mathlib, Mathlib.LinearAlgebra.Multilinear.Basic — multilinearity of products in selected
factors. The needed form is proved here.
-/
namespace InexactRealizations.Operators

noncomputable section

variable {K A : Type*} [CommSemiring K] [Semiring A] [Algebra K A]

/-- Factors with independent variables only at the selected times.

Source: mathlib, Mathlib.LinearAlgebra.Multilinear.Basic — multilinearity of products in
selected factors.
-/
def selectedFactors (C : ℕ → A) (S : Finset ℕ) (v : S → A) (i : ℕ) : A :=
  if h : i ∈ S then v ⟨i, h⟩ else C i

omit [Semiring A] in
/-- Exact identity `selectedFactors C S (Function.update v s a) = Function.update (selectedFactors
C S v) s.val a`.

Source: mathlib, Mathlib.LinearAlgebra.Multilinear.Basic — multilinearity of products in
selected factors.
-/
theorem selectedFactors_update (C : ℕ → A) (S : Finset ℕ) (v : S → A)
    (s : S) (a : A) :
    selectedFactors C S (Function.update v s a) =
      Function.update (selectedFactors C S v) s.val a := by
  funext i
  by_cases hi : i = s.val
  · subst i
    simp [selectedFactors]
  · by_cases hS : i ∈ S
    · have hne : (⟨i, hS⟩ : S) ≠ s := by
        intro h
        exact hi (congrArg Subtype.val h)
      simp [selectedFactors, hS, hi, hne]
    · simp [selectedFactors, hS, hi]

/-- A term with `S.card` insertions is an actual `S`-indexed multilinear map.

Source: mathlib, Mathlib.LinearAlgebra.Multilinear.Basic — multilinearity of products in
selected factors.
-/
def insertionMultilinear (C : ℕ → A) (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range n) : MultilinearMap K (fun _ : S => A) A :=
  MultilinearMap.mk' (fun v => orderedProduct (selectedFactors C S v) n)
    (fun v s a b => by
      have hs : s.val < n := Finset.mem_range.mp (hS s.property)
      simp only [selectedFactors_update, orderedProduct_update _ _ hs]
      simp [mul_add, add_mul])
    (fun v s c a => by
      have hs : s.val < n := Finset.mem_range.mp (hS s.property)
      simp only [selectedFactors_update, orderedProduct_update _ _ hs]
      simp)

/-- Exact identity `insertionMultilinear (K := K) C n S hS (fun s => D s.val) = insertionTerm C D n
S`.

Source: mathlib, Mathlib.LinearAlgebra.Multilinear.Basic — multilinearity of products in
selected factors.
-/
theorem insertionMultilinear_apply (C D : ℕ → A) (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range n) :
    insertionMultilinear (K := K) C n S hS (fun s => D s.val) = insertionTerm C D n S := by
  unfold insertionMultilinear insertionTerm
  apply orderedProduct_congr
  intro i _
  simp [selectedFactors]

end
end InexactRealizations.Operators
