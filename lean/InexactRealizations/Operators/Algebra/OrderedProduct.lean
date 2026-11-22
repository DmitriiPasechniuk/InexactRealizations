import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Exact constant + linear + higher-order decomposition (algebraic).
Use: `InexactRealizations.Operators.orderedProduct_add_decomposition` feeds
`InexactRealizations.Operators.Realization.operatorTransfer_decomposition` (: an exact identity,
without any smallness assumption on the drift).
Proof chain: `InexactRealizations.Operators.Realization.static_shift_lower_bounds_general` — chebyshev1, Theorem
4.3; All insertion orders, partition bounds, finite/cosh bounds and attainment.
Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product. The needed form is proved here.
-/
namespace InexactRealizations.Operators

open scoped BigOperators

variable {A : Type*}

/-- `C (n-1) * ... * C 0`, with the empty product equal to one.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
def orderedProduct [Monoid A] (C : ℕ → A) : ℕ → A
  | 0 => 1
  | n + 1 => C n * orderedProduct C n

/-- Exact identity `orderedProduct C 0 = 1`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
@[simp] theorem orderedProduct_zero [Monoid A] (C : ℕ → A) :
    orderedProduct C 0 = 1 := rfl

/-- Exact identity `orderedProduct C (n + 1) = C n * orderedProduct C n`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
@[simp] theorem orderedProduct_succ [Monoid A] (C : ℕ → A) (n : ℕ) :
    orderedProduct C (n + 1) = C n * orderedProduct C n := rfl

/-- Exact identity `orderedProduct C n = orderedProduct D n`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
theorem orderedProduct_congr [Monoid A] {C D : ℕ → A} {n : ℕ}
    (h : ∀ i < n, C i = D i) : orderedProduct C n = orderedProduct D n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [orderedProduct_succ]
    rw [h n (by omega), ih (fun i hi => h i (by omega))]

/-- Splitting a causal product at a time boundary.

Exact identity `orderedProduct C (a + b) = orderedProduct (fun i => C (a + i)) b *
orderedProduct C a`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
theorem orderedProduct_add [Monoid A] (C : ℕ → A) (a b : ℕ) :
    orderedProduct C (a + b) =
      orderedProduct (fun i => C (a + i)) b * orderedProduct C a := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega, orderedProduct_succ,
      orderedProduct_succ, ih, mul_assoc]

/-- A change at one time has a fixed tail and prefix.

Exact identity `orderedProduct (Function.update C s v) n = orderedProduct (fun i => C (s + 1 +
i)) (n - (s + 1)) * v * orderedProduct C s`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
theorem orderedProduct_update [Monoid A] (C : ℕ → A) (v : A) {n s : ℕ} (hs : s < n) :
    orderedProduct (Function.update C s v) n =
      orderedProduct (fun i => C (s + 1 + i)) (n - (s + 1)) * v * orderedProduct C s := by
  rw [show n = (s + 1) + (n - (s + 1)) by omega, orderedProduct_add,
    orderedProduct_succ, Function.update_self]
  have htail : orderedProduct (fun i => Function.update C s v (s + 1 + i))
      (n - (s + 1)) = orderedProduct (fun i => C (s + 1 + i)) (n - (s + 1)) := by
    apply orderedProduct_congr
    intro i _
    simp [Function.update_of_ne (show s + 1 + i ≠ s by omega)]
  have hprefix : orderedProduct (Function.update C s v) s = orderedProduct C s := by
    apply orderedProduct_congr
    intro i hi
    simp [Function.update_of_ne (show i ≠ s by omega)]
  rw [htail, hprefix, mul_assoc]
  simp

/-- Replace the steps indexed by `S` by insertions `D`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
def insertionTerm [Monoid A] (C D : ℕ → A) (n : ℕ) (S : Finset ℕ) : A :=
  orderedProduct (fun i => if i ∈ S then D i else C i) n

/-- Exact identity `insertionTerm C D n ∅ = orderedProduct C n`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
@[simp] theorem insertionTerm_empty [Monoid A] (C D : ℕ → A) (n : ℕ) :
    insertionTerm C D n ∅ = orderedProduct C n := by simp [insertionTerm]

/-- Exact identity `insertionTerm C D (n + 1) (insert n S) = D n * insertionTerm C D n S`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
theorem insertionTerm_insert_last [Monoid A] (C D : ℕ → A) (n : ℕ)
    (S : Finset ℕ) :
    insertionTerm C D (n + 1) (insert n S) = D n * insertionTerm C D n S := by
  simp only [insertionTerm, orderedProduct_succ, Finset.mem_insert_self, ite_true]
  congr 1
  apply orderedProduct_congr
  intro i hi
  simp [show i ≠ n by omega]

/-- The exact finite expansion, indexed by insertion times; no commutativity is used.

Exact identity `orderedProduct (fun i => C i + D i) n = ∑ S ∈ (Finset.range n).powerset,
insertionTerm C D n S`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
theorem orderedProduct_add_expansion [Semiring A] (C D : ℕ → A) (n : ℕ) :
    orderedProduct (fun i => C i + D i) n =
      ∑ S ∈ (Finset.range n).powerset, insertionTerm C D n S := by
  induction n with
  | zero => simp [insertionTerm]
  | succ n ih =>
    rw [orderedProduct_succ, add_mul, ih, Finset.range_add_one,
      Finset.sum_powerset_insert (by simp)]
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro S hS
      have hn : n ∉ S := Finset.notMem_of_mem_powerset_of_notMem hS (by simp)
      simp [insertionTerm, hn]
    · apply Finset.sum_congr rfl
      intro S _
      exact (insertionTerm_insert_last C D n S).symm

/-- The contribution with exactly `k` insertions.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
def degreeTerm [Semiring A] (C D : ℕ → A) (n k : ℕ) : A :=
  ∑ S ∈ (Finset.range n).powersetCard k, insertionTerm C D n S

/-- Exact identity `degreeTerm C D n 0 = orderedProduct C n`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
@[simp] theorem degreeTerm_zero [Semiring A] (C D : ℕ → A) (n : ℕ) :
    degreeTerm C D n 0 = orderedProduct C n := by simp [degreeTerm]

/-- Exact identity `degreeTerm C D n 1 = ∑ s ∈ Finset.range n, insertionTerm C D n {s}`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
theorem degreeTerm_one [Semiring A] (C D : ℕ → A) (n : ℕ) :
    degreeTerm C D n 1 = ∑ s ∈ Finset.range n, insertionTerm C D n {s} := by simp [degreeTerm, Finset.powersetCard_one]

/-- A single insertion has the unperturbed tail on its left and prefix on its right.

Exact identity `insertionTerm C D n {s} = orderedProduct (fun i => C (s + 1 + i)) (n - (s + 1))
* D s * orderedProduct C s`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
theorem insertionTerm_singleton [Monoid A] (C D : ℕ → A) {n s : ℕ} (hs : s < n) :
    insertionTerm C D n {s} =
      orderedProduct (fun i => C (s + 1 + i)) (n - (s + 1)) *
        D s * orderedProduct C s := by
  unfold insertionTerm
  rw [show n = (s + 1) + (n - (s + 1)) by omega, orderedProduct_add,
    orderedProduct_succ]
  have htail : orderedProduct
      (fun i => if s + 1 + i ∈ ({s} : Finset ℕ) then D (s + 1 + i)
        else C (s + 1 + i)) (n - (s + 1)) =
      orderedProduct (fun i => C (s + 1 + i)) (n - (s + 1)) := by
    apply orderedProduct_congr
    intro i _
    simp [show s + 1 + i ≠ s by omega]
  have hprefix : orderedProduct (fun i => if i ∈ ({s} : Finset ℕ) then D i else C i) s =
      orderedProduct C s := by
    apply orderedProduct_congr
    intro i hi
    simp [show i ≠ s by omega]
  rw [htail, hprefix]
  simp [mul_assoc]

/-- The first-order part, before any input/output contraction.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
def firstVariation [Semiring A] (C D : ℕ → A) (n : ℕ) : A := degreeTerm C D n 1

/-- Exact identity `firstVariation C D n = ∑ s ∈ Finset.range n, orderedProduct (fun i => C (s + 1
+ i)) (n - (s + 1)) * D s * orderedProduct C s`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
theorem firstVariation_eq_sum [Semiring A] (C D : ℕ → A) (n : ℕ) :
    firstVariation C D n = ∑ s ∈ Finset.range n,
      orderedProduct (fun i => C (s + 1 + i)) (n - (s + 1)) *
        D s * orderedProduct C s := by
  rw [firstVariation, degreeTerm_one]
  apply Finset.sum_congr rfl
  intro s hs
  exact insertionTerm_singleton C D (Finset.mem_range.mp hs)

/-- Exact identity `firstVariation C D 0 = 0`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
@[simp] theorem firstVariation_zero [Semiring A] (C D : ℕ → A) :
    firstVariation C D 0 = 0 := by simp [firstVariation, degreeTerm_one]

end InexactRealizations.Operators
