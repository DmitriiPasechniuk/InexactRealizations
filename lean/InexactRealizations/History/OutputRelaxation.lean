import InexactRealizations.History.Oracle

/-! Relax only the physical output weights. Every actual oracle query is
preserved, including for arbitrary nonlinear and time-dependent oracles. 
-/
namespace InexactRealizations.History
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ}

def relax (h : InexactRealizations.History N) (ω : ℝ) : InexactRealizations.History N where
  a := h.a
  b s := ω * h.b s
  triangular := h.triangular

@[simp] theorem relax_one (h : InexactRealizations.History N) : h.relax 1 = h := by
  cases h
  simp only [relax, one_mul]

theorem relax_response (h : InexactRealizations.History N) (ω : ℝ) (s : Fin N) :
    (h.relax ω).response s = C ω * h.response s := by
  change -(∑ j, C (ω * h.b j) * h.resolvent j s) = C ω * -(∑ j, C (h.b j) * h.resolvent j s)
  rw [mul_neg, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]
  ring

theorem relax_terminal (h : InexactRealizations.History N) (ω : ℝ) :
    (h.relax ω).terminal = 1 - C ω + C ω * h.terminal := by
  change 1 - X * ∑ j, C (ω * h.b j) * h.query j = 1 - C ω + C ω * (1 - X * ∑ j, C (h.b j) * h.query j)
  have hs : (∑ j, C (ω * h.b j) * h.query j) = C ω * ∑ j, C (h.b j) * h.query j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul]
    ring
  rw [hs]
  ring

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end
end InexactRealizations.History
