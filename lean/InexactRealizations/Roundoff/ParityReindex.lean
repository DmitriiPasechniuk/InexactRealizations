import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

/-! Exact reindexing of the parity impulse-response triangle. -/
namespace InexactRealizations.Roundoff
noncomputable section
open scoped BigOperators

def parityTriangleEquiv (N : ℕ) :
    ((j : Fin N) × Fin (j.val / 2)) ≃ ((s : Fin (N - 2)) × Fin ((N - 1 - s.val) / 2)) where
  toFun p :=
    ⟨⟨p.1.val - 2 * (p.2.val + 1), by have := p.1.isLt; have := p.2.isLt; omega⟩,
      ⟨p.2.val, by
        change p.2.val < (N - 1 - (p.1.val - 2 * (p.2.val + 1))) / 2
        have := p.1.isLt; have := p.2.isLt; omega⟩⟩
  invFun p :=
    ⟨⟨p.1.val + 2 * (p.2.val + 1), by have := p.1.isLt; have := p.2.isLt; omega⟩,
      ⟨p.2.val, by
        change p.2.val < (p.1.val + 2 * (p.2.val + 1)) / 2
        omega⟩⟩
  left_inv p := by
    rcases p with ⟨j, i⟩
    have hi := i.isLt
    apply Sigma.ext
    · apply Fin.ext
      dsimp
      omega
    · exact (Fin.heq_ext_iff (by dsimp; omega)).mpr rfl
  right_inv p := by
    rcases p with ⟨s, i⟩
    apply Sigma.ext
    · apply Fin.ext
      dsimp
      omega
    · exact (Fin.heq_ext_iff (by dsimp; omega)).mpr rfl

theorem parity_triangle_sum {E : Type*} [AddCommMonoid E] (N : ℕ) (f : ℕ → ℕ → E) :
    (∑ j : Fin N, ∑ i : Fin (j.val / 2), f (j.val - 2 * (i.val + 1)) j.val) =
      ∑ s : Fin (N - 2), ∑ i : Fin ((N - 1 - s.val) / 2), f s.val (s.val + 2 * (i.val + 1)) := by
  have hh := Fintype.sum_equiv (parityTriangleEquiv N)
    (fun p ↦ f (p.1.val - 2 * (p.2.val + 1)) p.1.val)
    (fun p ↦ f p.1.val (p.1.val + 2 * (p.2.val + 1))) (by
      intro p
      have hi := p.2.isLt
      dsimp [parityTriangleEquiv]
      congr 1
      omega)
  simpa only [Fintype.sum_sigma] using hh

end
end InexactRealizations.Roundoff
