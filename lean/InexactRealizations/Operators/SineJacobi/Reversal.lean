import InexactRealizations.Operators.SineJacobi.LeadingBounds
import Mathlib.Data.Fin.Rev

/-! Reversing a terminal block gives the corresponding leading block.
Use: `InexactRealizations.Operators.SineJacobi.tail_eq_leading_of_end` feeds
`InexactRealizations.Operators.SineJacobi.resolvent_diagonal` (resolvent diagonal).
Proof chain: `InexactRealizations.Operators.SineJacobi.gain_exact` — chebyshev1,; Exact sine gain,
resolvent expression, asymptotics and energy value.
-/
namespace InexactRealizations.Operators.SineJacobi
noncomputable section
open Polynomial

/-- Exact identity `(data N).aSq (N-s) = (data N).aSq s`. -/
theorem data_aSq_reflect (N s : ℕ) (hs : s ≤ N) : (data N).aSq (N-s) = (data N).aSq s := by
  by_cases hs0 : s = 0
  · subst s; simp [data]
  · by_cases hsN : s = N
    · subst s; simp [data]
    · rw [data_aSq N (N-s) (by omega) (by omega), data_aSq N s (by omega) (by omega)]
      exact couplingSq_reflect N s (by omega) (by omega)

/-- Reversing a terminal block gives the corresponding leading block.

Exact identity `((data N).matrix (N-n) n).submatrix Fin.rev Fin.rev = (data N).matrix 0 n`.
-/
theorem tail_matrix_reverse (N n : ℕ) (hn : n ≤ N) :
    ((data N).matrix (N-n) n).submatrix Fin.rev Fin.rev = (data N).matrix 0 n := by
  apply Matrix.ext
  intro i j
  rw [Matrix.submatrix_apply, JacobiData.matrix_apply, JacobiData.matrix_apply]
  simp only [data_b, Nat.zero_add]
  by_cases hij : i = j
  · subst j; simp
  · have hrev : i.rev ≠ j.rev := fun h => hij (Fin.rev_injective h)
    rw [ite_eq_right hrev, ite_eq_right hij]
    have h1 : i.rev.val+1 = j.rev.val ↔ j.val+1 = i.val := by
      dsimp [Fin.rev]
      omega
    have h2 : j.rev.val+1 = i.rev.val ↔ i.val+1 = j.val := by
      dsimp [Fin.rev]
      omega
    simp only [h1, h2]
    by_cases hup : i.val+1 = j.val
    · have hdown : ¬j.val+1 = i.val := by omega
      simp only [ite_eq_left hup, ite_eq_right hdown]
      rw [show N-n+i.rev.val = N-j.val by dsimp [Fin.rev]; omega,
        data_aSq_reflect N j.val (by omega)]
    · by_cases hdown : j.val+1 = i.val
      · simp only [ite_eq_left hdown, ite_eq_right hup]
        rw [show N-n+j.rev.val = N-i.val by dsimp [Fin.rev]; omega,
          data_aSq_reflect N i.val (by omega)]
      · simp only [ite_eq_right hup, ite_eq_right hdown]

/-- Exact identity `(data N).block (N-n) n = (data N).leading n`. -/
theorem tail_eq_leading (N n : ℕ) (hn : n ≤ N) :
    (data N).block (N-n) n = (data N).leading n := by
  rw [JacobiData.block_eq_charpoly _ (data_aSq_nonneg N), JacobiData.leading,
    JacobiData.block_eq_charpoly _ (data_aSq_nonneg N)]
  have hc := Matrix.charpoly_reindex (Fin.revPerm : Fin n ≃ Fin n) ((data N).matrix (N-n) n)
  have he : Matrix.reindex (Fin.revPerm : Fin n ≃ Fin n) Fin.revPerm ((data N).matrix (N-n) n) =
      (data N).matrix 0 n := tail_matrix_reverse N n hn
  rw [he] at hc
  exact hc.symm

/-- The stated quantitative bound `|((data N).block a n).eval x| ≤ ((data N).block a n).eval 1`. -/
theorem tail_endpoint_max (N a n : ℕ) (ha : a+n = N) (hn : n < N)
    (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) :
    |((data N).block a n).eval x| ≤ ((data N).block a n).eval 1 := by
  rw [show a = N-n by omega, tail_eq_leading N n hn.le]
  exact leading_endpoint_max N n hn x hx

end
end InexactRealizations.Operators.SineJacobi
