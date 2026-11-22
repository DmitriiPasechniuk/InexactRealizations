import InexactRealizations.Prose.TailReadouts
import InexactRealizations.Comparisons.Competitors.Prefix

/-! Each intermediate readout of the one actual Prefix trajectory has
exactly the original shorter Prefix response, extended by zero after its
last call. Therefore tail averaging averages the physical responses. 
-/
namespace InexactRealizations.Prose.Tail
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ}

theorem sum_extend {R : Type*} [AddCommMonoid R] (m n : ℕ) (hm : m ≤ n) (f : Fin m → R) :
    (∑ s : Fin n, if hs : s.val < m then f ⟨s.val, hs⟩ else 0) = ∑ s : Fin m, f s := by
  induction n generalizing m with
  | zero =>
    have hm0 : m = 0 := by omega
    subst m
    simp
  | succ n ih =>
    by_cases hmN : m ≤ n
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, show ¬n < m by omega, dite_false, add_zero]
      exact ih m hmN f
    · have he : m = n + 1 := by omega
      subst m
      simp only [Fin.is_lt, dite_true, Fin.eta]

theorem prefix_query (I : InexactRealizations.Operators.SpectralInterval) (M : ℕ) (s : Fin M) :
    (InexactRealizations.Classical.history I M).query s = I.residual s.val := by
  rw [← InexactRealizations.Comparisons.Competitors.Prefix.history_eq_classical,
    InexactRealizations.Comparisons.Competitors.Prefix.query_polynomial]

theorem prefix_readout_terminal (I : InexactRealizations.Operators.SpectralInterval) (j : Fin (N + 1)) :
    (readout (InexactRealizations.Classical.history I N) j).terminal = I.residual j.val := by
  rw [readout_terminal]
  split_ifs with hj
  · exact prefix_query I N ⟨j.val, hj⟩
  · have hjN : j.val = N := by omega
    rw [hjN]
    exact InexactRealizations.Classical.history_exact I N

def extendedResponse (I : InexactRealizations.Operators.SpectralInterval) (m : ℕ) (s : Fin N) : ℝ[X] :=
  if hs : s.val < m then (InexactRealizations.Classical.history I m).response ⟨s.val, hs⟩ else 0

theorem extended_tensor (I : InexactRealizations.Operators.SpectralInterval) (m : ℕ) (hm : m ≤ N) (x y : ℝ) :
    (∑ s : Fin N, (extendedResponse I m s).eval x * (I.residual s.val).eval y) =
      InexactRealizations.History.dividedDifference (I.residual m) x y := by
  have hs := sum_extend m N hm
    (fun s : Fin m ↦ ((InexactRealizations.Classical.history I m).response s).eval x * (I.residual s.val).eval y)
  have hh := (InexactRealizations.Classical.history I m).physical_bezout_all x y
  rw [InexactRealizations.Classical.history_exact I m] at hh
  simp_rw [prefix_query I m] at hh
  apply Eq.trans (b := ∑ s : Fin m, ((InexactRealizations.Classical.history I m).response s).eval x * (I.residual s.val).eval y) ?_ hh
  convert hs using 1
  apply Finset.sum_congr rfl
  intro s _
  unfold extendedResponse
  split_ifs <;> simp

theorem prefix_readout_response (I : InexactRealizations.Operators.SpectralInterval) (j : Fin (N + 1)) (s : Fin N) :
    (readout (InexactRealizations.Classical.history I N) j).response s = extendedResponse I j.val s := by
  let Q := (InexactRealizations.Classical.queryFamily I N).physical I
  have hQ (i : Fin N) (y : ℝ) : (Q.poly i).eval y = (I.residual i.val).eval y := by
    rw [InexactRealizations.GradedFamily.physical_eval, I.residual_eval]
    simp only [InexactRealizations.Classical.queryFamily, eval_mul, eval_C, one_div_mul_eq_div]
  apply Polynomial.funext
  intro x
  have hpoly : (∑ i : Fin N, ((readout (InexactRealizations.Classical.history I N) j).response i).eval x • Q.poly i) =
      ∑ i : Fin N, (extendedResponse I j.val i).eval x • Q.poly i := by
    apply Polynomial.funext
    intro y
    simp only [eval_finsetSum, eval_smul, smul_eq_mul, hQ]
    have hh := (readout (InexactRealizations.Classical.history I N) j).physical_bezout_all x y
    simp_rw [readout_query, prefix_query] at hh
    rw [prefix_readout_terminal] at hh
    exact hh.trans (extended_tensor I j.val (by omega) x y).symm
  exact congrFun (Q.expansion_unique _ _ hpoly) s

def history (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : InexactRealizations.History N :=
  average (InexactRealizations.Classical.history I N) (weights N)

theorem terminal (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    (history I N).terminal = ∑ j : Fin (N + 1), weights N j • I.residual j.val := by
  rw [history, average_terminal _ _ (weights_sum N)]
  simp_rw [prefix_readout_terminal]

theorem response (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (s : Fin N) :
    (history I N).response s = ∑ j : Fin (N + 1), weights N j • extendedResponse I j.val s := by
  rw [history, average_response]
  simp_rw [prefix_readout_response]

end
end InexactRealizations.Prose.Tail
