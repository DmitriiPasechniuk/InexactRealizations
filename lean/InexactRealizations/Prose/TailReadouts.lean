import InexactRealizations.Centered.Queries
import InexactRealizations.History.Oracle
import Mathlib.Order.Interval.Finset.Fin

/-! A weighted average of the actual Prefix iterates is one causal history
with the same actual oracle queries, not separate reruns of its prefixes. 
-/
namespace InexactRealizations.Prose.Tail
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ}

def readout (h : InexactRealizations.History N) (j : Fin (N + 1)) : InexactRealizations.History N where
  a := h.a
  b s := if hj : j.val < N then h.a ⟨j.val, hj⟩ s else h.b s
  triangular := h.triangular

theorem readout_query (h : InexactRealizations.History N) (j : Fin (N + 1)) (s : Fin N) :
    (readout h j).query s = h.query s := rfl

theorem queryHistory_terminal (h : InexactRealizations.History N) (s : Fin N) :
    (InexactRealizations.Centered.queryHistory h s).terminal = h.query s := by
  rw [h.query_recurrence]
  change 1 - X * ∑ j, C (h.a s j) * h.query j = _
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < s
  · simp only [hj, ite_true]
  · simp only [hj, ite_false, h.triangular s j (le_of_not_gt hj), C_0, mul_zero, zero_mul]

theorem readout_terminal (h : InexactRealizations.History N) (j : Fin (N + 1)) :
    (readout h j).terminal = if hj : j.val < N then h.query ⟨j.val, hj⟩ else h.terminal := by
  by_cases hj : j.val < N
  · rw [dite_eq_left hj]
    have he : readout h j = InexactRealizations.Centered.queryHistory h ⟨j.val, hj⟩ := by
      cases h
      simp only [readout, InexactRealizations.Centered.queryHistory, hj, dite_true]
    rw [he, queryHistory_terminal]
  · have he : readout h j = h := by cases h; simp only [readout, hj, dite_false]
    rw [he, dite_eq_right hj]

def average (h : InexactRealizations.History N) (weight : Fin (N + 1) → ℝ) : InexactRealizations.History N where
  a := h.a
  b s := ∑ j, weight j * (readout h j).b s
  triangular := h.triangular

theorem average_response (h : InexactRealizations.History N) (weight : Fin (N + 1) → ℝ) (s : Fin N) :
    (average h weight).response s = ∑ j, weight j • (readout h j).response s := by
  change -(∑ i, C (∑ j, weight j * (readout h j).b i) * h.resolvent i s) = _
  simp only [map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change -(∑ i, C (weight j) * C ((readout h j).b i) * h.resolvent i s) =
    weight j • -(∑ i, C ((readout h j).b i) * h.resolvent i s)
  rw [smul_eq_C_mul, mul_neg, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem average_terminal (h : InexactRealizations.History N) (weight : Fin (N + 1) → ℝ) (hw : ∑ j, weight j = 1) :
    (average h weight).terminal = ∑ j, weight j • (readout h j).terminal := by
  change 1 - X * (∑ i, C (∑ j, weight j * (readout h j).b i) * h.query i) = _
  simp only [map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hsum : (∑ j, weight j • (readout h j).terminal) =
      C (∑ j, weight j) - X * ∑ j, ∑ i, C (weight j) * C ((readout h j).b i) * h.query i := by
    simp only [InexactRealizations.History.terminal, readout_query, smul_eq_C_mul, mul_sub, mul_one,
      Finset.sum_sub_distrib, map_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, hw, C_1]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem same_answers (h g : InexactRealizations.History N) (ha : g.a = h.a) (initial : E) (oracle : Fin N → E → E) :
    g.oracleAnswers initial oracle = h.oracleAnswers initial oracle := by
  apply h.oracleAnswers_unique initial oracle
  intro s
  have he := g.oracleAnswers_eq initial oracle s
  simpa only [InexactRealizations.History.oracleQuery, ha] using he

theorem average_output (h : InexactRealizations.History N) (weight : Fin (N + 1) → ℝ) (hw : ∑ j, weight j = 1)
    (initial : E) (oracle : Fin N → E → E) :
    (average h weight).oracleOutput initial oracle = ∑ j, weight j • (readout h j).oracleOutput initial oracle := by
  simp only [InexactRealizations.History.oracleOutput]
  rw [same_answers h (average h weight) rfl]
  simp_rw [same_answers h (readout h _) rfl]
  change initial - ∑ s, (∑ j, weight j * (readout h j).b s) • h.oracleAnswers initial oracle s = _
  simp only [Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp only [smul_sub, Finset.smul_sum, Finset.sum_sub_distrib, ← Finset.sum_smul, hw, one_smul]

def start (N : ℕ) : ℕ := (N + 1) / 2

def indices (N : ℕ) : Finset (Fin (N + 1)) := Finset.Ici ⟨start N, by unfold start; omega⟩

def weights (N : ℕ) (j : Fin (N + 1)) : ℝ :=
  if j ∈ indices N then (indices N).card⁻¹ else 0

theorem indices_card (N : ℕ) : (indices N).card = N + 1 - start N := Fin.card_Ici _

theorem indices_card_pos (N : ℕ) : 0 < (indices N).card := by rw [indices_card]; unfold start; omega

theorem weights_sum (N : ℕ) : ∑ j, weights N j = 1 := by
  simp only [weights, ← Finset.sum_filter]
  have hset : (Finset.univ.filter (fun j : Fin (N + 1) ↦ j ∈ indices N)) = indices N := by ext j; simp
  rw [hset]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : ((indices N).card : ℝ) ≠ 0 := by exact_mod_cast (indices_card_pos N).ne'
  exact mul_inv_cancel₀ hc

end
end InexactRealizations.Prose.Tail
