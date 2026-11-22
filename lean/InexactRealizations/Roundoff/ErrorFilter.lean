import InexactRealizations.Roundoff.AverageCoefficients

/-! The exact parity filter of the gradient discrepancies.
The weighted identity includes zero startup mass, rather than assuming
every averaging mass to be positive. 
-/
namespace InexactRealizations.Roundoff
noncomputable section
open InexactRealizations.Balanced InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def averageError (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (w iota : ℕ → E) : ℕ → E
  | 0 => w 0 + iota 0
  | 1 => w 1 + iota 1
  | s + 2 => (1 - phi I N (s + 2) / theta I N (s + 2)) • averageError I N w iota s +
      (phi I N (s + 2) / theta I N (s + 2)) • w (s + 2) + iota (s + 2)

def recoveredError (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (w iota : ℕ → E) (s : ℕ) : E :=
  if s < 2 then w s else (theta I N s)⁻¹ • (w s - (1 - theta I N s) • averageError I N w iota (s - 2))

def parityAccum (f : ℕ → E) : ℕ → E
  | 0 => f 0
  | 1 => f 1
  | s + 2 => parityAccum f s + f (s + 2)

def averageWeight (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ :=
  mass I N (s + 2) / omega N (s + 2)

theorem averageError_add (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (w v iota kappa : ℕ → E) (s : ℕ) :
    averageError I N (w + v) (iota + kappa) s =
      averageError I N w iota s + averageError I N v kappa s := by
  induction s using Nat.twoStepInduction with
  | zero => simp only [averageError, Pi.add_apply]; abel
  | one => simp only [averageError, Pi.add_apply]; abel
  | more s ih _ => simp only [averageError, ih, Pi.add_apply, smul_add]; abel

theorem recoveredError_add (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (w v iota kappa : ℕ → E) (s : ℕ) :
    recoveredError I N (w + v) (iota + kappa) s =
      recoveredError I N w iota s + recoveredError I N v kappa s := by
  unfold recoveredError
  split_ifs
  · rfl
  · simp only [Pi.add_apply, averageError_add, smul_add]
    module

theorem averageError_zero (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    averageError I N (0 : ℕ → E) 0 s = 0 := by
  induction s using Nat.twoStepInduction with
  | zero => simp [averageError]
  | one => simp [averageError]
  | more s ih _ => simp [averageError, ih]

theorem recoveredError_split (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (w iota : ℕ → E) (s : ℕ) :
    recoveredError I N w iota s = recoveredError I N w 0 s + recoveredError I N 0 iota s := by
  simpa only [add_zero, zero_add] using recoveredError_add I N w 0 0 iota s

theorem weighted_averageError (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s + 2 < N) (iota : ℕ → E) :
    averageWeight I N s • averageError I N 0 iota s =
      parityAccum (fun j ↦ averageWeight I N j • iota j) s := by
  induction s using Nat.twoStepInduction with
  | zero => simp [averageError, parityAccum]
  | one => simp [averageError, parityAccum]
  | more s ih _ =>
    have hc : averageWeight I N (s + 2) * (1 - phi I N (s + 2) / theta I N (s + 2)) =
        averageWeight I N s := by
      exact average_error_telescope I hN (by omega : 2 ≤ s + 2) hs
    simp only [averageError, Pi.zero_apply, smul_zero, add_zero, smul_add, smul_smul,
      hc, parityAccum, ih (by omega : s + 2 < N)]

theorem recovered_averageError (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : 2 ≤ s) (hsN : s < N) (iota : ℕ → E) :
    recoveredError I N 0 iota s =
      -(I.den s)⁻¹ • parityAccum (fun j ↦ averageWeight I N j • iota j) (s - 2) := by
  have hsmall : ¬s < 2 := by omega
  have hindex : s - 2 + 2 = s := by omega
  have hw := weighted_averageError I hN (by omega : s - 2 + 2 < N) iota
  rw [recoveredError, ite_eq_right hsmall]
  simp only [Pi.zero_apply, zero_sub, smul_neg, smul_smul]
  rw [← hw]
  have hc : (theta I N s)⁻¹ * (1 - theta I N s) = (I.den s)⁻¹ * averageWeight I N (s - 2) := by
    have hh := recovery_average_coefficient I hN hsN
    unfold averageWeight
    rw [hindex]
    rw [div_eq_mul_inv] at hh
    rw [mul_comm] at hh
    rw [hh]
    ring
  rw [hc]
  simp only [smul_smul, neg_mul, neg_smul]

omit [Module ℝ E] in
theorem parityAccum_sum (f : ℕ → E) (s : ℕ) :
    parityAccum f s = ∑ i ∈ Finset.range (s / 2 + 1), f (s - 2 * i) := by
  induction s using Nat.twoStepInduction with
  | zero => simp [parityAccum]
  | one => simp [parityAccum]
  | more s ih _ =>
    have hdiv : (s + 2) / 2 + 1 = (s / 2 + 1) + 1 := by omega
    have hh : (∑ i ∈ Finset.range (s / 2 + 1), f (s + 2 - 2 * (i + 1))) =
        ∑ i ∈ Finset.range (s / 2 + 1), f (s - 2 * i) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    have hright : (∑ i ∈ Finset.range ((s + 2) / 2 + 1), f (s + 2 - 2 * i)) =
        f (s + 2) + ∑ i ∈ Finset.range (s / 2 + 1), f (s - 2 * i) := by
      rw [hdiv, Finset.sum_range_succ', hh]
      simp only [mul_zero, Nat.sub_zero]
      abel
    rw [parityAccum, ih, hright]
    abel

theorem recovered_iota_sum (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s < N) (iota : ℕ → E) :
    recoveredError I N 0 iota s = -(I.den s)⁻¹ •
      ∑ i : Fin (s / 2), averageWeight I N (s - 2 * (i.val + 1)) • iota (s - 2 * (i.val + 1)) := by
  have hf : (∑ i : Fin (s / 2), averageWeight I N (s - 2 * (i.val + 1)) • iota (s - 2 * (i.val + 1))) =
      ∑ i ∈ Finset.range (s / 2), averageWeight I N (s - 2 * (i + 1)) • iota (s - 2 * (i + 1)) :=
    Fin.sum_univ_eq_sum_range (fun i ↦ averageWeight I N (s - 2 * (i + 1)) • iota (s - 2 * (i + 1))) (s / 2)
  rw [hf]
  by_cases hsmall : s < 2
  · have hdiv : s / 2 = 0 := by omega
    simp [recoveredError, hsmall, hdiv]
  · rw [recovered_averageError I hN (by omega) hs, parityAccum_sum]
    have hdiv : (s - 2) / 2 + 1 = s / 2 := by omega
    rw [hdiv]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hi : s - 2 - 2 * i = s - 2 * (i + 1) := by omega
    rw [hi]

end
end InexactRealizations.Roundoff
