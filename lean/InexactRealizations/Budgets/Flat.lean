import InexactRealizations.Budgets.Additive
import InexactRealizations.Flat.Response

/-! Current Theorem5.1(a), with the literal all-dimension actual-execution
risk and every gamma, including both endpoints. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open scoped BigOperators ENNReal NNReal
variable {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]

theorem additive_corner_chain (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    I.epsilon N * r + t * (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.additiveScale I N ≤
      I.epsilon N * r + t * callNorm q (fun s : Fin N ↦ (h.response s).eval I.mu) ∧
    I.epsilon N * r + t * callNorm q (fun s : Fin N ↦ (h.response s).eval I.mu) ≤ additiveRisk p h I r t := by
  have hh := mul_le_mul_of_nonneg_left (additive_endpoint_lower (p := p) (q := q) h I he hN) ht
  constructor
  · nlinarith
  · exact additiveRisk_endpoint_lower h I he hN hr ht

theorem positive_constant_profile [Nonempty (Fin N)] (I : InexactRealizations.Operators.SpectralInterval) :
    callNorm q (fun _ : Fin N ↦ InexactRealizations.Lower.additiveScale I N / N) =
      (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.additiveScale I N := by
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hS := InexactRealizations.Risk.additiveScale_nonneg I N
  have habs : (fun _ : Fin N ↦ InexactRealizations.Lower.additiveScale I N / N) =
      (fun _ : Fin N ↦ |-(InexactRealizations.Lower.additiveScale I N / N)|) := by
    funext s
    exact (abs_of_nonneg (div_nonneg hS (Nat.cast_nonneg N))).symm.trans (abs_neg _).symm
  rw [habs, callNorm_abs]
  simpa only [Fintype.card_fin, neg_div] using constant_signed_profile (p := p) (q := q) (ι := Fin N) hS

include q in
theorem flat_all_budgets (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N)
    {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    additiveRisk p (InexactRealizations.Flat.history I N hN) I r t =
      I.epsilon N * r + t * (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.additiveScale I N := by
  let : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  let h := InexactRealizations.Flat.history I N hN
  have he := InexactRealizations.Flat.history_exact I N hN
  have hup := additiveRisk_upper (p := p) (q := q) h I he
    (fun _ ↦ InexactRealizations.Lower.additiveScale I N / N)
    ⟨fun _ ↦ div_nonneg (InexactRealizations.Risk.additiveScale_nonneg I N) (Nat.cast_nonneg N),
      fun s x hx ↦ (InexactRealizations.Flat.response_uniform_sharp I N hN s).1 x hx⟩ hr ht
  rw [positive_constant_profile (p := p) (q := q) I] at hup
  have hlow := additiveRisk_endpoint_lower (p := p) (q := q) h I he (by omega) hr ht
  have hprofile : (fun s : Fin N ↦ (h.response s).eval I.mu) =
      (fun _ : Fin N ↦ -InexactRealizations.Lower.additiveScale I N / N) := by
    funext s
    simpa only [neg_div] using InexactRealizations.Flat.response_mu I N hN s
  rw [hprofile, show callNorm q (fun _ : Fin N ↦ -InexactRealizations.Lower.additiveScale I N / N) =
    (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.additiveScale I N by
      simpa only [Fintype.card_fin] using constant_signed_profile (p := p) (q := q) (ι := Fin N)
        (InexactRealizations.Risk.additiveScale_nonneg I N)] at hlow
  nlinarith

theorem flat_all_gamma (p : ℝ≥0∞) (hp : 1 ≤ p) (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N)
    {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    additiveRisk p (InexactRealizations.Flat.history I N hN) I r t =
      I.epsilon N * r + t * (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.additiveScale I N := by
  let : p.HolderConjugate (dualExponent p) := holder_dualExponent p hp
  exact flat_all_budgets (p := p) (q := dualExponent p) I hN hr ht

end
end InexactRealizations.Budgets
