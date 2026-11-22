import InexactRealizations.Budgets.Support
import InexactRealizations.Budgets.Corners
import InexactRealizations.Risk.Bounds

/-! The literal additive worst-case supremum with every lp call budget.
Its upper bound and scalar endpoint lower bound quantify actual executions. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial
open scoped BigOperators ENNReal NNReal
variable {N : ℕ}

inductive AdditiveValue (p : ℝ≥0∞) (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r t : ℝ) : ℝ → Prop where
  | execution (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (initial : E) (noise : Fin N → E)
      (u : h.Execution H initial noise) (delta : Fin N → ℝ) (hi : ‖initial‖ ≤ r)
      (hd : Budget p delta) (hw : ∀ s, ‖noise s‖ ≤ t * delta s) : AdditiveValue p h I r t ‖u.output‖

def additiveValues (p : ℝ≥0∞) (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r t : ℝ) : Set ℝ :=
  {v | AdditiveValue p h I r t v}
def additiveRisk (p : ℝ≥0∞) (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (r t : ℝ) : ℝ :=
  sSup (additiveValues p h I r t)

variable {p q : ℝ≥0∞} [p.HolderConjugate q]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem additive_upper (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (he : h.ChebyshevExact I)
    (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (P : Fin N → ℝ)
    (hP : InexactRealizations.Risk.ResponseBounds h I P) (initial : E) (noise : Fin N → E)
    (u : h.Execution H initial noise) {r t : ℝ} (ht : 0 ≤ t) (hi : ‖initial‖ ≤ r)
    (delta : Fin N → ℝ) (hd : Budget p delta) (hw : ∀ s, ‖noise s‖ ≤ t * delta s) :
    ‖u.output‖ ≤ I.epsilon N * r + t * callNorm q P := by
  rw [h.physical_response H initial noise u]
  have hb : ‖(aeval H h.terminal) initial‖ ≤ I.epsilon N * r := by
    rw [he]
    exact (InexactRealizations.Analysis.residual_action_bound I H hH N initial).trans
      (mul_le_mul_of_nonneg_left hi (one_div_pos.mpr (I.den_pos N)).le)
  have hsum : ‖∑ s, (aeval H (h.response s)) (noise s)‖ ≤ t * callNorm q P := by
    have hh := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun s _ ↦
      (InexactRealizations.Analysis.polynomial_action_bound I H hH (h.response s) (P s) (hP.1 s) (hP.2 s) (noise s)).trans
        (mul_le_mul_of_nonneg_left (hw s) (hP.1 s))))
    have hscaled : (∑ s, P s * (t * delta s)) = t * ∑ s, delta s * P s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [hscaled] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (holder_budget P delta hP.1 hd) ht)
  exact (norm_add_le _ _).trans (add_le_add hb hsum)

include q in
theorem additiveValues_nonempty (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    {r t : ℝ} (hr : 0 ≤ r) : (additiveValues p h I r t).Nonempty := by
  let : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  let H := InexactRealizations.History.scalarOperator I.mu
  let u := h.run H 0 (fun _ ↦ 0)
  refine ⟨‖u.output‖, AdditiveValue.execution ℝ H
    (InexactRealizations.Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩) 0 (fun _ ↦ 0) u (fun _ ↦ 0)
    (by simpa only [norm_zero] using hr) ⟨fun _ ↦ le_rfl, ?_⟩ (by intro s; simp)⟩
  change ‖(0 : PiLp p (fun _ : Fin N ↦ ℝ))‖ ≤ 1
  simp

include q in
theorem additiveValues_bddAbove (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) {r t : ℝ} (ht : 0 ≤ t) : BddAbove (additiveValues p h I r t) := by
  classical
  choose P hP0 hP using fun s : Fin N ↦ InexactRealizations.Analysis.exists_polynomial_bound I (h.response s)
  refine ⟨I.epsilon N * r + t * callNorm q P, ?_⟩
  intro v hv
  cases hv with
  | execution E H hH initial noise u delta hi hd hw =>
    exact additive_upper h I he H hH P ⟨hP0, hP⟩ initial noise u ht hi delta hd hw

theorem additiveRisk_upper (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (he : h.ChebyshevExact I)
    (P : Fin N → ℝ) (hP : InexactRealizations.Risk.ResponseBounds h I P) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    additiveRisk p h I r t ≤ I.epsilon N * r + t * callNorm q P := by
  apply csSup_le (additiveValues_nonempty (p := p) (q := q) h I hr)
  intro v hv
  cases hv with
  | execution E H hH initial noise u delta hi hd hw =>
    exact additive_upper h I he H hH P hP initial noise u ht hi delta hd hw

set_option maxHeartbeats 1000000 in
theorem additiveRisk_endpoint_lower (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (he : h.ChebyshevExact I) (hN : 0 < N) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    I.epsilon N * r + t * callNorm q (fun s : Fin N ↦ (h.response s).eval I.mu) ≤ additiveRisk p h I r t := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let H := InexactRealizations.History.scalarOperator I.mu
  have hH := InexactRealizations.Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩
  obtain ⟨initial, noise, delta, hi, hd, hw, hs⟩ := additive_support_attained (p := p) (q := q)
    h H hH.1 (1 : ℝ) (by norm_num) hr ht
  have hv : ‖(h.run H initial noise).output‖ ∈ additiveValues p h I r t :=
    AdditiveValue.execution ℝ H hH initial noise (h.run H initial noise) delta hi hd hw
  have hsup := le_csSup (additiveValues_bddAbove (p := p) (q := q) h I he ht) hv
  have hinner := real_inner_le_norm (1 : ℝ) (h.run H initial noise).output
  rw [hs] at hinner
  have hterm : ‖(aeval H h.terminal) (1 : ℝ)‖ = I.epsilon N := by
    rw [InexactRealizations.History.scalarOperator_polynomial_action, he, I.residual_eval_mu]
    simp only [mul_one, Real.norm_eq_abs]
    exact abs_of_pos (one_div_pos.mpr (I.den_pos N))
  have hprofile : callNorm q (fun s ↦ ‖(aeval H (h.response s)) (1 : ℝ)‖) =
      callNorm q (fun s : Fin N ↦ (h.response s).eval I.mu) := by
    simp only [H, InexactRealizations.History.scalarOperator_polynomial_action, mul_one, Real.norm_eq_abs]
    exact callNorm_abs _
  rw [hterm, hprofile, norm_one, one_mul] at hinner
  unfold additiveRisk
  nlinarith

end
end InexactRealizations.Budgets
