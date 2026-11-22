import InexactRealizations.Budgets.Relative
import InexactRealizations.Budgets.Corners

/-! The actual-query relative response has a uniform quadratic remainder
for every lp budget, not only the energy exponent. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial InexactRealizations.Analysis
open scoped BigOperators ENNReal NNReal
variable {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem relative_response_bound (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : Admissible I H) (initial : E) (noise : Fin N → E)
    (u : h.Execution H initial noise) (r t t0 : ℝ) (hr : 0 ≤ r)
    (ht : 0 ≤ t) (htt0 : t ≤ t0) (hi : ‖initial‖ ≤ r) (δ : Fin N → ℝ)
    (hw : RelativeErrors p h H initial noise u t δ) (P Q : Fin N → ℝ)
    (hP : Risk.ResponseBounds h I P) (hQ : ∀ s, 0 ≤ Q s)
    (hq : ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s) :
    ‖u.output - (aeval H h.terminal) initial‖ ≤
      t * r * callNorm q (fun s => P s * Q s) +
      t ^ 2 * r * callNorm q (fun s => P s * deviationMajorant h I.L t0 s) := by
  let : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  let d : Fin N → ℝ := deviationMajorant h I.L t0
  have hd := query_deviation_bound h I H hH initial noise u r t t0 hr ht htt0 hi δ hw
  have hn (s : Fin N) : ‖(aeval H (h.query s)) initial‖ ≤ r * Q s := by
    calc
      _ ≤ Q s * ‖initial‖ := polynomial_action_bound I H hH _ _ (hQ s) (hq s) initial
      _ ≤ Q s * r := mul_le_mul_of_nonneg_left hi (hQ s)
      _ = _ := mul_comm _ _
  have ha (s : Fin N) : ‖u.query s‖ ≤ r * Q s + t * r * d s := by
    calc
      _ = ‖(aeval H (h.query s)) initial +
          (u.query s - (aeval H (h.query s)) initial)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (hn s) (hd s))
  have hw' (s : Fin N) : ‖noise s‖ ≤
      t * r * (Q s * δ s) + t ^ 2 * r * (d s * δ s) := by
    calc
      _ ≤ t * δ s * ‖u.query s‖ := hw.2.2 s
      _ ≤ t * δ s * (r * Q s + t * r * d s) :=
        mul_le_mul_of_nonneg_left (ha s) (mul_nonneg ht (hw.1 s))
      _ = _ := by ring
  rw [h.physical_response H initial noise u, add_sub_cancel_left]
  calc
    _ ≤ ∑ s, P s * ‖noise s‖ := norm_sum_le_energy _ _ (fun s =>
      polynomial_action_bound I H hH _ _ (hP.1 s) (hP.2 s) _)
    _ ≤ ∑ s, P s * (t * r * (Q s * δ s) + t ^ 2 * r * (d s * δ s)) :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hw' s) (hP.1 s)
    _ = t * r * (∑ s, (P s * Q s) * δ s) +
        t ^ 2 * r * (∑ s, (P s * d s) * δ s) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ _ := by
      have hdnonneg : ∀ s, 0 ≤ d s := deviationMajorant_nonneg h
        (lt_trans I.mu_pos I.mu_lt_L).le (ht.trans htt0)
      have h₁ := holder_budget (p := p) (q := q) (fun s => P s * Q s) δ
        (fun s => mul_nonneg (hP.1 s) (hQ s)) (show Budget p δ from ⟨hw.1, hw.2.1⟩)
      have h₂ := holder_budget (p := p) (q := q) (fun s => P s * d s) δ
        (fun s => mul_nonneg (hP.1 s) (hdnonneg s)) (show Budget p δ from ⟨hw.1, hw.2.1⟩)
      simp_rw [mul_comm (δ _)] at h₁ h₂
      exact add_le_add (mul_le_mul_of_nonneg_left h₁ (mul_nonneg ht hr))
        (mul_le_mul_of_nonneg_left h₂ (mul_nonneg (sq_nonneg t) hr))

end
end InexactRealizations.Budgets
