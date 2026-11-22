import InexactRealizations.Budgets.Exponents
import InexactRealizations.History.Execution
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-! Actual additive executions realize the directional Holder support
formula in AppendixA, for every call budget exponent. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial
open scoped BigOperators ENNReal NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem polynomial_symmetric (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (p : ℝ[X]) :
    (aeval H p).IsSymmetric := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial n c =>
    rw [aeval_monomial, ← Algebra.smul_def]
    exact (hH.pow n).smul (by simp)

def unitDirection (z e : E) : E := by
  classical
  exact if z = 0 then e else ‖z‖⁻¹ • z

theorem unitDirection_norm (z e : E) (he : ‖e‖ = 1) : ‖unitDirection z e‖ = 1 := by
  by_cases hz : z = 0
  · simpa only [unitDirection, hz, ite_true] using he
  · simp only [unitDirection, hz, ite_false, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg z)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)

theorem inner_unitDirection (z e : E) : inner ℝ z (unitDirection z e) = ‖z‖ := by
  by_cases hz : z = 0
  · simp only [hz, inner_zero_left, norm_zero]
  · simp only [unitDirection, hz, ite_false, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp [(norm_ne_zero_iff.mpr hz)]

variable {N : ℕ} {p q : ℝ≥0∞} [p.HolderConjugate q]

set_option maxHeartbeats 1000000 in
theorem additive_support_upper (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise) (e : E)
    {r t : ℝ} (ht : 0 ≤ t) (hi : ‖initial‖ ≤ r) (delta : Fin N → ℝ) (hd : Budget p delta)
    (hw : ∀ s, ‖noise s‖ ≤ t * delta s) :
    inner ℝ e u.output ≤ r * ‖(aeval H h.terminal) e‖ +
      t * callNorm q (fun s ↦ ‖(aeval H (h.response s)) e‖) := by
  rw [h.physical_response H initial noise u, inner_add_right, inner_sum]
  have hterm : inner ℝ e ((aeval H h.terminal) initial) ≤ r * ‖(aeval H h.terminal) e‖ := by
    rw [← polynomial_symmetric H hH h.terminal e initial]
    have hh := real_inner_le_norm ((aeval H h.terminal) e) initial
    nlinarith [mul_le_mul_of_nonneg_left hi (norm_nonneg ((aeval H h.terminal) e))]
  have hsum : (∑ s, inner ℝ e ((aeval H (h.response s)) (noise s))) ≤
      t * callNorm q (fun s ↦ ‖(aeval H (h.response s)) e‖) := by
    have hp (s : Fin N) : inner ℝ e ((aeval H (h.response s)) (noise s)) ≤
        t * (delta s * ‖(aeval H (h.response s)) e‖) := by
      rw [← polynomial_symmetric H hH (h.response s) e (noise s)]
      exact (real_inner_le_norm _ _).trans (by
        have hh := mul_le_mul_of_nonneg_left (hw s) (norm_nonneg ((aeval H (h.response s)) e))
        nlinarith)
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ ↦ hp s)
    rw [← Finset.mul_sum] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (holder_budget _ delta (fun s ↦ norm_nonneg _) hd) ht)
  linarith

set_option maxHeartbeats 1000000 in
theorem additive_support_attained [Nonempty (Fin N)] (h : InexactRealizations.History N)
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (e : E) (he : ‖e‖ = 1)
    {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t) :
    ∃ (initial : E) (noise : Fin N → E) (delta : Fin N → ℝ),
      ‖initial‖ ≤ r ∧ Budget p delta ∧ (∀ s, ‖noise s‖ ≤ t * delta s) ∧
      inner ℝ e (h.run H initial noise).output =
        r * ‖(aeval H h.terminal) e‖ + t * callNorm q (fun s ↦ ‖(aeval H (h.response s)) e‖) := by
  obtain ⟨delta, hd, hdelta⟩ := exists_holder_budget (p := p) (q := q)
    (fun s : Fin N ↦ ‖(aeval H (h.response s)) e‖) (fun _ ↦ norm_nonneg _)
  let initial := r • unitDirection ((aeval H h.terminal) e) e
  let noise := fun s : Fin N ↦ (t * delta s) • unitDirection ((aeval H (h.response s)) e) e
  refine ⟨initial, noise, delta, ?_, hd, ?_, ?_⟩
  · simp only [initial, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, unitDirection_norm _ _ he, mul_one, le_refl]
  · intro s
    simp only [noise, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht (hd.1 s)),
      unitDirection_norm _ _ he, mul_one, le_refl]
  · rw [h.physical_response H initial noise (h.run H initial noise), inner_add_right, inner_sum]
    have hterm : inner ℝ e ((aeval H h.terminal) initial) = r * ‖(aeval H h.terminal) e‖ := by
      rw [← polynomial_symmetric H hH h.terminal e initial]
      simp only [initial, inner_smul_right, inner_unitDirection]
    have hresponse (s : Fin N) : inner ℝ e ((aeval H (h.response s)) (noise s)) =
        t * (delta s * ‖(aeval H (h.response s)) e‖) := by
      rw [← polynomial_symmetric H hH (h.response s) e (noise s)]
      simp only [noise, inner_smul_right, inner_unitDirection]
      ring
    simp_rw [hterm, hresponse]
    rw [← Finset.mul_sum, hdelta]

end
end InexactRealizations.Budgets
