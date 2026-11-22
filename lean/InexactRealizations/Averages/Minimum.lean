import InexactRealizations.Averages.Measure
import InexactRealizations.Centered.RMS
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! For every spectral probability measure, including measures with finite
support and degenerate moment matrices, the stated Christoffel minimum is
attained. This uses only finite-dimensional least squares in the actual L2. 
-/
namespace InexactRealizations.Averages.SpectralLaw
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory
open scoped BigOperators
variable {I : InexactRealizations.Operators.SpectralInterval} (ρ : SpectralLaw I)

theorem polynomial_memLp (p : ℝ[X]) : MemLp (fun x ↦ p.eval x) 2 ρ.measure := by
  apply (memLp_two_iff_integrable_sq_norm p.continuous.aestronglyMeasurable).mpr
  have hi : Integrable (fun x ↦ p.eval x ^ 2) ρ.measure := ρ.continuous_integrable (by fun_prop)
  simpa only [Real.norm_eq_abs, sq_abs] using hi

def polynomialLp : ℝ[X] →ₗ[ℝ] Lp ℝ 2 ρ.measure where
  toFun p := (ρ.polynomial_memLp p).toLp (fun x ↦ p.eval x)
  map_add' p q := by
    apply Lp.ext
    filter_upwards [(ρ.polynomial_memLp (p + q)).coeFn_toLp,
      Lp.coeFn_add ((ρ.polynomial_memLp p).toLp _) ((ρ.polynomial_memLp q).toLp _),
      (ρ.polynomial_memLp p).coeFn_toLp, (ρ.polynomial_memLp q).coeFn_toLp] with x h₁ h₂ h₃ h₄
    rw [h₁, h₂]
    simp only [h₃, h₄, eval_add, Pi.add_apply]
  map_smul' c p := by
    apply Lp.ext
    filter_upwards [(ρ.polynomial_memLp (c • p)).coeFn_toLp,
      Lp.coeFn_smul c ((ρ.polynomial_memLp p).toLp _),
      (ρ.polynomial_memLp p).coeFn_toLp] with x h₁ h₂ h₃
    simp only [RingHom.id_apply]
    rw [h₁, h₂]
    simp only [h₃, eval_smul, Pi.smul_apply]

theorem polynomialLp_norm_sq (p : ℝ[X]) : ‖ρ.polynomialLp p‖ ^ 2 = ρ.energy p := by
  change ‖(ρ.polynomial_memLp p).toLp (fun x ↦ p.eval x)‖ ^ 2 = ρ.energy p
  simpa only [energy, Real.norm_eq_abs, sq_abs] using
    InexactRealizations.Centered.l2_norm_sq (ρ.polynomial_memLp p)

set_option maxHeartbeats 800000 in
theorem exists_christoffel_minimizer (k : ℕ) :
    ∃ p : ℝ[X], p.natDegree ≤ k ∧ p.eval I.mu = 1 ∧ ρ.energy p = ρ.christoffel k := by
  let V := degreeLT ℝ (k + 1)
  let ev : V →ₗ[ℝ] ℝ := (aeval I.mu).toLinearMap.comp V.subtype
  let W := ev.ker
  let L : W →ₗ[ℝ] Lp ℝ 2 ρ.measure := (ρ.polynomialLp.comp V.subtype).comp W.subtype
  let M := L.range
  let : FiniteDimensional ℝ V := FiniteDimensional.of_injective
    (degreeLTEquiv ℝ (k + 1)).toLinearMap (degreeLTEquiv ℝ (k + 1)).injective
  have hclosed : IsClosed (M : Set (Lp ℝ 2 ρ.measure)) := M.closed_of_finiteDimensional
  obtain ⟨v, hv, hmin⟩ := M.exists_norm_eq_iInf_of_complete_subspace hclosed.isComplete (-ρ.polynomialLp 1)
  obtain ⟨q, hq⟩ := hv
  let p : ℝ[X] := 1 + q.val.val
  have hdeg : p.natDegree ≤ k := by
    have hqdeg := mem_degreeLT.mp q.val.property
    have hqle : q.val.val.natDegree ≤ k := by
      by_cases hz : q.val.val = 0
      · simp only [hz, natDegree_zero, Nat.zero_le]
      · exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hz).mpr hqdeg)
    exact (natDegree_add_le _ _).trans (max_le (by simp) hqle)

  have heval : p.eval I.mu = 1 := by
    have heq : q.val.val.eval I.mu = 0 := q.property
    simp only [p, eval_add, eval_one, heq, add_zero]
  have hbest (a : ℝ[X]) (ha : a.natDegree ≤ k) (hae : a.eval I.mu = 1) : ρ.energy p ≤ ρ.energy a := by
    let b : V := ⟨a - 1, mem_degreeLT.mpr ((degree_sub_le _ _).trans_lt
      (max_lt (degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le ha)) (by rw [degree_one]; exact WithBot.coe_lt_coe.mpr (Nat.zero_lt_succ k))))⟩
    have hb : b ∈ W := by
      change (a - 1).eval I.mu = 0
      simp only [eval_sub, eval_one, hae, sub_self]
    have hu : L ⟨b, hb⟩ ∈ M := ⟨⟨b, hb⟩, rfl⟩
    have hn : ‖-ρ.polynomialLp 1 - v‖ ≤ ‖-ρ.polynomialLp 1 - L ⟨b, hb⟩‖ := by
      rw [hmin]
      have hbdd : BddBelow (Set.range (fun z : (M : Set (Lp ℝ 2 ρ.measure)) ↦ ‖-ρ.polynomialLp 1 - z.val‖)) :=
        ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩
      exact ciInf_le hbdd ⟨L ⟨b, hb⟩, hu⟩
    have hl : ρ.polynomialLp p = ρ.polynomialLp 1 + v := by
      change ρ.polynomialLp (1 + q.val.val) = _
      rw [map_add]
      exact congrArg (fun z ↦ ρ.polynomialLp 1 + z) hq
    have hr : -ρ.polynomialLp 1 - L ⟨b, hb⟩ = -ρ.polynomialLp a := by
      change -ρ.polynomialLp 1 - ρ.polynomialLp (a - 1) = _
      rw [map_sub]
      abel
    have hn' : ‖ρ.polynomialLp p‖ ≤ ‖ρ.polynomialLp a‖ := by
      rw [hr, norm_neg, show -ρ.polynomialLp 1 - v = -(ρ.polynomialLp 1 + v) by abel, norm_neg, ← hl] at hn
      exact hn
    have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn'
    simpa only [polynomialLp_norm_sq] using hs
  refine ⟨p, hdeg, heval, le_antisymm ?_ (ρ.christoffel_le k p hdeg heval)⟩
  apply le_csInf (ρ.christoffelValues_nonempty k)
  rintro _ ⟨a, ha, hae, rfl⟩
  exact hbest a ha hae

end
end InexactRealizations.Averages.SpectralLaw
