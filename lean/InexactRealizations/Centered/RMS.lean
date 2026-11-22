import InexactRealizations.Probability.History
import Mathlib.MeasureTheory.Function.L2Space

namespace InexactRealizations.Centered
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem l2_norm_sq {f : Ω → E} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with ω hω
  rw [hω, real_inner_self_eq_norm_sq]

theorem l2_const_norm [IsProbabilityMeasure μ] (v : E) :
    ‖(memLp_const (μ := μ) (p := 2) v).toLp (fun _ : Ω ↦ v)‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [l2_norm_sq]
  simp

omit [InnerProductSpace ℝ E] in
theorem toLp_sum {J : Type*} (S : Finset J) (f : J → Ω → E) (hf : ∀ i, MemLp (f i) 2 μ) :
    (memLp_finsetSum S (fun i _ ↦ hf i)).toLp (fun ω ↦ ∑ i ∈ S, f i ω) = ∑ i ∈ S, (hf i).toLp (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rfl
  | @insert i S hi ih =>
    have hS := memLp_finsetSum S (fun j (_ : j ∈ S) ↦ hf j)
    calc
      _ = ((hf i).add hS).toLp (f i + (fun ω ↦ ∑ j ∈ S, f j ω)) := by
        apply MemLp.toLp_congr
        exact Eventually.of_forall (fun ω ↦ by simp only [Finset.sum_insert hi, Pi.add_apply])
      _ = (hf i).toLp (f i) + hS.toLp (fun ω ↦ ∑ j ∈ S, f j ω) := MemLp.toLp_add (hf i) hS
      _ = (hf i).toLp (f i) + ∑ j ∈ S, (hf j).toLp (f j) := by rw [ih]
      _ = _ := (Finset.sum_insert hi).symm

theorem toLp_linearMap [CompleteSpace E] (L : E →L[ℝ] E) {f : Ω → E} (hf : MemLp f 2 μ) :
    (hf.continuousLinearMap_comp L).toLp (fun ω ↦ L (f ω)) = L.compLpL 2 μ (hf.toLp f) := by
  apply Lp.ext
  filter_upwards [(hf.continuousLinearMap_comp L).coeFn_toLp, L.coeFn_compLpL (hf.toLp f), hf.coeFn_toLp]
    with ω h₁ h₂ h₃
  rw [h₁, h₂, h₃]

theorem l2_relative_bound [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {w y : Ω → E} (hw : MemLp w 2 μ) (hy : MemLp y 2 μ) (t : ℝ) (ht : 0 ≤ t)
    (hcond : μ[fun ω ↦ ‖w ω‖ ^ 2 | m] ≤ᵐ[μ] fun ω ↦ t ^ 2 * ‖y ω‖ ^ 2) :
    ‖hw.toLp w‖ ≤ t * ‖hy.toLp y‖ := by
  have hb := integral_mono_ae integrable_condExp
    ((hy.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul (t ^ 2)) hcond
  rw [integral_condExp hm, integral_const_mul] at hb
  rw [← l2_norm_sq (mΩ := mΩ) hw, ← l2_norm_sq (mΩ := mΩ) hy] at hb
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht (norm_nonneg _))).mp
    (by simpa only [mul_pow] using hb)

end
end InexactRealizations.Centered
