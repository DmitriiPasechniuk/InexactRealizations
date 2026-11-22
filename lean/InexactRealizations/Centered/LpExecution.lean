import InexactRealizations.Centered.RMS
import InexactRealizations.Centered.Queries
import InexactRealizations.Centered.Envelope
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! The L2 states are the equivalence classes of the actual random queries
and answers. The causal execution equations hold exactly in L2. 
-/
namespace InexactRealizations.Centered
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial MeasureTheory Filter
open scoped BigOperators ENNReal NNReal
variable {N : ℕ} {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}

def liftedH (H : E →ₗ[ℝ] E) : Lp E 2 μ →ₗ[ℝ] Lp E 2 μ :=
  (H.toContinuousLinearMap.compLpL 2 μ).toLinearMap

theorem liftedH_const (H : E →ₗ[ℝ] E) (v : E) :
    liftedH (μ := μ) H (Lp.const 2 μ v) = Lp.const 2 μ (H v) := by
  exact (toLp_linearMap H.toContinuousLinearMap (memLp_const (μ := μ) (p := 2) v)).symm

theorem lifted_polynomial_const (H : E →ₗ[ℝ] E) (p : ℝ[X]) (v : E) :
    (aeval (liftedH (μ := μ) H) p) (Lp.const 2 μ v) = Lp.const 2 μ ((aeval H p) v) := by
  let C := Lp.constₗ 2 μ ℝ (E := E)
  have hconst (x : E) : liftedH (μ := μ) H (C x) = C (H x) := liftedH_const H x
  have hp (n : ℕ) (x : E) : (liftedH (μ := μ) H ^ n) (C x) = C ((H ^ n) x) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, hconst, ← Module.End.mul_apply, ← pow_succ']
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp only [map_add, LinearMap.add_apply, ihp, ihq]
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    change c • (liftedH (μ := μ) H ^ n) (C v) = C (c • (H ^ n) v)
    rw [hp, C.map_smul]

def randomAnswer (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (w : ℕ → Ω → E) (s : Fin N) (ω : Ω) : E :=
  (h.run H initial (fun j ↦ w j.val ω)).answer s

omit [CompleteSpace E] in
theorem randomAnswer_memLp (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ) (s : Fin N) :
    MemLp (randomAnswer h H initial w s) 2 μ := by
  have hh : randomAnswer h H initial w s =
      (fun ω ↦ H (randomQuery h H initial w s ω)) + w s.val := by
    funext ω
    exact (h.run H initial (fun j ↦ w j.val ω)).answer_eq s
  rw [hh]
  exact ((randomQuery_memLp h H initial hw s).continuousLinearMap_comp H.toContinuousLinearMap).add
    (hw.squareIntegrable s.val s.isLt)

def lpExecution (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ) :
    h.Execution (liftedH H) (Lp.const 2 μ initial)
      (fun j : Fin N ↦ (hw.squareIntegrable j.val j.isLt).toLp (w j.val)) where
  query s := (randomQuery_memLp h H initial hw s).toLp (randomQuery h H initial w s)
  answer s := (randomAnswer_memLp h H initial hw s).toLp (randomAnswer h H initial w s)
  query_eq s := by
    let f := fun j : Fin N ↦ h.a s j • randomAnswer h H initial w j
    have hf (j : Fin N) : MemLp (f j) 2 μ := (randomAnswer_memLp h H initial hw j).const_smul _
    have hsum := toLp_sum Finset.univ f hf
    have he : randomQuery h H initial w s = (fun _ : Ω ↦ initial) - (fun ω ↦ ∑ j, f j ω) := by
      funext ω
      exact (h.run H initial (fun j ↦ w j.val ω)).query_eq s
    calc
      _ = ((memLp_const (μ := μ) (p := 2) initial).sub (memLp_finsetSum Finset.univ (fun j _ ↦ hf j))).toLp
          ((fun _ : Ω ↦ initial) - (fun ω ↦ ∑ j, f j ω)) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall (congrFun he))
      _ = _ := by
        rw [MemLp.toLp_sub (memLp_const (μ := μ) (p := 2) initial)
          (memLp_finsetSum Finset.univ (fun j _ ↦ hf j)), hsum]
        congr 1
  answer_eq s := by
    have hq := randomQuery_memLp h H initial hw s
    have hnoise := hw.squareIntegrable s.val s.isLt
    have he : randomAnswer h H initial w s = (fun ω ↦ H (randomQuery h H initial w s ω)) + w s.val := by
      funext ω
      exact (h.run H initial (fun j ↦ w j.val ω)).answer_eq s
    calc
      _ = ((hq.continuousLinearMap_comp H.toContinuousLinearMap).add hnoise).toLp
          ((fun ω ↦ H.toContinuousLinearMap (randomQuery h H initial w s ω)) + w s.val) :=
        MemLp.toLp_congr _ _ (Eventually.of_forall (congrFun he))
      _ = _ := by
        rw [MemLp.toLp_add (hq.continuousLinearMap_comp H.toContinuousLinearMap) hnoise]
        exact congrArg (fun v ↦ v + hnoise.toLp (w s.val)) (toLp_linearMap H.toContinuousLinearMap hq)

end
end InexactRealizations.Centered
