import InexactRealizations.Probability.History

/-! Actual noisy queries are deterministic linear responses of the preceding
martingale errors. This gives their square integrability and exact bias/
variance split without independence assumptions. 
-/
namespace InexactRealizations.Centered
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators
variable {N : ℕ}

def queryHistory (h : InexactRealizations.History N) (s : Fin N) : InexactRealizations.History N where
  a := h.a
  b := h.a s
  triangular := h.triangular

section Deterministic
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def queryExecution (h : InexactRealizations.History N) (s : Fin N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise) :
    (queryHistory h s).Execution H initial noise where
  query := u.query
  answer := u.answer
  query_eq := u.query_eq
  answer_eq := u.answer_eq

theorem queryExecution_output (h : InexactRealizations.History N) (s : Fin N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise) :
    (queryExecution h s H initial noise u).output = u.query s := (u.query_eq s).symm

theorem queryHistory_nominal (h : InexactRealizations.History N) (s : Fin N) (H : E →ₗ[ℝ] E) (initial : E) :
    (aeval H (queryHistory h s).terminal) initial = (aeval H (h.query s)) initial := by
  let u := h.run H initial (fun _ ↦ 0)
  rw [← (queryHistory h s).nominal_output H initial (queryExecution h s H initial (fun _ ↦ 0) u),
    queryExecution_output, h.nominal_query H initial u]

theorem query_response (h : InexactRealizations.History N) (s : Fin N) (H : E →ₗ[ℝ] E)
    (initial : E) (noise : Fin N → E) (u : h.Execution H initial noise) :
    u.query s = (aeval H (h.query s)) initial +
      ∑ j, (aeval H ((queryHistory h s).response j)) (noise j) := by
  rw [← queryExecution_output h s H initial noise u,
    (queryHistory h s).physical_response H initial noise (queryExecution h s H initial noise u),
    queryHistory_nominal]

end Deterministic

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}

def randomQuery (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (w : ℕ → Ω → E) (s : Fin N) (ω : Ω) : E :=
  (h.run H initial (fun j ↦ w j.val ω)).query s

def queryResponse (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (s j : Fin N) : E →L[ℝ] E :=
  (aeval H ((queryHistory h s).response j)).toContinuousLinearMap

omit mΩ [CompleteSpace E] in
theorem randomQuery_response (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (w : ℕ → Ω → E) (s : Fin N) (ω : Ω) :
    randomQuery h H initial w s ω = (aeval H (h.query s)) initial +
      ∑ j : Fin N, queryResponse h H s j (w j.val ω) :=
  query_response h s H initial _ _

omit [CompleteSpace E] in
theorem randomQuery_memLp (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ) (s : Fin N) :
    MemLp (randomQuery h H initial w s) 2 μ := by
  have hh : (randomQuery h H initial w s) = (fun _ : Ω ↦ (aeval H (h.query s)) initial) +
      (fun ω ↦ ∑ j : Fin N, queryResponse h H s j (w j.val ω)) := by
    funext ω
    exact randomQuery_response h H initial w s ω
  rw [hh]
  exact (memLp_const (μ := μ) (p := 2) ((aeval H (h.query s)) initial)).add
    (memLp_finsetSum Finset.univ (fun j _ ↦
    (hw.squareIntegrable j.val j.isLt).continuousLinearMap_comp (queryResponse h H s j)))

theorem randomQuery_second_moment (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ) (s : Fin N) :
    (∫ ω, ‖randomQuery h H initial w s ω‖ ^ 2 ∂μ) = ‖(aeval H (h.query s)) initial‖ ^ 2 +
      ∫ ω, ‖randomQuery h H initial w s ω - (aeval H (h.query s)) initial‖ ^ 2 ∂μ := by
  simp_rw [randomQuery_response, add_sub_cancel_left]
  have hh := hw.integral_norm_sq_finite_response ((aeval H (h.query s)) initial) (queryResponse h H s)
  have hz := hw.integral_norm_sq_finite_response (0 : E) (queryResponse h H s)
  simp only [zero_add, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hz
  rw [hz]
  exact hh

end
end InexactRealizations.Centered
