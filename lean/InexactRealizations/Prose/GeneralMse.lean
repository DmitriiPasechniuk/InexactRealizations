import InexactRealizations.Prose.RawMoments
import InexactRealizations.Risk.AllLinearLower

/-! Actual MSE bounds for arbitrary terminals, needed for the tail-averaged
Prefix assertion. The risk continues to be the literal raw-model supremum. 
-/
namespace InexactRealizations.Prose
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators
variable {N : ℕ}

theorem general_mse_upper (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (P : Fin N → ℝ) (hP : InexactRealizations.Risk.ResponseBounds h I P) (c : ℝ) (hc : 0 ≤ c)
    (hp : ∀ x ∈ Set.Icc I.mu I.L, |h.terminal.eval x| ≤ c)
    (r σ : ℝ) (hr : 0 ≤ r) : InexactRealizations.Risk.mseRisk h I r σ ≤ c ^ 2 * r ^ 2 + σ ^ 2 * ∑ s, P s ^ 2 := by
  have hbelow : BddBelow {C : ℝ | InexactRealizations.Risk.MseBound h I r σ C} :=
    ⟨0, fun C hC ↦ InexactRealizations.Risk.AllLinear.mseBounds_nonneg h I hr hC⟩
  apply csInf_le hbelow
  intro E Ω _ _ _ _ _ μ _ 𝓕 w hw hσ H hH initial hi
  have hn := (InexactRealizations.Analysis.polynomial_action_bound I H hH _ c hc hp initial).trans
    (mul_le_mul_of_nonneg_left hi hc)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc hr)).mpr hn
  rw [mul_pow] at hs
  have hop : (∑ s, ‖h.responseOperator H s‖ ^ 2) ≤ ∑ s, P s ^ 2 := by
    apply Finset.sum_le_sum
    intro s _
    exact (sq_le_sq₀ (norm_nonneg _) (hP.1 s)).mpr
      (InexactRealizations.Analysis.polynomial_operator_bound I H hH _ _ (hP.1 s) (hP.2 s))
  exact (h.integral_stochasticOutput_norm_sq_le H initial hw σ hσ).trans
    (add_le_add hs (mul_le_mul_of_nonneg_left hop (sq_nonneg σ)))

theorem general_mse_endpoint_lower (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (r σ : ℝ) (hr : 0 ≤ r) : r ^ 2 * h.terminal.eval I.mu ^ 2 +
      σ ^ 2 * ∑ s, (h.response s).eval I.mu ^ 2 ≤ InexactRealizations.Risk.mseRisk h I r σ := by
  apply le_csInf (InexactRealizations.Risk.AllLinear.allMseBounds_nonempty h I r σ hr)
  intro C hC
  exact InexactRealizations.Risk.AllLinear.mseBound_twoMode_lower h I hr hC ⟨le_rfl, I.mu_lt_L.le⟩

end
end InexactRealizations.Prose
