import InexactRealizations.Risk.AdaptiveModels

/-! The Gaussian execution is an actual admissible member of the risk
class; the desired minimax lower bound is never supplied as a hypothesis. 
-/
namespace InexactRealizations.Risk.Adaptive
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open InexactRealizations.Probability
open InexactRealizations.Probability.Gaussian
variable {N : ℕ} {U : Type} [MeasurableSpace U]

theorem gaussian_model_value (M : AdaptiveMethod N ℝ U) (P : Measure U) [IsProbabilityMeasure P]
    (I : InexactRealizations.Operators.SpectralInterval) (r sigma : ℝ) :
    ScalarMseValue M P I r sigma
      (∫⁻ p : U × Sample N, ENNReal.ofReal ((r * p.2 none - gaussianOutput M I.mu r sigma p) ^ 2)
        ∂P.prod (stdGaussian (Sample N))) := by
  have hnoise (p : U × Sample N) :
      (fun i : Fin N ↦ fun q ↦ I.mu * (q - r * p.2 none) + noise N sigma i.val p.2) =
        physicalOracle I.mu r sigma p.2 := by
    funext i q
    simp only [noise, i.isLt, dite_true, physicalOracle]
  have ho : actualOutput M Prod.fst (fun p : U × Sample N ↦ r * p.2 none) I.mu
      (fun s p ↦ noise N sigma s p.2) = gaussianOutput M I.mu r sigma := by
    funext p
    unfold actualOutput gaussianOutput
    rw [hnoise]
  have htarget : Measurable (fun x : Sample N ↦ r * x none) := by fun_prop
  have hindep : IndepFun (Prod.fst : U × Sample N → U) (fun p ↦ r * p.2 none)
      (P.prod (stdGaussian (Sample N))) := indepFun_prod measurable_id htarget
  have hmem : MemLp (fun p : U × Sample N ↦ r * p.2 none) 2 (P.prod (stdGaussian (Sample N))) := by
    have hh : MemLp ((fun x : Sample N ↦ inner ℝ (hiddenVector N r) x) ∘ Prod.snd) 2
        (P.prod (stdGaussian (Sample N))) :=
      (linear_memLp (hiddenVector N r)).comp_measurePreserving measurePreserving_snd
    simp_rw [Function.comp_def, hidden_inner] at hh
    exact hh
  rw [← ho]
  apply ScalarMseValue.model (U × Sample N) (P.prod (stdGaussian (Sample N)))
    (seededPast U N r sigma) Prod.fst (seed_measurable N r sigma 0)
    measurePreserving_fst.map_eq (fun p ↦ r * p.2 none)
    hindep (seeded_hidden_measurable N r sigma) hmem
    (le_of_eq (seeded_hidden_mean_budget N r P)) I.mu ⟨le_rfl, I.mu_lt_L.le⟩
    (fun s p ↦ noise N sigma s p.2) (seeded_noise_martingale N r sigma P)
  · intro s hs
    exact (seeded_noise_conditional_variance N r sigma P s hs).le
  · intro s
    have he : actualQuery M Prod.fst (fun p : U × Sample N ↦ r * p.2 none) I.mu
        (fun s p ↦ noise N sigma s p.2) s = gaussianQuery M I.mu r sigma s := by
      funext p
      unfold actualQuery gaussianQuery
      rw [hnoise]
    rw [he]
    exact gaussianQuery_adapted M I.mu r sigma s

theorem scalar_adaptive_mse_gaussian_lower (M : AdaptiveMethod N ℝ U)
    (P : Measure U) [IsProbabilityMeasure P] (I : InexactRealizations.Operators.SpectralInterval) (r sigma : ℝ)
    (hD : denominator N I.mu r sigma ≠ 0) :
    ENNReal.ofReal (r ^ 2 * sigma ^ 2 / denominator N I.mu r sigma) ≤ scalarMseRisk M P I r sigma :=
  (gaussian_randomized_mse_lower M I.mu r sigma hD P).trans
    (le_sSup (gaussian_model_value M P I r sigma))

theorem interior_denominator_nonzero (I : InexactRealizations.Operators.SpectralInterval) (hN : 0 < N) (r sigma : ℝ)
    (hdom : I.epsilon N * r ^ 2 < (sigma ^ 2 / (I.mu ^ 2 * N)) * (1 - I.epsilon N)) :
    denominator N I.mu r sigma ≠ 0 := by
  have he := AllLinear.epsilon_unit I hN
  have hs : sigma ≠ 0 := by
    intro hzero
    simp only [hzero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, zero_mul] at hdom
    exact (not_lt_of_ge (mul_nonneg he.1.le (sq_nonneg r))) hdom
  exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs)
    (by positivity : 0 ≤ (N : ℝ) * I.mu ^ 2 * r ^ 2))

theorem interior_value_gaussian (I : InexactRealizations.Operators.SpectralInterval) (hN : 0 < N) (r sigma : ℝ)
    (hdom : I.epsilon N * r ^ 2 < (sigma ^ 2 / (I.mu ^ 2 * N)) * (1 - I.epsilon N)) :
    AllLinear.allLinearValue I N r sigma = r ^ 2 * sigma ^ 2 / denominator N I.mu r sigma := by
  unfold AllLinear.allLinearValue AllLinear.value
  rw [ite_eq_right (not_le.mpr hdom)]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  unfold denominator
  field_simp [I.mu_pos.ne', hn]
  ring

theorem no_adaptive_improvement (M : AdaptiveMethod N ℝ U) (P : Measure U) [IsProbabilityMeasure P]
    (I : InexactRealizations.Operators.SpectralInterval) (hN : 0 < N) (r sigma : ℝ)
    (hdom : I.epsilon N * r ^ 2 < (sigma ^ 2 / (I.mu ^ 2 * N)) * (1 - I.epsilon N)) :
    ENNReal.ofReal (AllLinear.allLinearValue I N r sigma) ≤ scalarMseRisk M P I r sigma := by
  rw [interior_value_gaussian I hN r sigma hdom]
  exact scalar_adaptive_mse_gaussian_lower M P I r sigma (interior_denominator_nonzero I hN r sigma hdom)

end
end InexactRealizations.Risk.Adaptive
