import Mathlib.Probability.Independence.Basic

/-! Adding an independent random seed preserves independence from the past.
This is used to verify the actual randomized Gaussian oracle model. 
-/
namespace InexactRealizations.Probability
noncomputable section
open MeasureTheory ProbabilityTheory Set
variable {U Ω A B : Type*} [MeasurableSpace U] [MeasurableSpace Ω]
  [MeasurableSpace A] [MeasurableSpace B]
  {P : Measure U} {Q : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

theorem independent_seed_pair {f : Ω → A} {g : Ω → B}
    (hf : Measurable f) (hg : Measurable g) (hfg : IndepFun f g Q) :
    IndepFun (fun p : U × Ω ↦ f p.2) (fun p : U × Ω ↦ (p.1, g p.2)) (P.prod Q) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hleft : (fun p : U × Ω ↦ f p.2) ⁻¹' s = univ ×ˢ (f ⁻¹' s) := by ext p; simp
  have hbase : (P.prod Q) ((fun p : U × Ω ↦ f p.2) ⁻¹' s) = Q (f ⁻¹' s) := by
    rw [hleft, Measure.prod_prod, measure_univ, one_mul]
  have hfm : MeasurableSet ((fun p : U × Ω ↦ f p.2) ⁻¹' s) := (hf.comp measurable_snd) hs
  have htm : MeasurableSet ((fun p : U × Ω ↦ (p.1, g p.2)) ⁻¹' t) :=
    (measurable_fst.prodMk (hg.comp measurable_snd)) ht
  rw [Measure.prod_apply (hfm.inter htm), hbase, Measure.prod_apply htm]
  calc
    _ = ∫⁻ u, Q (f ⁻¹' s) * Q ((fun x : Ω ↦ (u, g x)) ⁻¹' t) ∂P := by
      apply lintegral_congr
      intro u
      exact hfg.measure_inter_preimage_eq_mul s ((fun b ↦ (u, b)) ⁻¹' t) hs
        (measurable_const.prodMk measurable_id ht)
    _ = _ := lintegral_const_mul' _ _ (measure_ne_top _ _)

end
end InexactRealizations.Probability
