import InexactRealizations.Comparisons.Classical.Bounds
import InexactRealizations.Gains.Witness
import InexactRealizations.Gains.HilbertSchmidt
import InexactRealizations.Operators.Prefix.Asymptotics

namespace InexactRealizations.Classical
noncomputable section
open Filter Topology
open scoped BigOperators

/-- Physical kernel equality preserves the complete spectral gain. -/
theorem spectralGain_eq_prefix (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0<N) :
    (history I N).spectralGain I = (InexactRealizations.Operators.Prefix.realization I).gain I N := by
  have hk (x y : ℝ) : (history I N).realization.kernelNorm N x y =
      (InexactRealizations.Operators.Prefix.realization I).kernelNorm N x y := by
    unfold InexactRealizations.Operators.Realization.kernelNorm
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_range] at hs
    rw [(history I N).realization_kernel ⟨s,hs⟩ x y]
    exact congrArg (fun t : ℝ => t^2) (physicalKernel_eq_prefix I N hN ⟨s,hs⟩ x y)
  unfold InexactRealizations.History.spectralGain InexactRealizations.Operators.Realization.gain
  congr 1
  ext v
  simp only [InexactRealizations.Operators.Realization.gainValues, Set.mem_ofPred_eq, hk]

/-- Exact finite classical spectral gain, including the exceptional first call. -/
theorem spectralGain_exact (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0<N) :
    (history I N).spectralGain I = I.epsilon N/I.delta *
      Real.sqrt (4*(N:ℝ)^2+16*∑ m ∈ Finset.range N, (m:ℝ)^2) := by
  rw [spectralGain_eq_prefix I N hN, InexactRealizations.Operators.Prefix.gain_exact_sum I N hN]

/-- Product-energy expression attained simultaneously at the lower endpoint. -/
theorem spectralGain_product_energy (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0<N) :
    (history I N).spectralGain I = Analysis.energyNorm
      (fun s : Fin N => responseBound I N s * queryBound I s) := by
  apply InexactRealizations.History.spectralGain_eq_product_energy _ I _ _ (responseBounds I N hN)
    (fun s => (queryBound_pos I s).le) (fun s _ hx => query_bound I N s hx)
  · intro s
    rw [response_endpoint I N hN s, abs_neg, abs_of_pos (responseBound_pos I s)]
  · intro s
    rw [query_endpoint I N s, abs_of_pos (queryBound_pos I s)]

/-- Both physical operator perturbation classes attain the same classical gain. -/
theorem operatorGain_eq (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0<N)
    (symmetric : Bool) : Gains.operatorGain (history I N) I symmetric =
      (history I N).spectralGain I := by
  apply le_antisymm
  · rw [spectralGain_product_energy I N hN]
    exact Gains.operatorGain_le_product_energy _ I _ _ (responseBounds I N hN)
      (fun s => (queryBound_pos I s).le) (fun s _ hx => query_bound I N s hx) symmetric
  · apply le_csInf (Gains.operatorBounds_nonempty _ I symmetric)
    intro C hb
    obtain ⟨x,hx,y,hy,he⟩ := (history I N).spectralGain_attained I
    rw [← he]
    exact Gains.operatorBound_kernel_norm _ I symmetric C hb x y hx hy

/-- The actual-query local relative coefficient has the same exact classical value. -/
theorem localRelativeGain_eq (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0<N) :
    Gains.localRelativeGain (history I N) I = (history I N).spectralGain I := by
  apply le_antisymm
  · rw [spectralGain_product_energy I N hN]
    exact Gains.localRelativeGain_le_product_energy _ I _ _ (responseBounds I N hN)
      (fun s => (queryBound_pos I s).le) (fun s _ hx => query_bound I N s hx)
  · apply le_csInf (Gains.localRelativeBounds_nonempty _ I)
    intro C hb
    obtain ⟨x,hx,y,hy,he⟩ := (history I N).spectralGain_attained I
    rw [← he]
    exact Gains.operatorBound_kernel_norm _ I false C
      (Gains.localRelativeBound_operatorBound _ I C hb false) x y hx hy

/-- The classical gain grows with the stated sharp N to the three-halves coefficient. -/
theorem gain_asymptotic (I : InexactRealizations.Operators.SpectralInterval) :
    Tendsto (fun N : ℕ => (history I N).spectralGain I*I.delta /
      (I.epsilon N*(N:ℝ)*Real.sqrt N)) atTop (𝓝 (4/Real.sqrt 3)) := by
  apply (InexactRealizations.Operators.Prefix.gain_asymptotic I).congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [spectralGain_eq_prefix I N hN]

end
end InexactRealizations.Classical
