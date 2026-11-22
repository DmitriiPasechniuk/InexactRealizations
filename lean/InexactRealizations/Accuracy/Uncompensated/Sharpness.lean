import InexactRealizations.Accuracy.Uncompensated.LowerLimit
import InexactRealizations.Accuracy.Uncompensated.Accuracy

/-! The two-sided order and its actual admissible-rounding witness.
The leading coefficient below is obtained from the executed recurrence. 
-/
namespace InexactRealizations.Accuracy.Uncompensated
noncomputable section
open Filter Topology
open scoped BigOperators

theorem averageFactor_upper_order (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    I.L * UncompensatedWitness.averageFactor I N ≤ I.kappa * Real.sqrt I.kappa / 2 := by
  have hh := averageFactor_upper_decay I hN
  rw [limitingUpper_condition] at hh
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hk := kappa_gt_one I
  have hs := Real.sqrt_nonneg I.kappa
  have hratio : (N : ℝ) / ((N : ℝ) - 1) ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hp : 0 ≤ (I.kappa - 1) * Real.sqrt I.kappa / 4 := by positivity
  have hbound := mul_le_mul_of_nonneg_right hratio hp
  nlinarith

theorem averageFactor_eventual_order (I : InexactRealizations.Operators.SpectralInterval) (hk4 : 4 ≤ I.kappa) :
    ∀ᶠ N : ℕ in atTop,
      I.kappa * Real.sqrt I.kappa / 64 ≤ I.L * UncompensatedWitness.averageFactor I N ∧
        I.L * UncompensatedWitness.averageFactor I N ≤ I.kappa * Real.sqrt I.kappa / 2 := by
  have hs0 := Real.sqrt_nonneg I.kappa
  have hs2 := Real.sq_sqrt (show 0 ≤ I.kappa by linarith)
  have hs : 2 ≤ Real.sqrt I.kappa := by nlinarith
  have heps : 0 < I.kappa * Real.sqrt I.kappa / 64 := by positivity
  have hquad : I.kappa / 4 ≤ (Real.sqrt I.kappa - 1) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 3 * Real.sqrt I.kappa - 2 by linarith)
      (show 0 ≤ Real.sqrt I.kappa - 2 by linarith)]
  have hlow : I.kappa * Real.sqrt I.kappa / 32 ≤
      (Real.sqrt I.kappa - 1) ^ 2 * Real.sqrt I.kappa / 8 := by
    nlinarith [mul_le_mul_of_nonneg_right hquad hs0]
  filter_upwards [averageFactor_eventual_lower I heps, eventually_ge_atTop 2] with N hN hN2
  exact ⟨by nlinarith, averageFactor_upper_order I hN2⟩

theorem actual_witness_normalized_error (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    {rho : ℝ} (hrho : 0 ≤ rho) :
    Tendsto (fun u : ℝ ↦ |(UncompensatedWitness.atScale I N rho u).x N - rho| / u)
      (𝓝[>] 0) (𝓝 (I.L * UncompensatedWitness.averageFactor I N * rho)) := by
  obtain ⟨q, hq⟩ := UncompensatedWitness.atScale_output_expansion I hN rho
  have hcoef : 0 ≤ I.L * UncompensatedWitness.averageFactor I N * rho :=
    mul_nonneg (mul_nonneg (lt_trans I.mu_pos I.mu_lt_L).le (UncompensatedWitness.averageFactor_nonneg I hN)) hrho
  have hqc : Tendsto (fun u : ℝ ↦ q.eval u) (𝓝 0) (𝓝 (q.eval 0)) := q.continuous.tendsto 0
  have hc : Tendsto (fun _ : ℝ ↦ I.L * UncompensatedWitness.averageFactor I N * rho)
      (𝓝 0) (𝓝 (I.L * UncompensatedWitness.averageFactor I N * rho)) := tendsto_const_nhds
  have hh := (hc.add (tendsto_id.mul hqc)).abs
  simp only [zero_mul, add_zero, abs_of_nonneg hcoef] at hh
  apply (hh.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : 0 < u := hu
  have heq : |(UncompensatedWitness.atScale I N rho u).x N - rho| / u =
      |I.L * UncompensatedWitness.averageFactor I N * rho + u * q.eval u| := by
    calc
      _ = |(UncompensatedWitness.atScale I N rho u).x N - rho| / |u| := by rw [abs_of_pos hu']
      _ = |((UncompensatedWitness.atScale I N rho u).x N - rho) / u| := (abs_div _ _).symm
      _ = _ := by
        rw [hq u]
        congr 1
        field_simp [hu'.ne']
  exact heq.symm

end
end InexactRealizations.Accuracy.Uncompensated
