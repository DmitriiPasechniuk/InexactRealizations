import InexactRealizations.History.Degrees
import InexactRealizations.Operators.Chebyshev.Normalization
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Polynomial

/-! Actual spectral probability measures, without a finite-support restriction,
and the literal polynomial energies and Christoffel infima. 
-/
namespace InexactRealizations.Averages
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators

structure SpectralLaw (I : InexactRealizations.Operators.SpectralInterval) where
  measure : Measure ℝ
  probability : IsProbabilityMeasure measure
  spectral : ∀ᵐ x ∂measure, x ∈ Set.Icc I.mu I.L

attribute [instance] SpectralLaw.probability

namespace SpectralLaw

variable {I : InexactRealizations.Operators.SpectralInterval} (ρ : SpectralLaw I)

theorem continuous_integrable {f : ℝ → ℝ} (hf : Continuous f) : Integrable f ρ.measure := by
  have hi : IntegrableOn f (Set.Icc I.mu I.L) ρ.measure := hf.integrableOn_Icc
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ρ.spectral] at hi

def energy (p : ℝ[X]) : ℝ := ∫ x, p.eval x ^ 2 ∂ρ.measure

theorem energy_nonneg (p : ℝ[X]) : 0 ≤ ρ.energy p := integral_nonneg fun _ ↦ sq_nonneg _

theorem energy_smul (c : ℝ) (p : ℝ[X]) : ρ.energy (c • p) = c ^ 2 * ρ.energy p := by
  simp only [energy, eval_smul, smul_eq_mul, mul_pow, integral_const_mul]

def variance {N : ℕ} (h : InexactRealizations.History N) : ℝ := ∑ s, ρ.energy (h.response s)

def christoffelValues (k : ℕ) : Set ℝ :=
  {v | ∃ p : ℝ[X], p.natDegree ≤ k ∧ p.eval I.mu = 1 ∧ v = ρ.energy p}

def christoffel (k : ℕ) : ℝ := sInf (ρ.christoffelValues k)

theorem christoffelValues_nonempty (k : ℕ) : (ρ.christoffelValues k).Nonempty :=
  ⟨ρ.energy 1, 1, by simp, by simp, rfl⟩

theorem christoffelValues_bddBelow (k : ℕ) : BddBelow (ρ.christoffelValues k) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨p, _, _, rfl⟩
  exact ρ.energy_nonneg p

theorem christoffel_le (k : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ k) (he : p.eval I.mu = 1) :
    ρ.christoffel k ≤ ρ.energy p :=
  csInf_le (ρ.christoffelValues_bddBelow k) ⟨p, hp, he, rfl⟩

theorem christoffel_energy_le (k : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ k) :
    ρ.christoffel k * p.eval I.mu ^ 2 ≤ ρ.energy p := by
  by_cases hz : p.eval I.mu = 0
  · simpa only [hz, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using ρ.energy_nonneg p
  · have hh := ρ.christoffel_le k ((p.eval I.mu)⁻¹ • p)
      ((natDegree_smul_le _ _).trans hp) (by simp [hz])
    rw [energy_smul] at hh
    have hs : p.eval I.mu ^ 2 ≠ 0 := pow_ne_zero _ hz
    have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg (p.eval I.mu))
    exact hm.trans_eq (by field_simp)

theorem variance_christoffel_lower {N : ℕ} (h : InexactRealizations.History N) :
    (∑ s : Fin N, ρ.christoffel (N - 1 - s.val) * (h.response s).eval I.mu ^ 2) ≤ ρ.variance h := by
  apply Finset.sum_le_sum
  intro s _
  exact ρ.christoffel_energy_le _ _ (h.response_natDegree_le s)

end SpectralLaw
end
end InexactRealizations.Averages
