import InexactRealizations.Channel.FiniteNoiseFirstOrder
import InexactRealizations.Probability.SignProducts

namespace InexactRealizations.Channel
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators
variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual finite random channel oracle, with one fresh fair sign per call. -/
def finiteSignOutput (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (δ : ℝ) (ω : Fin N → Bool) : E :=
  finiteNoiseOutput h H P initial (fun s => δ*InexactRealizations.Probability.Signs.stream N 1 s ω)

/-- Exact Walsh expansion of the actual physical finite-sign terminal. -/
theorem finiteSignOutput_expansion (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (δ : ℝ) (ω : Fin N → Bool) :
    finiteSignOutput h H P initial δ ω=
      ∑ S ∈ (Finset.range N).powerset, InexactRealizations.Probability.SignProducts.characterNat N S ω •
        (δ^S.card • finiteNoiseCoefficient h H P initial S) := by
  rw [finiteSignOutput, finiteNoise_sign_expansion]
  apply Finset.sum_congr rfl
  intro S _
  rw [smul_smul]
  congr 1
  exact mul_comm _ _

/-- Centering removes exactly the empty mask of the physical expansion. -/
theorem finiteSignOutput_centered (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (δ : ℝ) (ω : Fin N → Bool) :
    finiteSignOutput h H P initial δ ω-(aeval H h.terminal) initial=
      ∑ S ∈ (Finset.range N).powerset.erase ∅,
        InexactRealizations.Probability.SignProducts.characterNat N S ω •
          (δ^S.card • finiteNoiseCoefficient h H P initial S) := by
  let f (S : Finset ℕ) := InexactRealizations.Probability.SignProducts.characterNat N S ω •
    (δ^S.card • finiteNoiseCoefficient h H P initial S)
  have he := Finset.sum_erase_add (Finset.range N).powerset f (by simp : ∅∈(Finset.range N).powerset)
  have hz : f ∅=(aeval H h.terminal) initial := by
    simp [f, InexactRealizations.Probability.SignProducts.characterNat, finiteNoiseCoefficient_empty]
  rw [finiteSignOutput_expansion, ← he, hz]
  abel

variable [CompleteSpace E]

/-- The actual finite random oracle has exactly the noiseless terminal as its mean. -/
theorem finiteSignOutput_mean (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (δ : ℝ) :
    (∫ ω, finiteSignOutput h H P initial δ ω ∂InexactRealizations.Probability.Signs.law N)=
      (aeval H h.terminal) initial := by
  simp_rw [finiteSignOutput_expansion]
  rw [InexactRealizations.Probability.SignProducts.integral_sum _
    (fun _ hS => Finset.mem_powerset.mp hS)]
  simp [finiteNoiseCoefficient_empty]

omit [CompleteSpace E] in
/-- The exact physical finite-noise variance is a finite sum of nonnegative orders. -/
theorem finiteSignOutput_variance (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (P : Fin N → E →ₗ[ℝ] E) (initial : E) (δ : ℝ) :
    (∫ ω, ‖finiteSignOutput h H P initial δ ω-(aeval H h.terminal) initial‖^2
      ∂InexactRealizations.Probability.Signs.law N)=
      ∑ S ∈ (Finset.range N).powerset.erase ∅,
        δ^(2*S.card)*‖finiteNoiseCoefficient h H P initial S‖^2 := by
  simp_rw [finiteSignOutput_centered]
  rw [InexactRealizations.Probability.SignProducts.integral_norm_sq_sum _
    (fun _ hS => Finset.mem_powerset.mp (Finset.mem_erase.mp hS).2)]
  apply Finset.sum_congr rfl
  intro S _
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← pow_mul, Nat.mul_comm]

end
end InexactRealizations.Channel
