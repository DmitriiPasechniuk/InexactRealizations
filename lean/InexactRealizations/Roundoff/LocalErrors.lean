import Mathlib.Tactic

/-! Literal local-error equations of current. These definitions
compute the printed stages; none assumes the claimed terminal error formula. 
-/
namespace InexactRealizations.Roundoff
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def computedQuery (theta : ℝ) (x average error : E) : E := average + theta • (x - average) + error

def computedAnswer (H : E →ₗ[ℝ] E) (target query noise : E) : E := H (query - target) + noise

def recoveredGradient (theta : ℝ) (oldGradient answer error : E) : E :=
  oldGradient + theta⁻¹ • (answer - oldGradient) + error

def updatedAverage (phi : ℝ) (average x error : E) : E := average + phi • (x - average) + error

def combinedOracleError (H : E →ₗ[ℝ] E) (theta : ℝ) (w queryError recoveryError : E) : E :=
  w + H queryError + theta • recoveryError

def combinedAverageError (H : E →ₗ[ℝ] E) (averageError gradientError : E) : E :=
  gradientError - H averageError

theorem recovered_gradient_error (H : E →ₗ[ℝ] E) (theta : ℝ) (htheta : theta ≠ 0)
    (x target average oldGradient w queryError recoveryError : E) :
    theta • (recoveredGradient theta oldGradient
      (computedAnswer H target (computedQuery theta x average queryError) w) recoveryError - H (x - target)) =
      combinedOracleError H theta w queryError recoveryError -
        (1 - theta) • (oldGradient - H (average - target)) := by
  have he : theta • recoveredGradient theta oldGradient
      (computedAnswer H target (computedQuery theta x average queryError) w) recoveryError =
      theta • oldGradient + (computedAnswer H target (computedQuery theta x average queryError) w - oldGradient) +
        theta • recoveryError := by
    simp only [recoveredGradient, smul_add, smul_smul, mul_inv_cancel₀ htheta, one_smul]
  rw [smul_sub, he]
  simp only [computedAnswer, computedQuery, combinedOracleError, map_add, map_sub, map_smul]
  module

theorem updated_gradient_error (H : E →ₗ[ℝ] E) (phi : ℝ)
    (x target average oldGradient recovered averageError gradientError : E) :
    updatedAverage phi oldGradient recovered gradientError -
      H (updatedAverage phi average x averageError - target) =
      (1 - phi) • (oldGradient - H (average - target)) +
        phi • (recovered - H (x - target)) + combinedAverageError H averageError gradientError := by
  simp only [updatedAverage, combinedAverageError, map_add, map_sub, map_smul]
  module

theorem state_error_as_oracle_error (alpha beta : ℝ) (halpha : alpha ≠ 0)
    (x previous gradient error : E) :
    (1 + beta) • x - beta • previous - alpha • gradient + error =
      (1 + beta) • x - beta • previous - alpha • (gradient - alpha⁻¹ • error) := by
  simp only [smul_sub, smul_smul, mul_inv_cancel₀ halpha, one_smul]
  abel

end
end InexactRealizations.Roundoff
