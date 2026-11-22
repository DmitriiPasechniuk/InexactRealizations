import InexactRealizations.Roundoff.LocalErrors
import InexactRealizations.Roundoff.ErrorSystem

/-! The exact local-error execution equations printed before.
Only these operational equations are hypotheses; no terminal error identity,
response representation or optimality certificate is part of the model. 
-/
namespace InexactRealizations.Roundoff
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

structure LocalErrorStreams (E : Type*) where
  oracle : ℕ → E
  query : ℕ → E
  recovery : ℕ → E
  average : ℕ → E
  gradient : ℕ → E
  state : ℕ → E

def earlierAverage (f : ℕ → E) (s : ℕ) : E := if s < 2 then 0 else f (s - 2)

structure LocalExecution (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E)
    (initial target : E) (ell : LocalErrorStreams E) where
  x : ℕ → E
  y : ℕ → E
  g : ℕ → E
  recovered : ℕ → E
  average : ℕ → E
  gradient : ℕ → E
  initial_eq : x 0 = initial
  query_eq : ∀ s, s < N → y s = computedQuery (theta I N s) (x s) (earlierAverage average s) (ell.query s)
  answer_eq : ∀ s, s < N → g s = computedAnswer H target (y s) (ell.oracle s)
  recovered_eq : ∀ s, s < N →
    recovered s = recoveredGradient (theta I N s) (earlierAverage gradient s) (g s) (ell.recovery s)
  average_eq : ∀ s, s + 2 < N →
    average s = updatedAverage (phi I N s) (earlierAverage average s) (x s) (ell.average s)
  gradient_eq : ∀ s, s + 2 < N →
    gradient s = updatedAverage (phi I N s) (earlierAverage gradient s) (recovered s) (ell.gradient s)
  state_eq : ∀ s, s < N →
    x (s + 1) = (1 + beta I s) • x s - beta I s • x (s - 1) - alpha I s • recovered s + ell.state (s + 1)

def hatNoise (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E) (ell : LocalErrorStreams E) (s : ℕ) : E :=
  combinedOracleError H (theta I N s) (ell.oracle s) (ell.query s) (ell.recovery s)

def averageNoise (H : E →ₗ[ℝ] E) (ell : LocalErrorStreams E) (s : ℕ) : E :=
  combinedAverageError H (ell.average s) (ell.gradient s)

namespace LocalExecution
variable {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {H : E →ₗ[ℝ] E} {initial target : E} {ell : LocalErrorStreams E}

def hat (u : LocalExecution I N H initial target ell) (s : ℕ) : E := u.recovered s - H (u.x s - target)
def bar (u : LocalExecution I N H initial target ell) (s : ℕ) : E := u.gradient s - H (u.average s - target)

theorem error_system (u : LocalExecution I N H initial target ell) (hN : 2 ≤ N) :
    ErrorSystem I N (hatNoise I N H ell) (averageNoise H ell) u.hat u.bar where
  recovery s hs := by
    have hh := recovered_gradient_error H (theta I N s) (theta_unit I hN hs).1.ne' (u.x s) target
      (earlierAverage u.average s) (earlierAverage u.gradient s)
      (ell.oracle s) (ell.query s) (ell.recovery s)
    rw [← u.query_eq s hs, ← u.answer_eq s hs, ← u.recovered_eq s hs] at hh
    change theta I N s • u.hat s = hatNoise I N H ell s -
      (1 - theta I N s) • (earlierAverage u.gradient s - H (earlierAverage u.average s - target)) at hh
    by_cases hsmall : s < 2
    · simpa only [theta, hsmall, ite_true, sub_self, zero_smul, sub_zero] using hh
    · simpa only [earlierAverage, priorError, hsmall, ite_false, bar] using hh
  averaging s hs := by
    have hh := updated_gradient_error H (phi I N s) (u.x s) target (earlierAverage u.average s)
      (earlierAverage u.gradient s) (u.recovered s) (ell.average s) (ell.gradient s)
    rw [← u.gradient_eq s hs, ← u.average_eq s hs] at hh
    change u.bar s = (1 - phi I N s) • (earlierAverage u.gradient s - H (earlierAverage u.average s - target)) +
      phi I N s • u.hat s + averageNoise H ell s at hh
    by_cases hsmall : s < 2
    · simpa only [phi, hsmall, ite_true, sub_self, zero_smul, zero_add] using hh
    · simpa only [earlierAverage, priorError, hsmall, ite_false, bar] using hh

theorem recovered_error (u : LocalExecution I N H initial target ell) (hN : 2 ≤ N)
    (s : ℕ) (hs : s < N) :
    u.recovered s - H (u.x s - target) = recoveredError I N (hatNoise I N H ell) (averageNoise H ell) s :=
  (errorSystem_unique I hN _ _ u.hat u.bar (u.error_system hN) s hs).1

end LocalExecution
end
end InexactRealizations.Roundoff
