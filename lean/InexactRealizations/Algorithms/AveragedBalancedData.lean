import InexactRealizations.Algorithms.AveragedBalancedScalars
import InexactRealizations.Algorithms.AveragedBalancedRegisters
import InexactRealizations.Operators.Prefix.Exactness

/-! The prepared coefficients in the actual nine-register program and
the weighted-average identities needed for its nominal invariant. 
-/
namespace InexactRealizations.Algorithms.AveragedBalanced
noncomputable section
open Polynomial Polynomial.Chebyshev
open InexactRealizations.Balanced

def alpha (I : InexactRealizations.Operators.SpectralInterval) : ℕ → ℝ
  | 0 => 2 / (I.L + I.mu)
  | s + 1 => 4 * ratio I (s + 1) / I.delta

def beta (I : InexactRealizations.Operators.SpectralInterval) : ℕ → ℝ
  | 0 => 0
  | s + 1 => ratio I s * ratio I (s + 1)

def parameters (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : AveragedParameters N where
  alpha s := alpha I s.val
  beta s := beta I s.val
  theta s := theta I N s.val
  phi s := phi I N s.val

theorem alpha_eq (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) : alpha I s = InexactRealizations.Operators.Prefix.gamma I s := by
  cases s with
  | zero => rfl
  | succ s =>
    rw [alpha, ratio_eq, InexactRealizations.Operators.Prefix.gamma]
    ring

theorem beta_succ_eq (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) :
    beta I (s + 1) = InexactRealizations.Operators.Prefix.beta I (s + 1) := by
  rw [beta, ratio_eq, ratio_eq]
  simp only [InexactRealizations.Operators.Prefix.beta, Nat.add_sub_cancel]
  field_simp [I.den_ne (s + 1), I.den_ne (s + 2)]

theorem prefix_eval_step (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) (lam : ℝ) :
    (I.residual (s + 1)).eval lam =
      (1 + beta I s) * (I.residual s).eval lam - beta I s * (I.residual (s - 1)).eval lam -
        alpha I s * lam * (I.residual s).eval lam := by
  cases s with
  | zero =>
    simp only [alpha, beta, zero_add, add_zero, zero_mul, sub_zero,
      InexactRealizations.Operators.Prefix.residual_zero, InexactRealizations.Operators.Prefix.residual_one, eval_sub,
      eval_mul, eval_one, eval_C, eval_X]
    ring
  | succ s =>
    rw [beta_succ_eq, alpha_eq, InexactRealizations.Operators.Prefix.gamma_succ]
    have hh := congrArg (fun p : ℝ[X] ↦ p.eval lam) (InexactRealizations.Operators.Prefix.residual_recurrence I s)
    simp only [eval_sub, eval_mul, eval_C, eval_one, eval_X] at hh
    simpa only [Nat.add_sub_cancel] using hh.trans (by ring)

def mass (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ := normalizer I N s - omega N s * I.den s

@[simp] theorem mass_zero (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : mass I N 0 = 0 := by simp [mass]

@[simp] theorem mass_one (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : mass I N 1 = 0 := by simp [mass]

theorem mass_step (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    mass I N (s + 2) = mass I N s + (omega N s - omega N (s + 2)) * I.den s := by
  rw [mass, normalizer_step, mass]
  ring

theorem mass_nonneg (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    0 ≤ mass I N s := sub_nonneg.mpr (normalizer_ge_top I hN hs)

theorem mass_next_pos (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : 2 ≤ s) (hsN : s + 2 < N) : 0 < mass I N (s + 2) := by
  rw [mass_step]
  exact add_pos_of_nonneg_of_pos (mass_nonneg I hN (by omega))
    (mul_pos (sub_pos.mpr (omega_strict_drop hN hs hsN)) (I.den_pos s))

theorem phi_eq (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : 2 ≤ s) (hsN : s + 2 < N) :
    phi I N s = (omega N s - omega N (s + 2)) * I.den s / mass I N (s + 2) := by
  have hsmall : ¬s < 2 := by omega
  have he : mass I N (s + 2) = I.den s * (zeta I N s - omega N (s + 2)) := by
    rw [zeta_eq, mass_step, mass]
    field_simp [I.den_ne s]
    ring
  rw [phi, ite_eq_right hsmall, he]
  field_simp [I.den_ne s, (phi_denominator_pos I hN hs hsN).ne']

theorem theta_mass (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    1 - theta I N s = mass I N s / normalizer I N s := by
  rw [theta_eq I hN hs]
  unfold mass
  field_simp [(normalizer_pos I hN hs).ne']

theorem prefix_scaled (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) (lam : ℝ) :
    I.den s * (I.residual s).eval lam = (T ℝ s).eval (I.z lam) := by
  rw [I.residual_eval]
  field_simp [I.den_ne s]

theorem weighted_query (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ} (hN : 2 ≤ N) (hs : s < N)
    (lam average : ℝ) (ha : mass I N s * average = (remainder N s).eval (I.z lam)) :
    theta I N s * (I.residual s).eval lam + (1 - theta I N s) * average =
      (psi N s).eval (I.z lam) / normalizer I N s := by
  rw [theta_mass I hN hs, theta_eq I hN hs]
  calc
    _ = (omega N s * (I.den s * (I.residual s).eval lam) + mass I N s * average) /
        normalizer I N s := by ring
    _ = _ := by rw [prefix_scaled, ha]; simp only [psi, eval_add, eval_mul, eval_C]; ring

theorem weighted_average_step (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : 2 ≤ s) (hsN : s + 2 < N) (lam average : ℝ)
    (ha : mass I N s * average = (remainder N s).eval (I.z lam)) :
    mass I N (s + 2) * (phi I N s * (I.residual s).eval lam + (1 - phi I N s) * average) =
      (remainder N (s + 2)).eval (I.z lam) := by
  have hm := (mass_next_pos I hN hs hsN).ne'
  have hc := prefix_scaled I s lam
  have hr : (remainder N (s + 2)).eval (I.z lam) =
      (remainder N s).eval (I.z lam) + (omega N s - omega N (s + 2)) * (T ℝ s).eval (I.z lam) := by
    simp only [remainder, eval_add, eval_mul, eval_C]
  have hp : mass I N (s + 2) * phi I N s = (omega N s - omega N (s + 2)) * I.den s := by
    rw [phi_eq I hN hs hsN]
    field_simp [hm]
  have hq : mass I N (s + 2) * (1 - phi I N s) = mass I N s := by
    rw [mul_sub, mul_one, hp, mass_step]
    ring
  calc
    _ = (mass I N (s + 2) * phi I N s) * (I.residual s).eval lam +
        (mass I N (s + 2) * (1 - phi I N s)) * average := by ring
    _ = (omega N s - omega N (s + 2)) * (I.den s * (I.residual s).eval lam) +
        mass I N s * average := by rw [hp, hq]; ring
    _ = _ := by rw [hc, ha, hr]; ring

theorem weighted_startup_step (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (hs : s < 2) (lam : ℝ) :
    mass I N (s + 2) * (I.residual s).eval lam = (remainder N (s + 2)).eval (I.z lam) := by
  have hm : mass I N s = 0 := by
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;> simp
  have hr : (remainder N s).eval (I.z lam) = 0 := by
    rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl <;> simp [remainder]
  calc
    _ = (omega N s - omega N (s + 2)) * (I.den s * (I.residual s).eval lam) := by
      rw [mass_step, hm]
      ring
    _ = (remainder N s).eval (I.z lam) +
        (omega N s - omega N (s + 2)) * (T ℝ s).eval (I.z lam) := by rw [prefix_scaled, hr, zero_add]
    _ = _ := by simp only [remainder, eval_add, eval_mul, eval_C]

end
end InexactRealizations.Algorithms.AveragedBalanced
