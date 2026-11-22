import InexactRealizations.Algorithms.AveragedBalancedData

/-! Exact coefficient identities used in the current roundoff proof.
The weighted form remains valid at the zero initial mass. 
-/
namespace InexactRealizations.Roundoff
noncomputable section
open InexactRealizations.Balanced InexactRealizations.Algorithms.AveragedBalanced

theorem stored_mass (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    mass I N (s + 2) = normalizer I N s - omega N (s + 2) * I.den s := by
  rw [mass_step, mass]
  ring

theorem recovery_average_coefficient (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s < N) :
    (1 - theta I N s) / theta I N s = mass I N s / (omega N s * I.den s) := by
  rw [theta_mass I hN hs, theta_eq I hN hs]
  field_simp [(omega_pos hN hs).ne', I.den_ne s, (normalizer_pos I hN hs).ne']

theorem averaging_recovery_coefficient (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : 2 ≤ s) (hsN : s + 2 < N) :
    phi I N s / theta I N s =
      (omega N s - omega N (s + 2)) * normalizer I N s / (omega N s * mass I N (s + 2)) := by
  have hs' : s < N := by omega
  rw [phi_eq I hN hs hsN, theta_eq I hN hs']
  field_simp [(omega_pos hN hs').ne', I.den_ne s, (normalizer_pos I hN hs').ne',
    (mass_next_pos I hN hs hsN).ne']

theorem average_error_telescope (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : 2 ≤ s) (hsN : s + 2 < N) :
    mass I N (s + 2) / omega N (s + 2) * (1 - phi I N s / theta I N s) = mass I N s / omega N s := by
  have hs' : s < N := by omega
  rw [averaging_recovery_coefficient I hN hs hsN]
  calc
    _ = (omega N s * mass I N (s + 2) -
        (omega N s - omega N (s + 2)) * normalizer I N s) / (omega N s * omega N (s + 2)) := by
      field_simp [(omega_pos hN hs').ne', (omega_pos hN hsN).ne', (mass_next_pos I hN hs hsN).ne']
    _ = _ := by
      rw [stored_mass, mass]
      field_simp [(omega_pos hN hs').ne', (omega_pos hN hsN).ne']
      ring

end
end InexactRealizations.Roundoff
