import InexactRealizations.Accuracy.Estimates.Leading
import InexactRealizations.Accuracy.Bounds.Terminal

/-! Pointwise bounds on the average response, retaining the mass and
phi cancellations needed for cubic horizon growth. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
open InexactRealizations.Algorithms.AveragedBalanced

theorem mass_next_upper (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s + 2 < N) : mass I N (s + 2) ≤ I.den s := by
  have hz := normalizer_le_den I hN (by omega : s < N)
  have hw := (InexactRealizations.Balanced.omega_pos hN hs).le
  rw [mass_step]
  unfold mass
  nlinarith [mul_nonneg hw (I.den_pos s).le]

theorem averageWeight_bound (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s + 2 < N) :
    averageWeight I N s ≤ (N : ℝ) * (N - 1 - s : ℕ) * mass I N (s + 2) / (I.delta * I.den N) := by
  let k := N - 1 - s
  let p := (k ^ 2 / 4 : ℕ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hkEq : (k : ℝ) = (N : ℝ) - 1 - s := by dsimp [k]; push_cast [show 1 ≤ N by omega, show s ≤ N - 1 by omega]; ring
  have hfloorNat : 4 * p ≤ k ^ 2 := by dsimp [p]; omega
  have hfloor : 4 * (p : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hfloorNat
  have hw := InexactRealizations.Balanced.omega_pos hN hs
  have hwb := (omega_next_bounds hN hs).1
  rw [← hkEq] at hwb
  have hwb' : (k : ℝ) ≤ InexactRealizations.Balanced.omega N (s + 2) * N := (div_le_iff₀ hN0).mp hwb
  have hquot : 4 * (p : ℝ) / InexactRealizations.Balanced.omega N (s + 2) ≤ (N : ℝ) * k := by
    apply (div_le_iff₀ hw).mpr
    nlinarith [mul_le_mul_of_nonneg_left hwb' hk]
  have hm := mass_nonneg I hN hs
  have hc : 0 ≤ mass I N (s + 2) / (I.delta * I.den N) :=
    div_nonneg hm (mul_pos I.delta_pos (I.den_pos N)).le
  have hh := mul_le_mul_of_nonneg_left hquot hc
  rw [averageWeight, InexactRealizations.Roundoff.averageResponse_endpoint, InexactRealizations.Roundoff.averageScale]
  convert hh using 1 <;> dsimp only [p, k] <;> ring

theorem averageWeight_over_mass (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs2 : 2 ≤ s) (hs : s + 2 < N) :
    averageWeight I N s / mass I N (s + 2) ≤
      (N : ℝ) * (N - 1 - s : ℕ) / (I.delta * I.den N) := by
  have hm := mass_next_pos I hN hs2 hs
  apply (div_le_iff₀ hm).mpr
  convert averageWeight_bound I hN hs using 1
  ring

theorem averageWeight_phi (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs2 : 2 ≤ s) (hs : s + 2 < N) :
    averageWeight I N s * phi I N s ≤
      2 * (N : ℝ) * (N - 1 - s : ℕ) * I.den s / (((N : ℝ) - 1) * I.delta * I.den N) := by
  have hphi := (phi_unit I hN hs2 hs).1.le
  have hm := mass_next_pos I hN hs2 hs
  have hbase := mul_le_mul_of_nonneg_right (averageWeight_bound I hN hs) hphi
  have hidentity : mass I N (s + 2) * phi I N s =
      (InexactRealizations.Balanced.omega N s - InexactRealizations.Balanced.omega N (s + 2)) * I.den s := by
    rw [phi_eq I hN hs2 hs]
    field_simp [hm.ne']
  have hdrop := (omega_drop_bounds hN (show 1 ≤ s by omega)).2
  have hscale : 0 ≤ (N : ℝ) * (N - 1 - s : ℕ) * I.den s / (I.delta * I.den N) := by
    have hd := (I.den_pos s).le
    have hdN := (I.den_pos N).le
    have hdelta := I.delta_pos.le
    positivity
  have hh := mul_le_mul_of_nonneg_left hdrop hscale
  calc
    _ ≤ ((N : ℝ) * (N - 1 - s : ℕ) / (I.delta * I.den N)) *
        (mass I N (s + 2) * phi I N s) := by
          convert hbase using 1
          ring
    _ = ((N : ℝ) * (N - 1 - s : ℕ) * I.den s / (I.delta * I.den N)) *
        (InexactRealizations.Balanced.omega N s - InexactRealizations.Balanced.omega N (s + 2)) := by rw [hidentity]; ring
    _ ≤ _ := by
      convert hh using 1
      have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
      field_simp [I.delta_pos.ne', (I.den_pos N).ne', (show (N : ℝ) - 1 ≠ 0 by linarith)]

end
end InexactRealizations.Accuracy.Execution
