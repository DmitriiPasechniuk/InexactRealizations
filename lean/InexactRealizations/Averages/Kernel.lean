import InexactRealizations.Averages.Measure
import Mathlib.Algebra.Polynomial.Sequence

/-! The finite reproducing-kernel argument needed for the two explicit
Christoffel values. All orthogonality hypotheses will be discharged for
the actual Legendre and Chebyshev polynomials and the actual measures. 
-/
namespace InexactRealizations.Averages.SpectralLaw
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators
variable {I : InexactRealizations.Operators.SpectralInterval} (ρ : SpectralLaw I)

def integralMap : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x, p.eval x ∂ρ.measure
  map_add' p q := by
    simp only [eval_add]
    exact integral_add (ρ.continuous_integrable p.continuous) (ρ.continuous_integrable q.continuous)
  map_smul' c p := by simp only [eval_smul, smul_eq_mul, integral_const_mul, RingHom.id_apply]

def pairing (p q : ℝ[X]) : ℝ := ρ.integralMap (p * q)

theorem pairing_self (p : ℝ[X]) : ρ.pairing p p = ρ.energy p := by
  change (∫ x, (p * p).eval x ∂ρ.measure) = ∫ x, p.eval x ^ 2 ∂ρ.measure
  simp only [eval_mul, pow_two]

def pairingMap (p : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun q := ρ.pairing p q
  map_add' q r := by simp only [pairing, mul_add, map_add]
  map_smul' c q := by simp only [pairing, mul_smul_comm, map_smul, RingHom.id_apply]

theorem energy_sub_smul (p q : ℝ[X]) (c : ℝ) :
    ρ.energy (p - c • q) = ρ.energy p - 2 * c * ρ.pairing q p + c ^ 2 * ρ.energy q := by
  have he : (p - c • q) * (p - c • q) = p * p - (2 * c) • (q * p) + c ^ 2 • (q * q) := by
    simp only [smul_eq_C_mul, map_mul, map_pow, map_ofNat]
    ring
  rw [← pairing_self, pairing, he, map_add, map_sub, map_smul, map_smul]
  have hp : ρ.integralMap (p * p) = ρ.energy p := ρ.pairing_self p
  have hq : ρ.integralMap (q * q) = ρ.energy q := ρ.pairing_self q
  rw [hp, hq]
  rfl

def kernel (S : Polynomial.Sequence ℝ) (w : ℕ → ℝ) (k : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (k + 1), w j • S j

theorem kernel_degree (S : Polynomial.Sequence ℝ) (w : ℕ → ℝ) (k : ℕ) :
    (kernel S w k).natDegree ≤ k := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_smul_le _ _).trans ((S.natDegree_eq j).le.trans (by have := Finset.mem_range.mp hj; omega))

theorem kernel_reproduces (S : Polynomial.Sequence ℝ) (w : ℕ → ℝ)
    (hne : ∀ j, (S j).eval I.mu = 1)
    (horth : ∀ i j, i ≠ j → ρ.pairing (S i) (S j) = 0)
    (hnorm : ∀ j, w j * ρ.energy (S j) = 1)
    (k : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ k) :
    ρ.pairing (kernel S w k) p = p.eval I.mu := by
  let F : ℝ[X] →ₗ[ℝ] ℝ := ρ.pairingMap (kernel S w k) - (aeval I.mu).toLinearMap
  have hspan : p ∈ Submodule.span ℝ (S '' Set.Iio (k + 1)) := by
    rw [S.span_degreeLT (fun j _ ↦ isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (S.ne_zero j))), mem_degreeLT]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hp)
  have hker : Submodule.span ℝ (S '' Set.Iio (k + 1)) ≤ F.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change ρ.pairing (kernel S w k) (S j) - (S j).eval I.mu = 0
    rw [hne]
    apply sub_eq_zero.mpr
    unfold pairing kernel
    rw [Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · change w j * ρ.pairing (S j) (S j) = 1
      rw [pairing_self]
      exact hnorm j
    · intro i _ hij
      change w i * ρ.pairing (S i) (S j) = 0
      rw [horth i j hij, mul_zero]
    · intro hj'
      exact (hj' (Finset.mem_range.mpr hj)).elim
  exact sub_eq_zero.mp (hker hspan)

theorem christoffel_of_orthogonal_sequence (S : Polynomial.Sequence ℝ) (w : ℕ → ℝ)
    (hw : ∀ j, 0 < w j) (hne : ∀ j, (S j).eval I.mu = 1)
    (horth : ∀ i j, i ≠ j → ρ.pairing (S i) (S j) = 0)
    (hnorm : ∀ j, w j * ρ.energy (S j) = 1) (k : ℕ) :
    ρ.christoffel k = (∑ j ∈ Finset.range (k + 1), w j)⁻¹ := by
  let K := kernel S w k
  let A := ∑ j ∈ Finset.range (k + 1), w j
  have hA : 0 < A := Finset.sum_pos (fun j _ ↦ hw j) (by simp)
  have heval : K.eval I.mu = A := by simp only [K, kernel, eval_finsetSum, eval_smul, hne, smul_eq_mul, mul_one, A]
  have he : ρ.energy K = A := by
    rw [← pairing_self, kernel_reproduces ρ S w hne horth hnorm k K (kernel_degree S w k), heval]
  have hmin (p : ℝ[X]) (hp : p.natDegree ≤ k) (hp1 : p.eval I.mu = 1) : A⁻¹ ≤ ρ.energy p := by
    have hb := ρ.energy_nonneg (p - A⁻¹ • K)
    rw [energy_sub_smul, he, kernel_reproduces ρ S w hne horth hnorm k p hp, hp1] at hb
    have hid : ρ.energy p - 2 * A⁻¹ * 1 + A⁻¹ ^ 2 * A = ρ.energy p - A⁻¹ := by field_simp; ring
    rw [hid] at hb
    linarith
  apply le_antisymm
  · have ha : (A⁻¹ • K).eval I.mu = 1 := by simp only [eval_smul, smul_eq_mul, heval, inv_mul_cancel₀ hA.ne']
    have hl := ρ.christoffel_le k (A⁻¹ • K) ((natDegree_smul_le _ _).trans (kernel_degree S w k)) ha
    rw [energy_smul, he] at hl
    exact hl.trans_eq (by change A⁻¹ ^ 2 * A = A⁻¹; field_simp [hA.ne'])
  · apply le_csInf (ρ.christoffelValues_nonempty k)
    rintro _ ⟨p, hp, hp1, rfl⟩
    exact hmin p hp hp1

end
end InexactRealizations.Averages.SpectralLaw
