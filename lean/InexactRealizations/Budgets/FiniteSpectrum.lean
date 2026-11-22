import InexactRealizations.Budgets.Support
import InexactRealizations.Analysis.Spectral

/-! Finitely supported spectral probability distributions, with arbitrary
support size, repeated points and zero weights. Both directions of their
correspondence with actual finite-dimensional spectral measures are proved. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial
open scoped BigOperators

structure FiniteSpectrum (I : InexactRealizations.Operators.SpectralInterval) where
  size : ℕ
  point : Fin size → ℝ
  point_mem : ∀ i, point i ∈ Set.Icc I.mu I.L
  weight : Fin size → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  total : ∑ i, weight i = 1

namespace FiniteSpectrum
variable {I : InexactRealizations.Operators.SpectralInterval}

def moment (alpha : FiniteSpectrum I) (p : ℝ[X]) : ℝ :=
  ∑ i, alpha.weight i * p.eval (alpha.point i) ^ 2

def polynomialNorm (alpha : FiniteSpectrum I) (p : ℝ[X]) : ℝ :=
  Real.sqrt (alpha.moment p)

theorem moment_nonneg (alpha : FiniteSpectrum I) (p : ℝ[X]) : 0 ≤ alpha.moment p :=
  Finset.sum_nonneg (fun i _ ↦ mul_nonneg (alpha.nonneg i) (sq_nonneg _))

theorem polynomialNorm_nonneg (alpha : FiniteSpectrum I) (p : ℝ[X]) :
    0 ≤ alpha.polynomialNorm p := Real.sqrt_nonneg _

def vector (alpha : FiniteSpectrum I) : EuclideanSpace ℝ (Fin alpha.size) :=
  WithLp.toLp 2 (fun i ↦ Real.sqrt (alpha.weight i))

def diagonal {n : ℕ} (d : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun v := WithLp.toLp 2 (fun i ↦ d i * v i)
  map_add' v w := by ext i; simp [mul_add]
  map_smul' c v := by ext i; simp; ring

@[simp] theorem diagonal_apply {n : ℕ} (d : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) : diagonal d v i = d i * v i := rfl

theorem diagonal_symmetric {n : ℕ} (d : Fin n → ℝ) : (diagonal d).IsSymmetric := by
  intro v w
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, diagonal_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem diagonal_admissible {n : ℕ} (d : Fin n → ℝ)
    (hd : ∀ i, d i ∈ Set.Icc I.mu I.L) : InexactRealizations.Analysis.Admissible I (diagonal d) := by
  refine ⟨diagonal_symmetric d, ?_⟩
  intro lam hlam
  obtain ⟨v, hv⟩ := hlam.exists_hasEigenvector
  have he := hv.apply_eq_smul
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hv.2 (by ext i; exact hn i)
  have hei := congrArg (fun w : EuclideanSpace ℝ (Fin n) ↦ w i) he
  simp only [diagonal_apply, PiLp.smul_apply, smul_eq_mul] at hei
  have hl : d i = lam := mul_right_cancel₀ hi hei
  simpa only [hl] using hd i

theorem diagonal_polynomial {n : ℕ} (d : Fin n → ℝ) (p : ℝ[X])
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ((aeval (diagonal d) p) v) i = p.eval (d i) * v i := by
  have hpow (k : ℕ) (w : EuclideanSpace ℝ (Fin n)) :
      (((diagonal d) ^ k) w) i = (d i) ^ k * w i := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Module.End.mul_apply, diagonal_apply, ih]; ring
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, PiLp.add_apply, hp, hq, eval_add, add_mul]
  | monomial k a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      PiLp.smul_apply, smul_eq_mul, eval_monomial, hpow]
    ring

theorem vector_norm (alpha : FiniteSpectrum I) : ‖alpha.vector‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vector, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (alpha.nonneg _), one_pow]
  exact alpha.total

theorem polynomialNorm_eq_action (alpha : FiniteSpectrum I) (p : ℝ[X]) :
    alpha.polynomialNorm p = ‖(aeval (diagonal alpha.point) p) alpha.vector‖ := by
  apply (sq_eq_sq₀ (alpha.polynomialNorm_nonneg p) (norm_nonneg _)).mp
  rw [polynomialNorm, Real.sq_sqrt (alpha.moment_nonneg p), EuclideanSpace.norm_sq_eq]
  simp only [diagonal_polynomial, Real.norm_eq_abs, sq_abs, mul_pow, vector,
    Real.sq_sqrt (alpha.nonneg _), moment]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def ofVector (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (e : E) (he : ‖e‖ = 1) :
    FiniteSpectrum I where
  size := Module.finrank ℝ E
  point := hH.1.eigenvalues rfl
  point_mem i := hH.2 _ (hH.1.hasEigenvalue_eigenvalues rfl i)
  weight i := ((hH.1.eigenvectorBasis rfl).repr e i) ^ 2
  nonneg _ := sq_nonneg _
  total := by
    have hh := EuclideanSpace.norm_sq_eq ((hH.1.eigenvectorBasis rfl).repr e)
    rw [(hH.1.eigenvectorBasis rfl).repr.norm_map, he] at hh
    simpa only [Real.norm_eq_abs, sq_abs, one_pow] using hh.symm

theorem ofVector_polynomialNorm (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H)
    (e : E) (he : ‖e‖ = 1) (p : ℝ[X]) :
    (ofVector H hH e he).polynomialNorm p = ‖(aeval H p) e‖ := by
  apply (sq_eq_sq₀ (polynomialNorm_nonneg _ _) (norm_nonneg _)).mp
  rw [polynomialNorm, Real.sq_sqrt (moment_nonneg _ _),
    ← (hH.1.eigenvectorBasis rfl).repr.norm_map ((aeval H p) e), EuclideanSpace.norm_sq_eq]
  simp only [InexactRealizations.Analysis.polynomial_spectral_coordinates, Real.norm_eq_abs,
    sq_abs, mul_pow, moment, ofVector]
  apply Finset.sum_congr rfl
  intro i _
  ring

end FiniteSpectrum
end
end InexactRealizations.Budgets
