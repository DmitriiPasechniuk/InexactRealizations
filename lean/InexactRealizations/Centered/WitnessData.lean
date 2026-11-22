import InexactRealizations.Centered.Moments
import InexactRealizations.Budgets.FiniteSpectrum
import InexactRealizations.Probability.Signs

/-! A centered relative-error witness with deterministic amplitudes.
The noise axes are orthogonal to the initial spectral mode, so that mode
remains nominal in every actual query. 
-/
namespace InexactRealizations.Centered.Witness
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators
variable {N : ℕ}

abbrev Space (N : ℕ) := EuclideanSpace ℝ (Fin (N + 1))
def axis (i : Fin (N + 1)) : Space N := EuclideanSpace.single i 1

theorem axis_norm (i : Fin (N + 1)) : ‖axis i‖ = 1 := by simp [axis]

def hessian (lambda : Fin N → ℝ) (nu : ℝ) : Space N →ₗ[ℝ] Space N :=
  InexactRealizations.Budgets.FiniteSpectrum.diagonal (Fin.snoc lambda nu)

theorem hessian_admissible (I : InexactRealizations.Operators.SpectralInterval) (lambda : Fin N → ℝ) (nu : ℝ)
    (hlam : ∀ s, lambda s ∈ Set.Icc I.mu I.L) (hnu : nu ∈ Set.Icc I.mu I.L) :
    InexactRealizations.Analysis.Admissible I (hessian lambda nu) := by
  apply InexactRealizations.Budgets.FiniteSpectrum.diagonal_admissible
  intro i
  refine Fin.lastCases ?_ (fun s ↦ ?_) i
  · simpa only [Fin.snoc_last] using hnu
  · simpa only [Fin.snoc_castSucc] using hlam s

def initial (N : ℕ) (r : ℝ) : Space N := r • axis (Fin.last N)

theorem initial_norm (r : ℝ) (hr : 0 ≤ r) : ‖initial N r‖ = r := by
  rw [initial, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, axis_norm, mul_one]

def amplitude (h : InexactRealizations.History N) (nu r t : ℝ) (s : Fin N) : ℝ :=
  t * r * (h.query s).eval nu

def noiseMap (h : InexactRealizations.History N) (nu r t : ℝ) (s : Fin N) : ℝ →L[ℝ] Space N :=
  ContinuousLinearMap.toSpanSingleton ℝ (amplitude h nu r t s • axis s.castSucc)

def stream (h : InexactRealizations.History N) (nu r t : ℝ) (s : ℕ) (ω : Fin N → Bool) : Space N :=
  InexactRealizations.Probability.responseExtension (noiseMap h nu r t) s (InexactRealizations.Probability.Signs.stream N 1 s ω)

theorem stream_at (h : InexactRealizations.History N) (nu r t : ℝ) (s : Fin N) (ω : Fin N → Bool) :
    stream h nu r t s.val ω = InexactRealizations.Probability.Signs.error 1 s ω •
      (amplitude h nu r t s • axis s.castSucc) := by
  simp only [stream, InexactRealizations.Probability.responseExtension, s.isLt, dite_true,
    InexactRealizations.Probability.Signs.stream, ContinuousLinearMap.toSpanSingleton_apply, noiseMap]

theorem martingale (h : InexactRealizations.History N) (nu r t : ℝ) :
    InexactRealizations.Probability.MartingaleDifferences N (InexactRealizations.Probability.Signs.past N 1)
      (stream h nu r t) (InexactRealizations.Probability.Signs.law N) :=
  (InexactRealizations.Probability.Signs.martingale N 1).map (InexactRealizations.Probability.responseExtension (noiseMap h nu r t))

theorem stream_last_zero (h : InexactRealizations.History N) (nu r t : ℝ) (s : Fin N) (ω : Fin N → Bool) :
    stream h nu r t s.val ω (Fin.last N) = 0 := by
  rw [stream_at]
  simp [axis, (Fin.castSucc_ne_last s).symm]

theorem stream_norm_sq (h : InexactRealizations.History N) (nu r t : ℝ) (s : Fin N) (ω : Fin N → Bool) :
    ‖stream h nu r t s.val ω‖ ^ 2 = amplitude h nu r t s ^ 2 := by
  rw [stream_at, norm_smul, norm_smul, axis_norm, mul_one, mul_pow]
  have hh := InexactRealizations.Probability.Signs.error_norm_sq (N := N) 1 s ω
  rw [hh]
  simp only [Real.norm_eq_abs, sq_abs, one_pow, one_mul]

theorem query_last (h : InexactRealizations.History N) (lambda : Fin N → ℝ) (nu r t : ℝ)
    (s : Fin N) (ω : Fin N → Bool) :
    randomQuery h (hessian lambda nu) (initial N r) (stream h nu r t) s ω (Fin.last N) =
      r * (h.query s).eval nu := by
  have hh := congrArg (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin (N + 1) ↦ ℝ) (Fin.last N))
    (query_response h s (hessian lambda nu)
    (initial N r) (fun j ↦ stream h nu r t j.val ω) (h.run _ _ _))
  simp only [map_add, map_sum, PiLp.proj_apply, hessian,
    InexactRealizations.Budgets.FiniteSpectrum.diagonal_polynomial, Fin.snoc_last,
    stream_last_zero, mul_zero, Finset.sum_const_zero, add_zero, initial, PiLp.smul_apply,
    axis, PiLp.single_apply, ite_true, smul_eq_mul, mul_one] at hh
  exact hh.trans (mul_comm _ _)

theorem relative_variance (h : InexactRealizations.History N) (lambda : Fin N → ℝ) (nu r t : ℝ) :
    RelativeVariance h (hessian lambda nu) (initial N r) (stream h nu r t)
      (InexactRealizations.Probability.Signs.past N 1) (InexactRealizations.Probability.Signs.law N) t := by
  intro s
  have he : (fun ω ↦ ‖stream h nu r t s.val ω‖ ^ 2) = fun _ ↦ amplitude h nu r t s ^ 2 :=
    funext (stream_norm_sq h nu r t s)
  rw [he, condExp_const ((InexactRealizations.Probability.Signs.past N 1).le s.val)]
  apply Filter.Eventually.of_forall
  intro ω
  have hb := PiLp.norm_apply_le (randomQuery h (hessian lambda nu) (initial N r) (stream h nu r t) s ω) (Fin.last N)
  rw [query_last, Real.norm_eq_abs] at hb
  have hs := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hb
  rw [sq_abs] at hs
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg t)
  unfold amplitude
  convert hh using 1; ring

end
end InexactRealizations.Centered.Witness
