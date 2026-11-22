import InexactRealizations.Gains.Witness
import InexactRealizations.Risk.Suprema

/-! Current Theorem3.2: the bias-maximizing eigenspace and the noisy lower
endpoint coexist in one actual two-dimensional martingale oracle model. 
-/
namespace InexactRealizations.Risk.AllLinear
noncomputable section
open Polynomial Set MeasureTheory Filter
open InexactRealizations.Gains
open scoped BigOperators
variable {N : ℕ}

def axis (i : Fin 2) : ℝ →ₗ[ℝ] WitnessSpace where
  toFun a := WithLp.toLp 2 (Pi.single i a)
  map_add' a b := by ext j; by_cases hj : j = i <;> simp [hj]
  map_smul' a b := by ext j; by_cases hj : j = i <;> simp [hj]

@[simp] theorem axis_apply (i j : Fin 2) (a : ℝ) : axis i a j = if j = i then a else 0 := by
  simp [axis]

theorem axis_norm_sq (i : Fin 2) (a : ℝ) : ‖axis i a‖ ^ 2 = a ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [axis_apply, Real.norm_eq_abs, sq_abs]
  simp

theorem axis_norm (i : Fin 2) (a : ℝ) : ‖axis i a‖ = |a| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg a)).mp
  rw [axis_norm_sq, sq_abs]

theorem diagonal_axis (d : Fin 2 → ℝ) (p : ℝ[X]) (i : Fin 2) (a : ℝ) :
    (aeval (diagonalOperator d) p) (axis i a) = axis i (p.eval (d i) * a) := by
  ext j
  rw [diagonalOperator_polynomial, axis_apply, axis_apply]
  by_cases hj : j = i
  · subst j; simp
  · simp only [ite_eq_right hj, mul_zero]

def axisCLM (i : Fin 2) : ℝ →L[ℝ] WitnessSpace := (axis i).toContinuousLinearMap

theorem twoMode_mse (h : InexactRealizations.History N) (x y r σ : ℝ) :
    (∫ ω, ‖h.stochasticOutput (diagonalOperator ![x, y]) (axis 0 r)
      (fun s ω ↦ axis 1 (InexactRealizations.Probability.Signs.stream N σ s ω)) ω‖ ^ 2
        ∂InexactRealizations.Probability.Signs.law N) =
      r ^ 2 * h.terminal.eval x ^ 2 + σ ^ 2 * ∑ s, (h.response s).eval y ^ 2 := by
  have hw : InexactRealizations.Probability.MartingaleDifferences N (InexactRealizations.Probability.Signs.past N σ)
      (fun s ω ↦ axis 1 (InexactRealizations.Probability.Signs.stream N σ s ω)) (InexactRealizations.Probability.Signs.law N) :=
    (InexactRealizations.Probability.Signs.martingale N σ).map (fun _ ↦ axisCLM 1)
  rw [h.integral_stochasticOutput_norm_sq _ _ hw, diagonal_axis, axis_norm_sq]
  simp only [Fin.isValue, Matrix.cons_val_zero]
  have hterm (s : Fin N) :
      (∫ ω, ‖h.responseOperator (diagonalOperator ![x, y]) s
        (axis 1 (InexactRealizations.Probability.Signs.stream N σ s.val ω))‖ ^ 2 ∂InexactRealizations.Probability.Signs.law N) =
        (h.response s).eval y ^ 2 * σ ^ 2 := by
    have he (ω : Fin N → Bool) :
        ‖h.responseOperator (diagonalOperator ![x, y]) s
          (axis 1 (InexactRealizations.Probability.Signs.stream N σ s.val ω))‖ ^ 2 =
          (h.response s).eval y ^ 2 * σ ^ 2 := by
      rw [InexactRealizations.History.responseOperator_apply, diagonal_axis, axis_norm_sq, mul_pow]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, InexactRealizations.Probability.Signs.stream,
        dite_eq_left s.isLt, InexactRealizations.Probability.Signs.error, InexactRealizations.Probability.Signs.value]
      split_ifs <;> ring
    simp_rw [he]
    simp
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  ring

theorem mseBound_twoMode_lower {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) {r σ C : ℝ} (hr : 0 ≤ r)
    (hb : InexactRealizations.Risk.MseBound h I r σ C) {x : ℝ} (hx : x ∈ Icc I.mu I.L) :
    r ^ 2 * h.terminal.eval x ^ 2 + σ ^ 2 * ∑ s, (h.response s).eval I.mu ^ 2 ≤ C := by
  have hw : InexactRealizations.Probability.MartingaleDifferences N (InexactRealizations.Probability.Signs.past N σ)
      (fun s ω ↦ axis 1 (InexactRealizations.Probability.Signs.stream N σ s ω)) (InexactRealizations.Probability.Signs.law N) :=
    (InexactRealizations.Probability.Signs.martingale N σ).map (fun _ ↦ axisCLM 1)
  have hv : ∀ s, s < N →
      (InexactRealizations.Probability.Signs.law N)[fun ω ↦
        ‖axis 1 (InexactRealizations.Probability.Signs.stream N σ s ω)‖ ^ 2 | InexactRealizations.Probability.Signs.past N σ s] ≤ᵐ[
          InexactRealizations.Probability.Signs.law N] fun _ ↦ σ ^ 2 := by
    intro s hs
    have he : (fun ω ↦ ‖axis 1 (InexactRealizations.Probability.Signs.stream N σ s ω)‖ ^ 2) =
        fun ω ↦ ‖InexactRealizations.Probability.Signs.stream N σ s ω‖ ^ 2 := by
      funext ω
      rw [axis_norm_sq, Real.norm_eq_abs, sq_abs]
    rw [he, InexactRealizations.Probability.Signs.conditional_variance N σ s hs]
  have hh := hb WitnessSpace (Fin N → Bool) (InexactRealizations.Probability.Signs.law N)
    (InexactRealizations.Probability.Signs.past N σ) _ hw hv (diagonalOperator ![x, I.mu])
    (diagonalOperator_admissible I _ (by
      intro i; fin_cases i
      · exact hx
      · exact ⟨le_rfl, I.mu_lt_L.le⟩)) (axis 0 r) (by rw [axis_norm, abs_of_nonneg hr])
  exact (twoMode_mse h x I.mu r σ).symm.trans_le hh

end
end InexactRealizations.Risk.AllLinear
