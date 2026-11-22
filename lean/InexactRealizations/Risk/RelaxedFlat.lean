import InexactRealizations.History.OutputRelaxation
import InexactRealizations.Probability.InitialStateBounds
import InexactRealizations.Flat.Optima
import InexactRealizations.Risk.JournalQuadratic

/-! The actual shrunk Flat output in current Theorem3.2. Its terminal and
responses give the stated risk bound even for an F0-measurable random
minimizer, without independence assumptions on the martingale errors. 
-/
namespace InexactRealizations.Risk.AllLinear
noncomputable section
open Polynomial Set MeasureTheory Filter
open scoped BigOperators

theorem epsilon_unit (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 0 < N) :
    0 < I.epsilon N ∧ I.epsilon N < 1 := by
  refine ⟨one_div_pos.mpr (I.den_pos N), ?_⟩
  apply (div_lt_one (I.den_pos N)).mpr
  exact Polynomial.Chebyshev.one_lt_eval_T_real (by exact_mod_cast hN.ne') I.eta_gt_one

def relaxedFlat (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (ω : ℝ) : InexactRealizations.History N :=
  (InexactRealizations.Flat.history I N hN).relax ω

def relaxedTerminalBound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (ω : ℝ) : ℝ :=
  1 - ω + ω * I.epsilon N

theorem relaxedTerminalBound_nonneg (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    {ω : ℝ} (hω : ω ∈ Icc 0 1) : 0 ≤ relaxedTerminalBound I N ω :=
  add_nonneg (sub_nonneg.mpr hω.2) (mul_nonneg hω.1 (one_div_pos.mpr (I.den_pos N)).le)

theorem relaxedFlat_terminal_bound (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    {ω : ℝ} (hω : ω ∈ Icc 0 1) {x : ℝ} (hx : x ∈ Icc I.mu I.L) :
    |((relaxedFlat I N hN ω).terminal).eval x| ≤ relaxedTerminalBound I N ω := by
  have ht : (InexactRealizations.Flat.history I N hN).terminal = I.residual N := InexactRealizations.Flat.history_exact I N hN
  change |(((InexactRealizations.Flat.history I N hN).relax ω).terminal).eval x| ≤ _
  rw [InexactRealizations.History.relax_terminal, ht]
  simp only [eval_add, eval_sub, eval_one, eval_mul, eval_C]
  calc
    _ ≤ |1 - ω| + |ω * (I.residual N).eval x| := abs_add_le _ _
    _ = (1 - ω) + ω * |(I.residual N).eval x| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hω.2), abs_mul, abs_of_nonneg hω.1]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (I.residual_abs_le N hx) hω.1)

theorem relaxedFlat_response_bounds (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    {ω : ℝ} (hω : 0 ≤ ω) :
    InexactRealizations.Risk.ResponseBounds (relaxedFlat I N hN ω) I
      (fun _ ↦ ω * (InexactRealizations.Lower.additiveScale I N / N)) := by
  refine ⟨fun _ ↦ mul_nonneg hω (div_nonneg (InexactRealizations.Risk.additiveScale_nonneg I N) (Nat.cast_nonneg N)), ?_⟩
  intro s x hx
  change |(((InexactRealizations.Flat.history I N hN).relax ω).response s).eval x| ≤ _
  rw [InexactRealizations.History.relax_response]
  simp only [eval_mul, eval_C, abs_mul, abs_of_nonneg hω]
  exact mul_le_mul_of_nonneg_left (InexactRealizations.Flat.response_abs_le I N hN s hx) hω

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {N : ℕ} {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E} [IsProbabilityMeasure μ]

theorem relaxedFlat_random_mse_upper (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H)
    (V : Ω → E) (hV : StronglyMeasurable[𝓕 0] V) (hV₂ : MemLp V 2 μ)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ)
    (r σ : ℝ) (hr : (∫ ω, ‖V ω‖ ^ 2 ∂μ) ≤ r ^ 2)
    (hσ : ∀ s, s < N → μ[fun ω ↦ ‖w s ω‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ ↦ σ ^ 2)
    {ω : ℝ} (hω : ω ∈ Icc 0 1) :
    (∫ ξ, ‖(relaxedFlat I N hN ω).stochasticOutput H (V ξ) w ξ‖ ^ 2 ∂μ) ≤
      objective (r ^ 2) (σ ^ 2 / (I.mu ^ 2 * N)) (relaxedTerminalBound I N ω) := by
  have hh := InexactRealizations.History.integral_randomInitial_stochasticOutput_le (relaxedFlat I N hN ω)
    I H hH V hV hV₂ hw r σ (relaxedTerminalBound I N ω) (relaxedTerminalBound_nonneg I N hω)
    (fun _ hx ↦ relaxedFlat_terminal_bound I N hN hω hx)
    (fun _ ↦ ω * (InexactRealizations.Lower.additiveScale I N / N)) (relaxedFlat_response_bounds I N hN hω.1) hr hσ
  apply hh.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold objective relaxedTerminalBound InexactRealizations.Lower.additiveScale
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp [I.mu_pos.ne', hn]
  ring

theorem shrunkFlat_random_mse_upper (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H)
    (V : Ω → E) (hV : StronglyMeasurable[𝓕 0] V) (hV₂ : MemLp V 2 μ)
    (hw : InexactRealizations.Probability.MartingaleDifferences N 𝓕 w μ)
    (r σ : ℝ) (hr : (∫ ξ, ‖V ξ‖ ^ 2 ∂μ) ≤ r ^ 2)
    (hσ : ∀ s, s < N → μ[fun ξ ↦ ‖w s ξ‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ ↦ σ ^ 2) :
    (∫ ξ, ‖(relaxedFlat I N hN (shrink (r ^ 2) (σ ^ 2 / (I.mu ^ 2 * N)) (I.epsilon N))).stochasticOutput
      H (V ξ) w ξ‖ ^ 2 ∂μ) ≤ value (r ^ 2) (σ ^ 2 / (I.mu ^ 2 * N)) (I.epsilon N) := by
  have he := epsilon_unit I (by omega : 0 < N)
  have hB : 0 ≤ σ ^ 2 / (I.mu ^ 2 * N) := by positivity
  have hω : shrink (r ^ 2) (σ ^ 2 / (I.mu ^ 2 * N)) (I.epsilon N) ∈ Icc 0 1 :=
    ⟨shrink_nonneg (sq_nonneg r) hB he.2, min_le_left _ _⟩
  have hh := relaxedFlat_random_mse_upper I hN H hH V hV hV₂ hw r σ hr hσ hω
  apply hh.trans_eq
  unfold relaxedTerminalBound
  have hc (a e : ℝ) : 1 - a + a * e = 1 - a * (1 - e) := by ring
  rw [hc]
  exact shrink_attains (sq_nonneg r) hB he.1 he.2

end
end InexactRealizations.Risk.AllLinear
