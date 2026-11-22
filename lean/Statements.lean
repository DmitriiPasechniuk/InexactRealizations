import InexactRealizations.Accuracy.Uncompensated.Journal
import InexactRealizations.Algorithms.JournalFlat
import InexactRealizations.Averages.Journal
import InexactRealizations.Balanced.Optima
import InexactRealizations.Budgets.OddGap
import InexactRealizations.Channel.SignalFiniteNoise
import InexactRealizations.Comparisons.Competitors.DFBHistory
import InexactRealizations.Comparisons.Competitors.LF
import InexactRealizations.Models.CycleChannel
import InexactRealizations.Probability.DitherHistory
import InexactRealizations.Prose.IsotropicAverage
import InexactRealizations.Prose.RawInitial
import InexactRealizations.Prose.RungeKutta
import InexactRealizations.Prose.TailExecution
import InexactRealizations.Prose.TailRates
import InexactRealizations.Prose.UniformRemainders
import InexactRealizations.Risk.JournalAdaptive
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Optimal Realizations of the Chebyshev Iteration with Inexact Residuals

Formal statements of the numbered results of the article and of the mathematical claims of its
text (labelled displays, figures and paragraphs), in printed order. Each block names the printed
statement (number, title and page of the journal version) or the place of the claim, and gives the
Lean theorems that formalize it; the comments explain the Lean names and record any difference
from the printed wording.

Printed convention: `α_s` is the stepsize, `β_s` momentum, `ω_s` the oracle
error, `π_s` the nominal query polynomial with `π_s(0) = 1`, and `Φ_s` its
physical terminal response: `K_s(λ,ν) = Φ_s(λ)π_s(ν)`. Averaging/output
weights are `ϖ_s`, `ϖ`; the library's coefficient names `omega` are retained.
-/

namespace Article
noncomputable section

section Part1

open Polynomial Filter Asymptotics MeasureTheory
open scoped BigOperators ENNReal NNReal Topology
universe u_1 u_2 u_3

section
/-! ## Introduction, p. 2 (tail averaging and exponential relative amplification)

The actual tail average uses the last half of one Prefix trajectory. Positive noise is the nonzero-noise domain of the stated two-sided rate. The Flat penalty is uniform over all call budgets and positive initial radii.
-/

theorem text_tail_prefix_mse_rate : ∀ (I : InexactRealizations.Operators.SpectralInterval) (r σ : ℝ),
  0 ≤ r →
    0 < σ →
      ∃ c C,
        0 < c ∧
          0 < C ∧
            ∀ᶠ (N : ℕ) in Filter.atTop,
              c / ↑N ≤ InexactRealizations.Risk.mseRisk (InexactRealizations.Prose.Tail.history I N) I r σ ∧
                InexactRealizations.Risk.mseRisk (InexactRealizations.Prose.Tail.history I N) I r σ ≤ C / ↑N :=
  @InexactRealizations.Prose.Tail.mse_one_over_N

theorem text_flat_relative_exponential : ∀ (I : InexactRealizations.Operators.SpectralInterval),
  ∃ b,
    1 < b ∧
      ∀ᶠ (N : ℕ) in Filter.atTop,
        ∀ (hN : 2 ≤ N) (p : ENNReal),
          1 ≤ p →
            ∀ (r : ℝ),
              0 < r →
                b ^ N * InexactRealizations.Budgets.localRelativeGain p (InexactRealizations.Balanced.history I N hN) I r ≤
                  InexactRealizations.Budgets.localRelativeGain p (InexactRealizations.Flat.history I N hN) I r :=
  @InexactRealizations.Prose.flat_exponential_vs_balanced

end



section
/-! ## Figure 1, p. 3 (normalized corner profiles)

The computed curves and chosen parameters are excluded. The exact mean-one
normalizations hold for every actual history; Flat has a constant response
profile and Balanced has a constant product profile at every even horizon,
including the printed horizon 32.
-/
private theorem aux1_additive_scale_pos (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    0 < InexactRealizations.Lower.additiveScale I N := by
  have hd : 1 < I.den N := by
    simpa using InexactRealizations.Algorithms.AveragedBalanced.den_strictMono I hN
  have he : I.epsilon N < 1 := (div_lt_one (I.den_pos N)).mpr hd
  exact div_pos (sub_pos.mpr he) I.mu_pos

theorem figure_1_response_mean {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (he : h.terminal = I.residual N) (hN : 0 < N) :
    (N : ℝ)⁻¹ * (∑ j, (-(N : ℝ) / ((1 - I.epsilon N) / I.mu)) * (h.response j).eval I.mu) = 1 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hS := (aux1_additive_scale_pos I N hN).ne'
  change (N : ℝ)⁻¹ * (∑ j, (-(N : ℝ) / InexactRealizations.Lower.additiveScale I N) * (h.response j).eval I.mu) = 1
  rw [← Finset.mul_sum, InexactRealizations.Lower.response_sum_mu h I he]
  field_simp

theorem figure_1_product_mean {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (he : h.terminal = I.residual N) (hN : 0 < N) :
    (N : ℝ)⁻¹ * (∑ j, (-(N : ℝ) / (2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta)) *
      ((h.response j).eval I.mu * (h.query j).eval I.mu)) = 1 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hD : InexactRealizations.Lower.derivativeScale I N ≠ 0 := by
    have hp := one_div_pos.mpr (I.den_pos N)
    have hd := I.delta_pos
    unfold InexactRealizations.Lower.derivativeScale
    positivity
  change (N : ℝ)⁻¹ * (∑ j, (-(N : ℝ) / InexactRealizations.Lower.derivativeScale I N) *
    ((h.response j).eval I.mu * (h.query j).eval I.mu)) = 1
  have hs := InexactRealizations.Lower.kernel_sum_mu h I he
  change (∑ j, (h.response j).eval I.mu * (h.query j).eval I.mu) =
    -InexactRealizations.Lower.derivativeScale I N at hs
  rw [← Finset.mul_sum, hs]
  field_simp

theorem figure_1_flat_constant (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (hN : 2 ≤ N) (j : Fin N) :
    ((InexactRealizations.Flat.history I N hN).response j).eval I.mu = -((1 - I.epsilon N) / I.mu) / N :=
by
  simpa only [InexactRealizations.Lower.additiveScale, neg_div] using InexactRealizations.Flat.response_mu I N hN j

theorem figure_1_balanced_constant (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (hN : 2 ≤ N) (hEven : Even N) (j : Fin N) :
    ((InexactRealizations.Balanced.history I N hN).response j).eval I.mu *
      ((InexactRealizations.Balanced.history I N hN).query j).eval I.mu =
      -(2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / N := by
  rw [InexactRealizations.Balanced.response_endpoint, InexactRealizations.Balanced.query_endpoint_physical, neg_mul,
    InexactRealizations.Balanced.bound_product I hN j.isLt]
  simp only [InexactRealizations.Balanced.classMass, hEven, ite_true]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : N ≠ 0)
  field_simp
  ring
end

section
/-! ## Section 2, p. 4 (spectral notation and the causal oracle)

The error coordinate is `x - x^⋆`. `I.epsilon N` is the printed `ε_N^⋆`,
and `I.residual N` is `p_N^⋆`. The canonical `oracleQuery`, `oracleAnswers`
and `oracleOutput` are the article's actual y, g and x in that coordinate.
Coefficients with j >= s vanish, so the finite sums below equal the printed
strict-prefix sums. The data structure imposes no sign or memory bound.
-/
theorem notation_interval (I : InexactRealizations.Operators.SpectralInterval) :
    0 < I.mu ∧ I.mu < I.L ∧ I.delta = I.L - I.mu ∧
      I.eta = (I.L + I.mu) / I.delta ∧ I.kappa = I.L / I.mu :=
  ⟨I.mu_pos, I.mu_lt_L, rfl, rfl, rfl⟩

theorem notation_terminal (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (x : ℝ) :
    I.epsilon N = 1 / (Polynomial.Chebyshev.T ℝ N).eval I.eta ∧
      (I.residual N).eval x = I.epsilon N *
        (Polynomial.Chebyshev.T ℝ N).eval (I.eta - 2 * x / I.delta) := by
  refine ⟨rfl, ?_⟩
  rw [I.residual_eval, InexactRealizations.Operators.SpectralInterval.z_eq]
  have hz : I.eta - 2 / I.delta * x = I.eta - 2 * x / I.delta := by ring
  rw [hz]
  unfold InexactRealizations.Operators.SpectralInterval.epsilon
  ring

theorem text_terminal_degree_and_normalization {N : ℕ} (h : InexactRealizations.History N) :
    h.terminal.natDegree ≤ N ∧ h.terminal.eval 0 = 1 :=
  ⟨h.terminal_natDegree_le, h.terminal_eval_zero⟩


end


section StrictGap1

open Polynomial Polynomial.Chebyshev Filter
open scoped Topology

section
/-! ## Section 2, p. 4 (preliminary Chebyshev identities)

The polynomials are the actual first- and second-kind Chebyshev
polynomials. Natural degrees are embedded in the integer indexing used by
Mathlib; this also gives the printed zero predecessor U at degree -1.
The sine formula is stated as a global multiplied identity, as a quotient
where its denominator is nonzero, and with its continuous endpoint
extensions. No value is assigned to the quotient 0/0.
-/

theorem text_chebyshev_T_recurrence (n : ℕ) :
    T ℝ (n + 2) = 2 * X * T ℝ (n + 1) - T ℝ n := by
  simp

theorem text_chebyshev_U_recurrence (n : ℕ) :
    U ℝ (n + 2) = 2 * X * U ℝ (n + 1) - U ℝ n := by
  simp

theorem text_chebyshev_T_at_one (n : ℕ) : (T ℝ n).eval 1 = 1 :=
  T_eval_one ℝ n

theorem text_chebyshev_U_at_one (n : ℕ) : (U ℝ n).eval 1 = (n : ℝ) + 1 := by
  simp

theorem text_chebyshev_U_at_neg_one (n : ℕ) :
    (U ℝ n).eval (-1) = (-1 : ℝ) ^ n * ((n : ℝ) + 1) := by
  simp

theorem text_chebyshev_U_predecessor : U ℝ (-1) = 0 := by simp

theorem text_chebyshev_T_derivative (n : ℕ) :
    (T ℝ n).derivative = C (n : ℝ) * U ℝ ((n : ℤ) - 1) := by
  simpa using T_derivative_eq_U (R := ℝ) (n : ℤ)

theorem text_chebyshev_T_interval_bound (n : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) : |(T ℝ n).eval x| ≤ 1 :=
  abs_eval_T_real_le_one n (abs_le.mpr hx)

theorem text_chebyshev_T_cosine (n : ℕ) (t : ℝ) :
    (T ℝ n).eval (Real.cos t) = Real.cos ((n : ℝ) * t) := by
  simp

theorem text_chebyshev_U_sine_multiplied (n : ℕ) (t : ℝ) :
    (U ℝ n).eval (Real.cos t) * Real.sin t = Real.sin (((n : ℝ) + 1) * t) := by
  simp

theorem text_chebyshev_U_sine_quotient (n : ℕ) (t : ℝ) (ht : Real.sin t ≠ 0) :
    (U ℝ n).eval (Real.cos t) = Real.sin (((n : ℝ) + 1) * t) / Real.sin t :=
  (eq_div_iff ht).mpr (text_chebyshev_U_sine_multiplied n t)

theorem text_chebyshev_U_cosine_continuous (n : ℕ) :
    Continuous (fun t : ℝ => (U ℝ n).eval (Real.cos t)) := by fun_prop

theorem text_chebyshev_U_zero_extension (n : ℕ) :
    Tendsto (fun t : ℝ => (U ℝ n).eval (Real.cos t)) (𝓝 0) (𝓝 ((n : ℝ) + 1)) := by
  simpa using (text_chebyshev_U_cosine_continuous n).continuousAt (x := 0) |>.tendsto

theorem text_chebyshev_U_pi_extension (n : ℕ) :
    Tendsto (fun t : ℝ => (U ℝ n).eval (Real.cos t)) (𝓝 Real.pi)
      (𝓝 ((-1 : ℝ) ^ n * ((n : ℝ) + 1))) := by
  have hh := (text_chebyshev_U_cosine_continuous n).continuousAt (x := Real.pi) |>.tendsto
  simpa only [Real.cos_pi, text_chebyshev_U_at_neg_one] using hh

theorem text_chebyshev_U_quotient_zero_limit (n : ℕ) :
    Tendsto (fun t : ℝ => Real.sin (((n : ℝ) + 1) * t) / Real.sin t)
      (𝓝[{t : ℝ | Real.sin t ≠ 0}] 0) (𝓝 ((n : ℝ) + 1)) := by
  apply (text_chebyshev_U_zero_extension n).mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact text_chebyshev_U_sine_quotient n t ht

theorem text_chebyshev_U_quotient_pi_limit (n : ℕ) :
    Tendsto (fun t : ℝ => Real.sin (((n : ℝ) + 1) * t) / Real.sin t)
      (𝓝[{t : ℝ | Real.sin t ≠ 0}] Real.pi)
      (𝓝 ((-1 : ℝ) ^ n * ((n : ℝ) + 1))) := by
  apply (text_chebyshev_U_pi_extension n).mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact text_chebyshev_U_sine_quotient n t ht

end
end StrictGap1

section
/-! ## Section 2, p. 4, Display (1) (normalized minimax terminal)

`I` is the printed interval with 0 < mu < L. The theorem gives the actual normalized Chebyshev polynomial, its endpoint attainment and the full minimax problem over all normalized real polynomials.
-/

theorem display_1_minimax : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  IsLeast {M | ∃ p, p.degree ≤ ↑N ∧ Polynomial.eval 0 p = 1 ∧ ∀ lam ∈ Set.Icc I.mu I.L, |Polynomial.eval lam p| ≤ M}
    (I.epsilon N) :=
  @InexactRealizations.Properties.terminal_minimax

theorem display_1_attainment : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  (I.residual N).degree ≤ ↑N ∧
    Polynomial.eval 0 (I.residual N) = 1 ∧
      (∀ lam ∈ Set.Icc I.mu I.L, |Polynomial.eval lam (I.residual N)| ≤ I.epsilon N) ∧
        |Polynomial.eval I.mu (I.residual N)| = I.epsilon N :=
  @InexactRealizations.Properties.terminal_minimax_attained

end

section
/-! ## Display (2), p. 4 (actual causal oracle)

The canonical queries, answers and output use the actual preceding answers.
Strict causality makes the full finite sums equal the printed prefix sums.
-/
theorem display_2_queries {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (h : InexactRealizations.History N) (initial : E) (oracle : Fin N → E → E) (s : Fin N) :
    h.oracleQuery initial oracle s = initial - ∑ j, h.a s j • h.oracleAnswers initial oracle j := rfl

theorem display_2_answers {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (h : InexactRealizations.History N) (initial : E) (oracle : Fin N → E → E) (s : Fin N) :
    h.oracleAnswers initial oracle s = oracle s (h.oracleQuery initial oracle s) :=
  h.oracleAnswers_eq initial oracle s

theorem display_2_output {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (h : InexactRealizations.History N) (initial : E) (oracle : Fin N → E → E) :
    h.oracleOutput initial oracle = initial - ∑ j, h.b j • h.oracleAnswers initial oracle j := rfl
end

section
/-! ## Sections 1–2, pp. 3–4 (explicit Runge–Kutta histories)

`toHistory` sends the concrete strictly lower triangular Butcher matrix and readout to the actual causal oracle history. The internal-stability row is the printed matrix inverse expression.
-/

theorem text_rk_stages : ∀ {N : ℕ} {E : Type u_1} [_inst : AddCommGroup E] [_inst_1 : Module ℝ E]
  (T : InexactRealizations.Prose.RungeKutta.ExplicitTableau N) (F : Fin N → E → E) (initial : E) (s : Fin N),
  InexactRealizations.Prose.RungeKutta.stage T F initial s =
    F s (initial + ∑ j, T.A s j • InexactRealizations.Prose.RungeKutta.stage T F initial j) :=
  @InexactRealizations.Prose.RungeKutta.stage_equation

theorem text_rk_output : ∀ {N : ℕ} {E : Type u_1} [_inst : AddCommGroup E] [_inst_1 : Module ℝ E]
  (T : InexactRealizations.Prose.RungeKutta.ExplicitTableau N) (F : Fin N → E → E) (initial : E),
  InexactRealizations.Prose.RungeKutta.output T F initial =
    (InexactRealizations.Prose.RungeKutta.toHistory T).oracleOutput initial fun j y => -F j y :=
  @InexactRealizations.Prose.RungeKutta.output_eq_history

theorem text_rk_stability : ∀ {N : ℕ} (T : InexactRealizations.Prose.RungeKutta.ExplicitTableau N) (z initial : ℝ),
  InexactRealizations.Prose.RungeKutta.output T (fun _ y => z * y) initial =
    Polynomial.eval z (InexactRealizations.Prose.RungeKutta.stability T) * initial :=
  @InexactRealizations.Prose.RungeKutta.test_equation

theorem text_rk_internal_response : ∀ {N : ℕ} (T : InexactRealizations.Prose.RungeKutta.ExplicitTableau N) (lam : ℝ)
  (j : Fin N),
  InexactRealizations.Prose.RungeKutta.internalResponse T (-lam) j =
    lam * Polynomial.eval lam ((InexactRealizations.Prose.RungeKutta.toHistory T).response j) :=
  @InexactRealizations.Prose.RungeKutta.internalResponse_physical

theorem text_rk_bijection {N : ℕ} :
    Function.Bijective (@InexactRealizations.Prose.RungeKutta.toHistory N) :=
  (@InexactRealizations.Prose.RungeKutta.tableauEquiv N).bijective

theorem text_rk_terminal_polynomial {N : ℕ} (T : InexactRealizations.Prose.RungeKutta.ExplicitTableau N) :
    InexactRealizations.Prose.RungeKutta.stability T =
      (InexactRealizations.Prose.RungeKutta.toHistory T).terminal.comp (-Polynomial.X) := rfl

theorem text_rk_internal_row {N : ℕ} (T : InexactRealizations.Prose.RungeKutta.ExplicitTableau N)
    (lam : ℝ) (j : Fin N) :
    (-lam) * (∑ k, T.b k * ((1 - (-lam) • Matrix.of T.A)⁻¹) k j) =
      lam * ((InexactRealizations.Prose.RungeKutta.toHistory T).response j).eval lam :=
  InexactRealizations.Prose.RungeKutta.internalResponse_physical T lam j

end

section
/-! ## Theorem 2.1 (Realization identity), p. 5, Displays (3)–(5)

Queries and responses are the actual causal polynomials of the supplied universal history. Physical execution, the explicit divided-difference extension, and the constructed converse are stated below. The degree and factorization theorem also holds for N = 1.
-/

theorem theorem_2_1_degrees_and_factorization : ∀ {N : ℕ} (h : InexactRealizations.History N),
  0 < N →
    ∀ (I : InexactRealizations.Operators.SpectralInterval),
      h.ChebyshevExact I →
        (∀ (s : Fin N), (h.query s).degree = ↑↑s ∧ (h.response s).degree = ↑(N - 1 - ↑s)) ∧
          (∀ (s : Fin N),
              (h.chartQuery I s).degree = ↑↑s ∧
                (h.chartFactor I s).degree = ↑(N - 1 - ↑s) ∧ Polynomial.eval I.eta (h.chartQuery I s) = 1) ∧
            (∀ (x y : ℝ),
                ∑ s, Polynomial.eval x (h.response s) * Polynomial.eval y (h.query s) =
                  InexactRealizations.History.dividedDifference h.terminal x y) ∧
              (Continuous fun (xy : ℝ × ℝ) => InexactRealizations.History.dividedDifference h.terminal xy.1 xy.2) ∧
                ∀ (x y : ℝ),
                  ∑ s, Polynomial.eval x (h.chartFactor I s) * Polynomial.eval y (h.chartQuery I s) =
                    ((if x = y then (Polynomial.Chebyshev.T ℝ N).derivative.eval x else ((Polynomial.Chebyshev.T ℝ N).eval x - (Polynomial.Chebyshev.T ℝ N).eval y) / (x - y)) / 2) :=
  @InexactRealizations.realization_identity

theorem theorem_2_1_coordinate_query : ∀ {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
  (s : Fin N) (lam : ℝ), Polynomial.eval (I.z lam) (h.chartQuery I s) = Polynomial.eval lam (h.query s) :=
  @InexactRealizations.History.chartQuery_physical_eval

theorem theorem_2_1_coordinate_response : ∀ {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
  (s : Fin N) (lam : ℝ),
  Polynomial.eval lam (h.response s) = -4 * I.epsilon N / I.delta * Polynomial.eval (I.z lam) (h.chartFactor I s) :=
  @InexactRealizations.History.chartFactor_physical_eval

theorem theorem_2_1_factor_uniqueness : ∀ {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
  0 < N →
    h.ChebyshevExact I →
      ∀ (f : Fin N → Polynomial ℝ),
        (∀ (x y : ℝ),
            ∑ s, Polynomial.eval x (f s) * Polynomial.eval y (h.chartQuery I s) = ((if x = y then (Polynomial.Chebyshev.T ℝ N).derivative.eval x else ((Polynomial.Chebyshev.T ℝ N).eval x - (Polynomial.Chebyshev.T ℝ N).eval y) / (x - y)) / 2)) →
          f = h.chartFactor I :=
  @InexactRealizations.History.chart_factors_unique

end


section
/-! ## Theorem 2.1, p. 5 (actual execution and the constructed converse)

The execution is `h.run`, rather than a supplied certificate of the equations.
The input graded family is universally quantified as in the printed converse;
`Q.realize` is the actual history constructed from it, and its uniqueness is
stated together with its exact terminal and nominal queries.
-/
theorem theorem_2_1_nominal_query {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (initial : E) (s : Fin N) :
    (h.run H initial (fun _ => 0)).query s = (aeval H (h.query s)) initial :=
  h.nominal_query H initial (h.run H initial (fun _ => 0)) s

theorem theorem_2_1_actual_physical_response {N : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℝ E] (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (he : h.terminal = I.residual N)
    (H : E →ₗ[ℝ] E) (initial : E) (w : Fin N → E) :
    (h.run H initial w).output = (aeval H (I.residual N)) initial +
      ∑ j, (aeval H (h.response j)) (w j) := by
  rw [h.physical_response H initial w (h.run H initial w), he]

theorem theorem_2_1_divided_difference {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (he : h.terminal = I.residual N) (x y : ℝ) :
    (∑ j, (h.response j).eval x * (h.query j).eval y) =
      if x = y then (I.residual N).derivative.eval x
      else ((I.residual N).eval x - (I.residual N).eval y) / (x - y) := by
  simpa only [InexactRealizations.History.dividedDifference, he] using h.physical_bezout_all x y

theorem theorem_2_1_continuous_diagonal {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (he : h.terminal = I.residual N) :
    Continuous (fun xy : ℝ × ℝ => if xy.1 = xy.2 then (I.residual N).derivative.eval xy.1
      else ((I.residual N).eval xy.1 - (I.residual N).eval xy.2) / (xy.1 - xy.2)) := by
  simpa only [InexactRealizations.History.dividedDifference, he] using h.continuous_physical_bezout

theorem theorem_2_1_converse {N : ℕ} (Q : InexactRealizations.GradedFamily N)
    (I : InexactRealizations.Operators.SpectralInterval) (hQ : ∀ j, (Q.poly j).eval I.eta = 1) :
    ∃! h : InexactRealizations.History N, h.terminal = I.residual N ∧
      ∀ j, h.chartQuery I j = Q.poly j :=
  Q.existsUnique_realization I hQ

theorem theorem_2_1_constructed_history {N : ℕ} (Q : InexactRealizations.GradedFamily N)
    (I : InexactRealizations.Operators.SpectralInterval) (hQ : ∀ j, (Q.poly j).eval I.eta = 1) :
    (Q.realize I hQ).terminal = I.residual N ∧
      ∀ j, (Q.realize I hQ).chartQuery I j = Q.poly j :=
  ⟨Q.realize_exact I hQ, Q.realize_chartQuery I hQ⟩
end

section
/-! ## Section 2, p. 5, Display (6) (the two corner sums)

The signs and normalizations are the printed S_N and D_N. The same
identities give the normalized mean-one profiles of Figure 1, p. 3.
-/
theorem display_6_response_sum {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (he : h.terminal = I.residual N) :
    (∑ j, (h.response j).eval I.mu) = -(1 - I.epsilon N) / I.mu :=
by
  simpa only [InexactRealizations.Lower.additiveScale, neg_div] using InexactRealizations.Lower.response_sum_mu h I he

theorem display_6_response_query_sum {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (he : h.terminal = I.residual N) :
    (∑ j, (h.response j).eval I.mu * (h.query j).eval I.mu) =
      -(2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) :=
  InexactRealizations.Lower.kernel_sum_mu h I he
end

section
/-! ## Theorem 2.2 (Corner bounds), p. 6, Display (7)

`p` and its Holder conjugate `q` encode gamma and gamma*. The risks are literal suprema of actual executions. The additive equality clause uses precisely the printed t > 0 qualification; the relative equality clause has no t premise.
-/

theorem theorem_2_2_additive : ∀ {N : ℕ} {p q : ENNReal} [p.HolderConjugate q] (h : InexactRealizations.History N)
  (I : InexactRealizations.Operators.SpectralInterval),
  h.ChebyshevExact I →
    0 < N →
      ∀ {r t : ℝ},
        0 ≤ r →
          0 ≤ t →
            (I.epsilon N * r + t * ↑N ^ (-(1 / p).toReal) * ((1 - I.epsilon N) / I.mu) ≤
                I.epsilon N * r + t * InexactRealizations.Budgets.callNorm q fun s => Polynomial.eval I.mu (h.response s)) ∧
              (I.epsilon N * r + t * InexactRealizations.Budgets.callNorm q fun s => Polynomial.eval I.mu (h.response s)) ≤
                InexactRealizations.Budgets.additiveRisk p h I r t :=
  @InexactRealizations.Budgets.additive_corner_chain

theorem theorem_2_2_relative : ∀ {N : ℕ} (p : ENNReal),
  1 ≤ p →
    ∀ (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
      h.ChebyshevExact I →
        0 < N →
          ∀ (r : ℝ),
            0 < r →
              InexactRealizations.Budgets.localRelativeGain p h I r = InexactRealizations.Budgets.operatorGain p h I false ∧
                (InexactRealizations.Budgets.callNorm (InexactRealizations.Budgets.dualExponent p) fun s =>
                      Polynomial.eval I.mu (h.response s) * Polynomial.eval I.mu (h.query s)) ≤
                    InexactRealizations.Budgets.localRelativeGain p h I r ∧
                  ↑N ^ (-(1 / p).toReal) * (2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) ≤
                    InexactRealizations.Budgets.callNorm (InexactRealizations.Budgets.dualExponent p) fun s =>
                      Polynomial.eval I.mu (h.response s) * Polynomial.eval I.mu (h.query s) :=
  @InexactRealizations.Budgets.relative_corner_chain

theorem theorem_2_2_symmetric_operator_lower : ∀ {N : ℕ} (p : ENNReal),
  1 ≤ p →
    ∀ (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
      h.ChebyshevExact I →
        0 < N →
          ∀ (symmetric : Bool),
            ↑N ^ (-(1 / p).toReal) * (2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) ≤ InexactRealizations.Budgets.operatorGain p h I symmetric :=
  @InexactRealizations.Budgets.operator_corner_lower

theorem theorem_2_2_additive_equality : ∀ {N : ℕ} {p q : ENNReal} [p.HolderConjugate q],
  p ≠ ⊤ →
    ∀ (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
      h.ChebyshevExact I →
        0 < N →
          ∀ {a t : ℝ},
            0 < t →
              ((a + t * InexactRealizations.Budgets.callNorm q fun s => Polynomial.eval I.mu (h.response s)) =
                  a + t * ↑N ^ (-(1 / p).toReal) * ((1 - I.epsilon N) / I.mu) ↔
                ∀ (s : Fin N), Polynomial.eval I.mu (h.response s) = -((1 - I.epsilon N) / I.mu) / ↑N) :=
  @InexactRealizations.Budgets.additive_corner_equality

theorem theorem_2_2_relative_equality : ∀ {N : ℕ} {p q : ENNReal} [p.HolderConjugate q],
  p ≠ ⊤ →
    ∀ (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
      h.ChebyshevExact I →
        0 < N →
          ((InexactRealizations.Budgets.callNorm q fun s => InexactRealizations.Lower.physicalKernel h s I.mu I.mu) =
              ↑N ^ (-(1 / p).toReal) * (2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) ↔
            ∀ (s : Fin N), InexactRealizations.Lower.physicalKernel h s I.mu I.mu = -(2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / ↑N) :=
  @InexactRealizations.Budgets.relative_corner_equality

end


section
/-! ## Section 3, p. 6, Display (8) (the stochastic oracle model)

The nonnegative conditional second moment is expressed by conditional
Lebesgue expectation. It implies L2 integrability. The stochastic risk is
therefore exactly the supremum over the printed raw moment class, with no
integrability or independence assumption added to that class.
-/
theorem display_8_square_integrability {N : ℕ} {Omega E : Type*}
    [mOmega : MeasurableSpace Omega] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (F : Filtration ℕ mOmega)
    (w : ℕ → Omega → E) (sigma : ℝ)
    (ha : ∀ j, j < N → StronglyMeasurable[F (j + 1)] (w j))
    (hc : ∀ j, j < N → mu[w j | F j] =ᵐ[mu] 0)
    (hv : ∀ j, j < N → mu⁻[fun omega => ENNReal.ofReal (‖w j omega‖ ^ 2) | F j] ≤ᵐ[mu]
      fun _ => ENNReal.ofReal (sigma ^ 2)) :
    ∀ j, j < N → MemLp (w j) 2 mu :=
  (InexactRealizations.Prose.RawAdditiveLaw.mk ha hc hv).squareIntegrable

theorem display_8_raw_mse_supremum {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (he : h.terminal = I.residual N)
    (r sigma : ℝ) (hr : 0 ≤ r) :
    InexactRealizations.Risk.mseRisk h I r sigma =
      sSup {v : ℝ | InexactRealizations.Prose.RawMseValue h I r sigma v} :=
  InexactRealizations.Prose.mseRisk_raw_supremum h I he r sigma hr
end

section
/-! ## Theorem 3.1 (Exact additive optima), p. 6, Displays (9)–(10)

The sets range over all Chebyshev-exact histories with unrestricted signs and memory. Their displayed values are attained least elements, proved for the actual constructed Flat history.
-/

theorem theorem_3_1_additive_minimum : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  2 ≤ N →
    ∀ (r t : ℝ),
      0 ≤ r →
        0 ≤ t →
          IsLeast {v | ∃ h : InexactRealizations.History N, h.ChebyshevExact I ∧ v = InexactRealizations.Risk.additiveRisk h I r t}
            ((I.epsilon N * r + t * ((1 - I.epsilon N) / I.mu) / Real.sqrt N)) :=
  @InexactRealizations.Flat.additive_minimum

theorem theorem_3_1_mse_minimum : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  2 ≤ N →
    ∀ (r σ : ℝ),
      0 ≤ r → IsLeast {v | ∃ h : InexactRealizations.History N, h.ChebyshevExact I ∧ v = InexactRealizations.Risk.mseRisk h I r σ} (((I.epsilon N) ^ 2 * r ^ 2 + σ ^ 2 * ((1 - I.epsilon N) / I.mu) ^ 2 / N)) :=
  @InexactRealizations.Flat.mse_minimum

theorem theorem_3_1_flat_additive (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    InexactRealizations.Risk.additiveRisk (InexactRealizations.Flat.history I N hN) I r t =
      I.epsilon N * r + t * ((1 - I.epsilon N) / I.mu) / Real.sqrt N :=
  InexactRealizations.Flat.additiveRisk_eq I N hN r t hr ht

theorem theorem_3_1_flat_mse (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (r sigma : ℝ) (hr : 0 ≤ r) :
    InexactRealizations.Risk.mseRisk (InexactRealizations.Flat.history I N hN) I r sigma =
      (I.epsilon N) ^ 2 * r ^ 2 + sigma ^ 2 * ((1 - I.epsilon N) / I.mu) ^ 2 / N :=
  InexactRealizations.Flat.mseRisk_eq I N hN r sigma hr

end


section
/-! ## Section 3, p. 6, Displays (11)–(12) (the constructed Flat factors)

`mass`, `unitMass`, `reservoir`, `tau` and `factorPolynomial` are precisely
the printed a_m, d, R_m, tau_s and barred T_m. Natural subtraction is used
only within the displayed valid horizon indices. The zero predecessor term
vanishes because tau_0 = 0.
-/
theorem display_11_flat_data (I : InexactRealizations.Operators.SpectralInterval) (N m j : ℕ) :
    InexactRealizations.Flat.u I j = (Polynomial.Chebyshev.U ℝ j).eval I.eta ∧
      InexactRealizations.Flat.mass I N m =
        (if m = 0 then InexactRealizations.Flat.u I (N - 1) / 2 else InexactRealizations.Flat.u I (N - 1 - m)) ∧
      InexactRealizations.Flat.unitMass I N = (∑ k ∈ Finset.range N, InexactRealizations.Flat.mass I N k) / N ∧
      InexactRealizations.Flat.reservoir I N m =
        (∑ k ∈ Finset.range (m + 1), InexactRealizations.Flat.mass I N k) - (m : ℝ) * InexactRealizations.Flat.unitMass I N ∧
      InexactRealizations.Flat.tau I N j = InexactRealizations.Flat.reservoir I N (N - 1 - j) / InexactRealizations.Flat.unitMass I N - 1 := by
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  by_cases hN : N = 0
  · subst N
    simp [InexactRealizations.Flat.unitMass]
  · simp only [InexactRealizations.Flat.unitMass, InexactRealizations.Flat.totalMass, InexactRealizations.Flat.prefixMass,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN)]

theorem display_11_flat_tau (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    InexactRealizations.Flat.tau I N 0 = 0 ∧ ∀ j < N, 0 ≤ InexactRealizations.Flat.tau I N j :=
  ⟨InexactRealizations.Flat.tau_zero I N hN, fun j hj => InexactRealizations.Flat.tau_nonneg I N hN j hj⟩

theorem display_12_flat_response_recurrence (I : InexactRealizations.Operators.SpectralInterval) (N m : ℕ) :
    InexactRealizations.Flat.factorPolynomial I N 0 = 1 ∧
      InexactRealizations.Flat.factorPolynomial I N (m + 1) =
        C (1 - InexactRealizations.Flat.mass I N (m + 1) / InexactRealizations.Flat.reservoir I N (m + 1)) *
          InexactRealizations.Flat.factorPolynomial I N m +
        C (InexactRealizations.Flat.mass I N (m + 1) / InexactRealizations.Flat.reservoir I N (m + 1)) *
          Polynomial.Chebyshev.T ℝ ((m + 1 : ℕ) : ℤ) := ⟨rfl, rfl⟩

theorem display_12_flat_convex_coefficients (I : InexactRealizations.Operators.SpectralInterval)
    (N : ℕ) (hN : 0 < N) (m : ℕ) (hm : m < N) :
    0 ≤ InexactRealizations.Flat.mass I N m / InexactRealizations.Flat.reservoir I N m ∧
      InexactRealizations.Flat.mass I N m / InexactRealizations.Flat.reservoir I N m ≤ 1 :=
  InexactRealizations.Flat.mixture_mem I N hN m hm

theorem display_12_flat_query (I : InexactRealizations.Operators.SpectralInterval) (N j : ℕ) :
    InexactRealizations.Flat.queryPolynomial I N j =
      C (1 + InexactRealizations.Flat.tau I N j) * InexactRealizations.Flat.normalizedU I j -
      C (InexactRealizations.Flat.tau I N j) * InexactRealizations.Flat.normalizedU I (j - 1) := rfl

theorem display_12_flat_actual_factors (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (hN : 2 ≤ N) (j : Fin N) :
    (InexactRealizations.Flat.history I N hN).chartQuery I j = InexactRealizations.Flat.queryPolynomial I N j ∧
      (InexactRealizations.Flat.history I N hN).chartFactor I j =
        C (InexactRealizations.Flat.unitMass I N) * InexactRealizations.Flat.factorPolynomial I N (N - 1 - j.val) :=
  ⟨InexactRealizations.Flat.history_chartQuery I N hN j, InexactRealizations.Flat.history_chartFactor I N hN j⟩
end

section
/-! ## Section 3, p. 6, Display (13) (Flat peak responses)

The same actual Flat history has equal signed responses at mu and the sharp interval bound at every call.
-/

theorem display_13_flat_responses : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (s : Fin N),
  (∀ lam ∈ Set.Icc I.mu I.L,
      |Polynomial.eval lam ((InexactRealizations.Flat.history I N hN).response s)| ≤ ((1 - I.epsilon N) / I.mu) / ↑N) ∧
    Polynomial.eval I.mu ((InexactRealizations.Flat.history I N hN).response s) = -(((1 - I.epsilon N) / I.mu) / ↑N) :=
  @InexactRealizations.Flat.response_uniform_sharp

end

section
/-! ## Algorithm 1 (Flat Chebyshev), p. 7

`ratioProgram` is the printed ratio-prepared four-register program. Its actual queries and terminal output equal the concrete Flat history for every time-dependent oracle. Every division used by the preparation has positive denominator.
-/

theorem algorithm_1_preparation : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  2 ≤ N →
    0 < 2 * I.eta ∧
      (∀ (j : ℕ), 0 < 2 * I.eta - InexactRealizations.Algorithms.Flat.ratioU I j) ∧
        0 < InexactRealizations.Algorithms.Flat.ratioMass I N ∧
          0 < I.delta ∧
            0 < I.eta - InexactRealizations.Algorithms.Flat.ratioU I (N - 2) ∧
              ∀ (s : Fin N), 0 < 1 + InexactRealizations.Algorithms.Flat.ratioTau I N ↑s :=
  @InexactRealizations.Algorithms.Flat.journal_flat_preparation_defined

theorem algorithm_1_queries : ∀ {E : Type u_1} [_inst : AddCommGroup E] [_inst_1 : Module ℝ E]
  (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (oracle : Fin N → E → E) (initial : E) (s : Fin N),
  (InexactRealizations.Algorithms.Flat.ratioProgram I N).queryAt oracle initial s =
    (InexactRealizations.Flat.history I N hN).oracleQuery initial oracle s :=
  @InexactRealizations.Algorithms.Flat.ratioProgram_query

theorem algorithm_1_output : ∀ {E : Type u_1} [_inst : AddCommGroup E] [_inst_1 : Module ℝ E]
  (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (oracle : Fin N → E → E) (initial : E),
  (InexactRealizations.Algorithms.Flat.ratioProgram I N).output oracle initial =
    (InexactRealizations.Flat.history I N hN).oracleOutput initial oracle :=
  @InexactRealizations.Algorithms.Flat.ratioProgram_output

theorem algorithm_1_physical_response : ∀ {E : Type u_1} [_inst : AddCommGroup E] [_inst_1 : Module ℝ E]
  (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (H : E →ₗ[ℝ] E) (initial : E) (w : Fin N → E),
  (InexactRealizations.Algorithms.Flat.ratioProgram I N).output (fun s y => H y + w s) initial =
    ((Polynomial.aeval H) (I.residual N)) initial +
      ∑ s, ((Polynomial.aeval H) ((InexactRealizations.Flat.history I N hN).response s)) (w s) :=
  @InexactRealizations.Algorithms.Flat.journal_flat_physical_response

theorem algorithm_1_calls : ∀ {E : Type u_1} [_inst : AddCommGroup E] [_inst_1 : Module ℝ E]
  (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (oracle : Fin N → E → E) (initial : E),
  ((InexactRealizations.Algorithms.Flat.ratioProgram I N).run oracle initial).calls = N :=
  @InexactRealizations.Algorithms.Flat.journal_flat_oracle_calls

theorem algorithm_1_storage : Fintype.card (Fin 4) = 4 :=
  @InexactRealizations.Algorithms.Flat.journal_flat_vector_slots

theorem algorithm_1_all_prefix_states {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (oracle : Fin N → E → E)
    (initial : E) (j : ℕ) (hj : j ≤ N) :
    ∃ values : Fin 4 → E, (InexactRealizations.Algorithms.Flat.ratioProgram I N).runPrefix oracle initial j =
      ⟨values, j⟩ := by
  refine ⟨((InexactRealizations.Algorithms.Flat.ratioProgram I N).runPrefix oracle initial j).vectors, ?_⟩
  apply InexactRealizations.Algorithms.RegisterState.ext
  · rfl
  · exact InexactRealizations.Algorithms.RegisterProgram.runPrefix_calls _ _ _ j hj

end

section
/-! ## Section 3, p. 7, Display (14) (Prefix variance)

`Classical.history` is Prefix, and `varianceLimit` is its explicit positive fixed-interval limit. The variance formula concerns the oracle-noise contribution.
-/

theorem display_14_classical_variance : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  0 < N →
    InexactRealizations.Classical.variance I N =
      16 * I.epsilon N ^ 2 / I.delta ^ 2 * (↑N ^ 2 / 4 + ∑ s ∈ Finset.Ico 1 N, (↑N - ↑s) ^ 2 * I.den s ^ 2) :=
  @InexactRealizations.Classical.variance_exact

theorem display_14_actual_mse (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (r sigma : ℝ) (hr : 0 ≤ r) :
    InexactRealizations.Risk.mseRisk (InexactRealizations.Classical.history I N) I r sigma =
      (I.epsilon N) ^ 2 * r ^ 2 + sigma ^ 2 *
        ((16 * (I.epsilon N) ^ 2 / I.delta ^ 2) *
          ((N : ℝ) ^ 2 / 4 + ∑ j ∈ Finset.Ico 1 N, ((N : ℝ) - j) ^ 2 * (I.den j) ^ 2)) := by
  rw [InexactRealizations.Classical.mseRisk_eq I N hN r sigma hr, InexactRealizations.Classical.variance_exact I N hN]

theorem text_classical_positive_limit : ∀ (I : InexactRealizations.Operators.SpectralInterval),
  Filter.Tendsto (InexactRealizations.Classical.variance I) Filter.atTop (nhds (InexactRealizations.Classical.varianceLimit I)) :=
  @InexactRealizations.Classical.variance_tendsto

theorem text_classical_limit_positive : ∀ (I : InexactRealizations.Operators.SpectralInterval), 0 < InexactRealizations.Classical.varianceLimit I :=
  @InexactRealizations.Classical.varianceLimit_pos

theorem text_flat_variance_asymptotic : ∀ (I : InexactRealizations.Operators.SpectralInterval),
  Asymptotics.IsEquivalent Filter.atTop (fun N => ((1 - I.epsilon N) / I.mu) ^ 2 / ↑N) fun N => 1 / (I.mu ^ 2 * ↑N) :=
  @InexactRealizations.Properties.flat_variance_isEquivalent

end

section
/-! ## Theorem 3.2 (All linear methods), p. 7, Display (15)

All fixed-coefficient histories are allowed, with an arbitrary terminal polynomial. The displayed piecewise value is written explicitly for both deterministic and random initial-error classes; its scalar constrained minimum is included. The probability model grants a method only its seed and prior oracle answers.
-/

theorem theorem_3_2_minima : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  2 ≤ N →
    ∀ (r σ : ℝ),
      0 ≤ r →
        IsLeast {v | ∃ h : InexactRealizations.History N, v = InexactRealizations.Risk.mseRisk h I r σ} ((if σ ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2 then r ^ 2 * (I.epsilon N) ^ 2 + (σ ^ 2 / (I.mu ^ 2 * ↑N)) * (1 - I.epsilon N) ^ 2 else r ^ 2 * (σ ^ 2 / (I.mu ^ 2 * ↑N)) / (r ^ 2 + σ ^ 2 / (I.mu ^ 2 * ↑N)))) ∧
          IsLeast {v | ∃ h : InexactRealizations.History N, v = InexactRealizations.Risk.AllLinear.randomMseRisk h I r σ}
              ((if σ ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2 then r ^ 2 * (I.epsilon N) ^ 2 + (σ ^ 2 / (I.mu ^ 2 * ↑N)) * (1 - I.epsilon N) ^ 2 else r ^ 2 * (σ ^ 2 / (I.mu ^ 2 * ↑N)) / (r ^ 2 + σ ^ 2 / (I.mu ^ 2 * ↑N)))) ∧
            IsLeast ((fun c : ℝ => r ^ 2 * c ^ 2 + (σ ^ 2 / (I.mu ^ 2 * ↑N)) * (1 - c) ^ 2) '' Set.Icc (I.epsilon N) 1)
              ((if σ ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2 then r ^ 2 * (I.epsilon N) ^ 2 + (σ ^ 2 / (I.mu ^ 2 * ↑N)) * (1 - I.epsilon N) ^ 2 else r ^ 2 * (σ ^ 2 / (I.mu ^ 2 * ↑N)) / (r ^ 2 + σ ^ 2 / (I.mu ^ 2 * ↑N)))) :=
  @InexactRealizations.Risk.AllLinear.journal_all_linear_fixed_coefficients

theorem theorem_3_2_raw_random_initial_class {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (r sigma : ℝ) (hr : 0 ≤ r) :
    InexactRealizations.Risk.AllLinear.randomMseRisk h I r sigma =
      sSup {v : ℝ | InexactRealizations.Prose.RawRandomMseValue h I r sigma v} :=
  InexactRealizations.Prose.randomMseRisk_raw_supremum h I r sigma hr

theorem theorem_3_2_flat_iff : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (r σ : ℝ),
  0 ≤ r →
    (InexactRealizations.Risk.mseRisk (InexactRealizations.Flat.history I N hN) I r σ = (if σ ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2 then r ^ 2 * (I.epsilon N) ^ 2 + (σ ^ 2 / (I.mu ^ 2 * ↑N)) * (1 - I.epsilon N) ^ 2 else r ^ 2 * (σ ^ 2 / (I.mu ^ 2 * ↑N)) / (r ^ 2 + σ ^ 2 / (I.mu ^ 2 * ↑N))) ↔
        σ ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2) ∧
      (InexactRealizations.Risk.AllLinear.randomMseRisk (InexactRealizations.Flat.history I N hN) I r σ =
          (if σ ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2 then r ^ 2 * (I.epsilon N) ^ 2 + (σ ^ 2 / (I.mu ^ 2 * ↑N)) * (1 - I.epsilon N) ^ 2 else r ^ 2 * (σ ^ 2 / (I.mu ^ 2 * ↑N)) / (r ^ 2 + σ ^ 2 / (I.mu ^ 2 * ↑N))) ↔
        σ ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2) :=
  @InexactRealizations.Risk.AllLinear.journal_all_linear_flat_iff

theorem theorem_3_2_shrunk_flat : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (r σ : ℝ),
  0 ≤ r →
    InexactRealizations.Risk.mseRisk (InexactRealizations.Risk.AllLinear.optimalHistory I N hN r σ) I r σ =
      (if σ ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2 then r ^ 2 * (I.epsilon N) ^ 2 + (σ ^ 2 / (I.mu ^ 2 * ↑N)) * (1 - I.epsilon N) ^ 2 else r ^ 2 * (σ ^ 2 / (I.mu ^ 2 * ↑N)) / (r ^ 2 + σ ^ 2 / (I.mu ^ 2 * ↑N))) :=
  @InexactRealizations.Risk.AllLinear.optimalHistory_mseRisk

theorem theorem_3_2_shrunk_flat_random : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (r σ : ℝ),
  0 ≤ r →
    InexactRealizations.Risk.AllLinear.randomMseRisk (InexactRealizations.Risk.AllLinear.optimalHistory I N hN r σ) I r σ =
      (if σ ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2 then r ^ 2 * (I.epsilon N) ^ 2 + (σ ^ 2 / (I.mu ^ 2 * ↑N)) * (1 - I.epsilon N) ^ 2 else r ^ 2 * (σ ^ 2 / (I.mu ^ 2 * ↑N)) / (r ^ 2 + σ ^ 2 / (I.mu ^ 2 * ↑N))) :=
  @InexactRealizations.Risk.AllLinear.optimalHistory_randomMseRisk

theorem theorem_3_2_multiplicative : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (r σ : ℝ),
  0 < r →
    InexactRealizations.Risk.mseRisk (InexactRealizations.Flat.history I N hN) I r σ ≤
      (1 + σ ^ 2 / (I.mu ^ 2 * ↑N) / r ^ 2) * (if σ ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2 then r ^ 2 * (I.epsilon N) ^ 2 + (σ ^ 2 / (I.mu ^ 2 * ↑N)) * (1 - I.epsilon N) ^ 2 else r ^ 2 * (σ ^ 2 / (I.mu ^ 2 * ↑N)) / (r ^ 2 + σ ^ 2 / (I.mu ^ 2 * ↑N))) :=
  @InexactRealizations.Risk.AllLinear.flat_all_linear_factor

theorem theorem_3_2_multiplicative_random : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
  (r σ : ℝ),
  0 < r →
    InexactRealizations.Risk.AllLinear.randomMseRisk (InexactRealizations.Flat.history I N hN) I r σ ≤
      (1 + σ ^ 2 / (I.mu ^ 2 * ↑N) / r ^ 2) * (if σ ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2 then r ^ 2 * (I.epsilon N) ^ 2 + (σ ^ 2 / (I.mu ^ 2 * ↑N)) * (1 - I.epsilon N) ^ 2 else r ^ 2 * (σ ^ 2 / (I.mu ^ 2 * ↑N)) / (r ^ 2 + σ ^ 2 / (I.mu ^ 2 * ↑N))) :=
  @InexactRealizations.Risk.AllLinear.flat_all_linear_random_factor

theorem theorem_3_2_zero_signal_zero_noise : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  InexactRealizations.Risk.AllLinear.optimalShrink I N 0 0 = 0 :=
  @InexactRealizations.Risk.AllLinear.optimalShrink_zero_zero

theorem theorem_3_2_shrink_coefficient (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (r sigma : ℝ) :
    InexactRealizations.Risk.AllLinear.optimalShrink I N r sigma =
      min 1 (r ^ 2 / ((r ^ 2 + sigma ^ 2 / (I.mu ^ 2 * N)) * (1 - I.epsilon N))) := rfl

theorem theorem_3_2_arbitrary_adaptive : ∀ {N : ℕ} {U : Type} [_inst : MeasurableSpace U]
  (I : InexactRealizations.Operators.SpectralInterval),
  2 ≤ N →
    ∀ (r sigma : ℝ),
      0 ≤ r →
        0 ≤ sigma →
          sigma ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) > I.epsilon N * r ^ 2 →
            ∀ (M : InexactRealizations.Risk.Adaptive.Family N U) (P : MeasureTheory.Measure U)
              [MeasureTheory.IsProbabilityMeasure P],
              ENNReal.ofReal ((if sigma ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2 then r ^ 2 * (I.epsilon N) ^ 2 + (sigma ^ 2 / (I.mu ^ 2 * ↑N)) * (1 - I.epsilon N) ^ 2 else r ^ 2 * (sigma ^ 2 / (I.mu ^ 2 * ↑N)) / (r ^ 2 + sigma ^ 2 / (I.mu ^ 2 * ↑N)))) ≤
                InexactRealizations.Risk.Adaptive.mseRisk M P I r sigma :=
  @InexactRealizations.Risk.AllLinear.journal_arbitrary_adaptive_lower

theorem theorem_3_2_arbitrary_adaptive_at_initial_point : ∀ {N : ℕ} {U : Type} [_inst : MeasurableSpace U]
  (I : InexactRealizations.Operators.SpectralInterval),
  2 ≤ N →
    ∀ (r sigma x0 : ℝ),
      0 ≤ r →
        0 ≤ sigma →
          sigma ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) > I.epsilon N * r ^ 2 →
            ∀ (M : InexactRealizations.Probability.AdaptiveMethod N ℝ U) (P : MeasureTheory.Measure U)
              [MeasureTheory.IsProbabilityMeasure P],
              ENNReal.ofReal ((if sigma ^ 2 / (I.mu ^ 2 * ↑N) * (1 - I.epsilon N) ≤ I.epsilon N * r ^ 2 then r ^ 2 * (I.epsilon N) ^ 2 + (sigma ^ 2 / (I.mu ^ 2 * ↑N)) * (1 - I.epsilon N) ^ 2 else r ^ 2 * (sigma ^ 2 / (I.mu ^ 2 * ↑N)) / (r ^ 2 + sigma ^ 2 / (I.mu ^ 2 * ↑N)))) ≤
                InexactRealizations.Risk.Adaptive.scalarMseRisk (M.recenter x0) P I r sigma :=
  @InexactRealizations.Risk.AllLinear.journal_arbitrary_adaptive_lower_at

end



section
/-! ## Section 4, p. 8, Display (16) (spectral kernel and first variation)

The maximum exists over the whole closed spectral square. The derivative is
of the actual time-dependent perturbed oracle execution, with no derivative
certificate among the hypotheses.
-/
theorem display_16_kernel_maximum {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) :
    (∀ x ∈ Set.Icc I.mu I.L, ∀ y ∈ Set.Icc I.mu I.L,
      Real.sqrt (∑ j, ((h.response j).eval x * (h.query j).eval y) ^ 2) ≤ h.spectralGain I) ∧
      ∃ x ∈ Set.Icc I.mu I.L, ∃ y ∈ Set.Icc I.mu I.L,
        Real.sqrt (∑ j, ((h.response j).eval x * (h.query j).eval y) ^ 2) = h.spectralGain I :=
  ⟨fun _ hx _ hy => h.physical_kernelNorm_le_gain I hx hy, h.spectralGain_attained I⟩

theorem text_hessian_variation_derivative {N : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E) (D : Fin N → E →ₗ[ℝ] E) (initial : E) :
    HasDerivAt (fun t : ℝ => h.oracleOutput initial (fun j y => H y + t • D j y))
      (∑ j, (aeval H (h.response j)) (D j ((aeval H (h.query j)) initial))) 0 :=
  h.hasDerivAt_perturbed_output H D initial

theorem text_hilbert_schmidt_bound {N : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (H : Matrix d d ℝ)
    (hH : H.IsHermitian) (hs : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (D : Fin N → Matrix d d ℝ) :
    InexactRealizations.Operators.hsNorm (h.matrixResponse H D) ≤
      h.spectralGain I * Real.sqrt (∑ j, InexactRealizations.Operators.hsNorm (D j) ^ 2) :=
  h.hs_matrixResponse_bound I H hH hs D
end

section
/-! ## Theorem 4.1, p. 8, Display (17) (the three gains for every history)

For a pooled energy budget the two-measure squared response is a bilinear
probability average of the pointwise squared spectral kernel. Its maximum
is attained at a pair of Dirac masses. This identifies the literal actual
relative gain and the supremum of actual operator norms with the printed
spectral maximum for every history and both perturbation classes.
-/
open InexactRealizations.Budgets

private theorem aux1_callNorm_two_sq {N : ℕ} (v : Fin N → ℝ) :
    callNorm 2 v ^ 2 = ∑ s, v s ^ 2 := by
  simpa only [callNorm, Real.norm_eq_abs, sq_abs] using
    (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 v))

private theorem aux1_callNorm_two {N : ℕ} (v : Fin N → ℝ) :
    callNorm 2 v = Real.sqrt (∑ s, v s ^ 2) := by
  apply (sq_eq_sq₀ (callNorm_nonneg (p := 2) _) (Real.sqrt_nonneg _)).mp
  rw [aux1_callNorm_two_sq, Real.sq_sqrt (Finset.sum_nonneg (fun s _ => sq_nonneg (v s)))]

private theorem aux1_product_moments {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (alpha beta : FiniteSpectrum I) :
    (∑ s : Fin N, alpha.moment (h.response s) * beta.moment (h.query s)) =
      ∑ i, alpha.weight i * ∑ j, beta.weight j *
        InexactRealizations.Lower.physicalKernelSq h (alpha.point i) (beta.point j) := by
  simp only [FiniteSpectrum.moment, InexactRealizations.Lower.physicalKernelSq,
    InexactRealizations.Lower.physicalKernel, mul_pow, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ j : Fin beta.size, ∑ i : Fin alpha.size, ∑ k : Fin N,
        alpha.weight i * (h.response k).eval (alpha.point i) ^ 2 *
          (beta.weight j * (h.query k).eval (beta.point j) ^ 2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

private theorem aux1_two_measure_upper {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (alpha beta : FiniteSpectrum I) :
    operatorSpectralValue 2 h alpha beta ≤ h.spectralGain I := by
  have hg : 0 ≤ h.spectralGain I := h.realization.gain_nonneg I N
  have he : operatorSpectralValue 2 h alpha beta ^ 2 =
      ∑ s : Fin N, alpha.moment (h.response s) * beta.moment (h.query s) := by
    rw [operatorSpectralValue, aux1_callNorm_two_sq]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow, FiniteSpectrum.polynomialNorm, FiniteSpectrum.polynomialNorm,
      Real.sq_sqrt (alpha.moment_nonneg _), Real.sq_sqrt (beta.moment_nonneg _)]
  have hb (i : Fin alpha.size) (j : Fin beta.size) :
      InexactRealizations.Lower.physicalKernelSq h (alpha.point i) (beta.point j) ≤ h.spectralGain I ^ 2 := by
    have hk := h.physical_kernelNorm_le_gain I (alpha.point_mem i) (beta.point_mem j)
    have hx : 0 ≤ InexactRealizations.Lower.physicalKernelSq h (alpha.point i) (beta.point j) :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hs := Real.sq_sqrt hx
    nlinarith [Real.sqrt_nonneg (InexactRealizations.Lower.physicalKernelSq h (alpha.point i) (beta.point j))]
  have hu : operatorSpectralValue 2 h alpha beta ^ 2 ≤ h.spectralGain I ^ 2 := by
    rw [he, aux1_product_moments]
    calc
      _ ≤ ∑ i, alpha.weight i * ∑ j, beta.weight j * h.spectralGain I ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (alpha.nonneg i)
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hb i j) (beta.nonneg j)
      _ = h.spectralGain I ^ 2 := by
        simp only [← Finset.sum_mul, alpha.total, beta.total, one_mul]
  have hn : 0 ≤ operatorSpectralValue 2 h alpha beta := callNorm_nonneg (p := 2) _
  nlinarith

theorem theorem_4_1_actual_operator_eq_spectral {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (hN : 0 < N) (symmetric : Bool) :
    InexactRealizations.Budgets.operatorGain 2 h I symmetric = h.spectralGain I := by
  let : (2 : ℝ≥0∞).HolderConjugate 2 := inferInstance
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  apply le_antisymm
  · rw [operator_spectral_duality (p := 2) (q := 2) h I hN symmetric]
    have hne : (operatorSpectralValues 2 h I).Nonempty :=
      ⟨operatorSpectralValue 2 h (FiniteSpectrum.pointMass I) (FiniteSpectrum.pointMass I), ⟨_, _, rfl⟩⟩
    apply csSup_le hne
    rintro _ ⟨alpha, beta, rfl⟩
    exact aux1_two_measure_upper h I alpha beta
  · obtain ⟨x, hx, y, hy, he⟩ := h.spectralGain_attained I
    rw [← he]
    have hk := operator_kernel_lower (p := 2) (q := 2) h I symmetric x y hx hy
    rw [aux1_callNorm_two] at hk
    exact hk

theorem theorem_4_1_actual_relative_operator_spectral {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (hN : 0 < N) (r : ℝ) (hr : 0 < r) (symmetric : Bool) :
    InexactRealizations.Budgets.localRelativeGain 2 h I r =
        InexactRealizations.Budgets.operatorNormGain 2 h I symmetric ∧
      InexactRealizations.Budgets.operatorNormGain 2 h I symmetric = h.spectralGain I := by
  let : (2 : ℝ≥0∞).HolderConjugate 2 := inferInstance
  have hm := (InexactRealizations.Budgets.journal_relative_operatorNorm_duality 2 (by norm_num)
    h I hN r hr symmetric).1
  refine ⟨hm, ?_⟩
  rw [InexactRealizations.Budgets.operatorNormGain_eq (p := 2) (q := 2)]
  exact theorem_4_1_actual_operator_eq_spectral h I hN symmetric

end

section
/-! ## Theorem 4.1 (Linear energy optimum), p. 8, Displays (17)–(18)

The exact printed parity correction is expanded in the gain value. All minima are over unrestricted Chebyshev-exact histories. The concrete Balanced history attains all gains, including both symmetric perturbation classes. The preceding block supplies the common-gain identity for every history.
-/

theorem theorem_4_1_spectral_lower : ∀ {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
  h.ChebyshevExact I → 2 ≤ N → ((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N * Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1)) ≤ h.spectralGain I :=
  @InexactRealizations.History.linearGain_le_spectralGain

theorem theorem_4_1_operator_lower : ∀ {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
  h.ChebyshevExact I →
    2 ≤ N → ∀ (symmetric : Bool), ((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N * Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1)) ≤ InexactRealizations.Gains.operatorGain h I symmetric :=
  @InexactRealizations.Gains.linearGain_le_operatorGain

theorem theorem_4_1_relative_lower : ∀ {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
  h.ChebyshevExact I → 2 ≤ N → ((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N * Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1)) ≤ InexactRealizations.Gains.localRelativeGain h I :=
  @InexactRealizations.Gains.linearGain_le_localRelativeGain

theorem theorem_4_1_hs_lower : ∀ {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
  h.ChebyshevExact I → 2 ≤ N → ∀ (symmetric : Bool), ((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N * Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1)) ≤ InexactRealizations.Gains.hsGain h I symmetric :=
  @InexactRealizations.Gains.linearGain_le_hsGain

theorem theorem_4_1_balanced_attainment : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N),
  (InexactRealizations.Balanced.history I N hN).spectralGain I = ((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N * Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1)) ∧
    InexactRealizations.Gains.localRelativeGain (InexactRealizations.Balanced.history I N hN) I = ((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N * Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1)) ∧
      (∀ (symmetric : Bool),
          InexactRealizations.Gains.operatorGain (InexactRealizations.Balanced.history I N hN) I symmetric = ((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N * Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1))) ∧
        ∀ (symmetric : Bool),
          InexactRealizations.Gains.hsGain (InexactRealizations.Balanced.history I N hN) I symmetric = ((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N * Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1)) :=
  @InexactRealizations.Balanced.linear_optima

theorem theorem_4_1_spectral_minimum : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  2 ≤ N → IsLeast {v | ∃ h : InexactRealizations.History N, h.ChebyshevExact I ∧ v = h.spectralGain I} (((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N * Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1))) :=
  @InexactRealizations.Balanced.spectral_minimum

theorem theorem_4_1_operator_minimum : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  2 ≤ N →
    ∀ (symmetric : Bool),
      IsLeast {v | ∃ h : InexactRealizations.History N, h.ChebyshevExact I ∧ v = InexactRealizations.Gains.operatorGain h I symmetric} (((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N * Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1))) :=
  @InexactRealizations.Balanced.operator_minimum

theorem theorem_4_1_relative_minimum : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  2 ≤ N → IsLeast {v | ∃ h : InexactRealizations.History N, h.ChebyshevExact I ∧ v = InexactRealizations.Gains.localRelativeGain h I} (((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N * Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1))) :=
  @InexactRealizations.Balanced.local_relative_minimum

theorem theorem_4_1_hs_minimum : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  2 ≤ N →
    ∀ (symmetric : Bool),
      IsLeast {v | ∃ h : InexactRealizations.History N, h.ChebyshevExact I ∧ v = InexactRealizations.Gains.hsGain h I symmetric} (((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N * Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1))) :=
  @InexactRealizations.Balanced.hs_minimum

private theorem aux1_actual_relative_eq_spectral {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (hN : 0 < N) (r : ℝ) (hr : 0 < r) :
    InexactRealizations.Budgets.localRelativeGain 2 h I r = h.spectralGain I := by
  have hh := theorem_4_1_actual_relative_operator_spectral h I hN r hr false
  exact hh.1.trans hh.2

theorem theorem_4_1_literal_relative_minimum (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (hN : 2 ≤ N) (r : ℝ) (hr : 0 < r) :
    IsLeast {v : ℝ | ∃ h : InexactRealizations.History N, h.terminal = I.residual N ∧
      v = InexactRealizations.Budgets.localRelativeGain 2 h I r}
      ((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N *
        Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1)) := by
  change IsLeast _ (InexactRealizations.Lower.linearGain I N)
  refine ⟨⟨InexactRealizations.Balanced.history I N hN, InexactRealizations.Balanced.history_exact I N hN, ?_⟩, ?_⟩
  · rw [aux1_actual_relative_eq_spectral _ I (by omega) r hr,
      InexactRealizations.Balanced.spectralGain_eq I N hN]
  · rintro _ ⟨h, he, rfl⟩
    rw [aux1_actual_relative_eq_spectral h I (by omega) r hr]
    exact h.linearGain_le_spectralGain I he hN

theorem theorem_4_1_literal_operator_minimum (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (hN : 2 ≤ N) (symmetric : Bool) :
    IsLeast {v : ℝ | ∃ h : InexactRealizations.History N, h.terminal = I.residual N ∧
      v = InexactRealizations.Budgets.operatorNormGain 2 h I symmetric}
      ((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N *
        Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1)) := by
  have heq (h : InexactRealizations.History N) :
      InexactRealizations.Budgets.operatorNormGain 2 h I symmetric = h.spectralGain I :=
    (theorem_4_1_actual_relative_operator_spectral h I (by omega) 1 zero_lt_one symmetric).2
  change IsLeast _ (InexactRealizations.Lower.linearGain I N)
  refine ⟨⟨InexactRealizations.Balanced.history I N hN, InexactRealizations.Balanced.history_exact I N hN, ?_⟩, ?_⟩
  · rw [heq, InexactRealizations.Balanced.spectralGain_eq I N hN]
  · rintro _ ⟨h, hh, rfl⟩
    rw [heq]
    exact h.linearGain_le_spectralGain I hh hN

theorem theorem_4_1_parity_rate : (fun N => √(InexactRealizations.Lower.linearCorrectionSq N) - 1) =O[Filter.atTop]
  fun N : ℕ => (1 : ℝ) / (N : ℝ) ^ 2 :=
  @InexactRealizations.Properties.linearCorrection_sub_one_isBigO

theorem theorem_4_1_parity_square_rate :
    (fun N : ℕ => (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1) - 1)
      =O[atTop] (fun N : ℕ => (1 : ℝ) / (N : ℝ) ^ 2) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hb := InexactRealizations.Properties.linearCorrectionSq_bounds hN
  change 1 ≤ (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1) ∧
    (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1) - 1 ≤ 1 / (N : ℝ) ^ 2 at hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hb.1),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2), one_mul]
  exact hb.2

end


section
/-! ## Section 4, p. 8, Displays (19)–(20) (the actual parity average)

The library's `omega` is the printed averaging weight `ϖ`, `psi` is Psi, and `normalizer`
is Z. The identities below state their exact formulas and recurrences.
-/
theorem display_19_balanced_recurrence (N j : ℕ) :
    InexactRealizations.Balanced.psi N 0 = 1 ∧
      InexactRealizations.Balanced.psi N 1 = Polynomial.Chebyshev.T ℝ 1 ∧
      InexactRealizations.Balanced.psi N (j + 2) = InexactRealizations.Balanced.psi N j +
        C (InexactRealizations.Balanced.omega N (j + 2)) *
          (Polynomial.Chebyshev.T ℝ (j + 2) - Polynomial.Chebyshev.T ℝ j) :=
  ⟨InexactRealizations.Balanced.psi_zero N, InexactRealizations.Balanced.psi_one N, InexactRealizations.Balanced.psi_add_two N j⟩

theorem display_19_balanced_normalizer (I : InexactRealizations.Operators.SpectralInterval) (N j : ℕ) :
    InexactRealizations.Balanced.normalizer I N j = (InexactRealizations.Balanced.psi N j).eval I.eta := rfl

theorem display_20_balanced_weights (N j : ℕ) :
    InexactRealizations.Balanced.omega N j = if j < 2 then 1 else
      if Even N then ((N : ℝ) + 2 - j - (j % 2 : ℕ)) / N else
      if Even j then ((N : ℝ) + 1) * ((N : ℝ) + 1 - j) / ((N : ℝ) ^ 2 + 1) else
      ((N : ℝ) + 2 - j) / ((N : ℝ) + 1) := rfl

private theorem aux1_remainder_sum (N j : ℕ) :
    InexactRealizations.Balanced.remainder N j = ∑ i ∈ Finset.range j,
      if i % 2 = j % 2 then C (InexactRealizations.Balanced.omega N i - InexactRealizations.Balanced.omega N (i + 2)) *
        Polynomial.Chebyshev.T ℝ i else 0 := by
  induction j using Nat.twoStepInduction with
  | zero => simp [InexactRealizations.Balanced.remainder]
  | one => simp [InexactRealizations.Balanced.remainder]
  | more j ih _ =>
    have hj : (j + 1) % 2 ≠ j % 2 := by omega
    rw [InexactRealizations.Balanced.remainder, ih]
    simp only [show j + 2 = j + 1 + 1 by omega, Finset.sum_range_succ]
    simp only [show (j + 1 + 1) % 2 = j % 2 by omega,
      hj, ite_false, ite_true, add_zero]

theorem display_19_balanced_expansion (N j : ℕ) :
    InexactRealizations.Balanced.psi N j =
      (∑ i ∈ Finset.range j,
        if i % 2 = j % 2 then C (InexactRealizations.Balanced.omega N i - InexactRealizations.Balanced.omega N (i + 2)) *
          Polynomial.Chebyshev.T ℝ i else 0) +
      C (InexactRealizations.Balanced.omega N j) * Polynomial.Chebyshev.T ℝ j := by
  rw [InexactRealizations.Balanced.psi, aux1_remainder_sum]

theorem text_balanced_mass_formula (I : InexactRealizations.Operators.SpectralInterval) (N j : ℕ) :
    InexactRealizations.Balanced.normalizer I N j - InexactRealizations.Balanced.omega N (j + 2) * I.den j =
      ∑ i ∈ Finset.range (j + 1),
        if i % 2 = j % 2 then
          (InexactRealizations.Balanced.omega N i - InexactRealizations.Balanced.omega N (i + 2)) * I.den i else 0 := by
  rw [Finset.sum_range_succ]
  simp only [ite_true]
  rw [InexactRealizations.Balanced.normalizer, display_19_balanced_expansion]
  simp only [eval_add, eval_finsetSum, eval_mul, eval_C]
  simp_rw [apply_ite (Polynomial.eval I.eta)]
  simp only [eval_mul, eval_C, eval_zero]
  change (∑ i ∈ Finset.range j,
      if i % 2 = j % 2 then (InexactRealizations.Balanced.omega N i - InexactRealizations.Balanced.omega N (i + 2)) * I.den i else 0) +
      InexactRealizations.Balanced.omega N j * I.den j - InexactRealizations.Balanced.omega N (j + 2) * I.den j = _
  ring
end

section
/-! ## Section 4, p. 8, Displays (19)–(21) (Balanced factor bounds)

`psi`, `omega` (printed `ϖ`) and `normalizer` are the constructed parity averages and their exact normalizers. Positive tail factors give the same actual Balanced responses.
-/

theorem text_balanced_factorization : ∀ (N : ℕ),
  2 ≤ N →
    ∀ (x y : ℝ),
      ∑ s ∈ Finset.range N,
          Polynomial.eval x (InexactRealizations.Balanced.factor N s) * Polynomial.eval y (InexactRealizations.Balanced.psi N s) =
        ((if x = y then (Polynomial.Chebyshev.T ℝ N).derivative.eval x else ((Polynomial.Chebyshev.T ℝ N).eval x - (Polynomial.Chebyshev.T ℝ N).eval y) / (x - y)) / 2) :=
  @InexactRealizations.Balanced.factorization


private theorem aux1_positive_coefficients {p : ℝ[X]} (hp : InexactRealizations.Balanced.ChebPositive p) :
    ∃ m : ℕ, ∃ degrees : Fin m → ℕ, ∃ weights : Fin m → ℝ,
      (∀ i, 0 ≤ weights i) ∧ p = ∑ i, C (weights i) * Polynomial.Chebyshev.T ℝ (degrees i) := by
  induction hp with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | term n => exact ⟨1, fun _ => n, fun _ => 1, fun _ => zero_le_one, by simp⟩
  | add hp hq ihp ihq =>
    obtain ⟨m, d, a, ha, he⟩ := ihp
    obtain ⟨n, e, b, hb, hf⟩ := ihq
    refine ⟨m + n, Fin.addCases d e, Fin.addCases a b, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun k => ?_) (fun k => ?_) i
      · simpa only [Fin.addCases_left] using ha k
      · simpa only [Fin.addCases_right] using hb k
    · rw [he, hf, Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right]
  | scale c hc hp ih =>
    obtain ⟨m, d, a, ha, he⟩ := ih
    refine ⟨m, d, fun i => c * a i, fun i => mul_nonneg hc (ha i), ?_⟩
    rw [he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul]
    ring

theorem text_balanced_positive_factors {N j : ℕ} (hN : 2 ≤ N) (hj : j < N) :
    ∃ m : ℕ, ∃ degrees : Fin m → ℕ, ∃ weights : Fin m → ℝ,
      (∀ i, 0 ≤ weights i) ∧ InexactRealizations.Balanced.factor N j =
        ∑ i, C (weights i) * Polynomial.Chebyshev.T ℝ (degrees i) :=
  aux1_positive_coefficients (InexactRealizations.Balanced.factor_positive hN hj)

theorem text_balanced_psi_convex_coefficients {N j : ℕ} (hN : 2 ≤ N) (hj : j < N) :
    ∃ m : ℕ, ∃ degrees : Fin m → ℕ, ∃ weights : Fin m → ℝ,
      (∀ i, 0 ≤ weights i) ∧ InexactRealizations.Balanced.psi N j =
        (∑ i, C (weights i) * Polynomial.Chebyshev.T ℝ (degrees i)) ∧
          ∑ i, weights i = 1 := by
  obtain ⟨m, degrees, weights, hw, hp⟩ := aux1_positive_coefficients (InexactRealizations.Balanced.psi_positive hN hj)
  refine ⟨m, degrees, weights, hw, hp, ?_⟩
  have hh := congrArg (fun p : ℝ[X] => p.eval 1) hp
  simpa only [eval_finsetSum, eval_mul, eval_C, Polynomial.Chebyshev.T_eval_one,
    mul_one, InexactRealizations.Balanced.psi_eval_one] using hh.symm

theorem text_balanced_factor_bound : ∀ {N s : ℕ},
  2 ≤ N →
    s < N →
      ∀ {x : ℝ},
        |x| ≤ 1 → |Polynomial.eval x (InexactRealizations.Balanced.factor N s)| ≤ Polynomial.eval 1 (InexactRealizations.Balanced.factor N s) :=
  @InexactRealizations.Balanced.factor_bound

theorem display_21_endpoint_products : ∀ {N s : ℕ},
  2 ≤ N → s < N → Polynomial.eval 1 (InexactRealizations.Balanced.factor N s) = (if Even N then (N : ℝ) / 2 else if Even s then ((N : ℝ) ^ 2 + 1) / (2 * ((N : ℝ) + 1)) else ((N : ℝ) + 1) / 2) :=
  @InexactRealizations.Balanced.factor_eval_one

theorem display_21_actual_products (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (hN : 2 ≤ N) (j : Fin N) :
    ((InexactRealizations.Balanced.history I N hN).chartFactor I j).eval 1 *
      ((InexactRealizations.Balanced.history I N hN).chartQuery I j).eval 1 =
        if Even N then (N : ℝ) / 2 else
          if Even j.val then ((N : ℝ) ^ 2 + 1) / (2 * ((N : ℝ) + 1)) else ((N : ℝ) + 1) / 2 := by
  rw [InexactRealizations.Balanced.history_chartFactor, InexactRealizations.Balanced.history_chartQuery]
  simp only [InexactRealizations.Balanced.responseFactor, eval_mul, eval_C,
    InexactRealizations.Balanced.psi_eval_one, mul_one, InexactRealizations.Balanced.factor_eval_one hN j.isLt]
  have hz := (InexactRealizations.Balanced.normalizer_pos I hN j.isLt).ne'
  change InexactRealizations.Balanced.normalizer I N j.val * InexactRealizations.Balanced.classMass N j.val *
    (1 / InexactRealizations.Balanced.normalizer I N j.val) = InexactRealizations.Balanced.classMass N j.val
  field_simp

theorem text_balanced_actual_response_coefficients (I : InexactRealizations.Operators.SpectralInterval)
    (N : ℕ) (hN : 2 ≤ N) (j : Fin N) :
    ∃ m : ℕ, ∃ degrees : Fin m → ℕ, ∃ weights : Fin m → ℝ,
      (∀ i, 0 ≤ weights i) ∧ (InexactRealizations.Balanced.history I N hN).chartFactor I j =
        ∑ i, C (weights i) * Polynomial.Chebyshev.T ℝ (degrees i) := by
  rw [InexactRealizations.Balanced.history_chartFactor]
  exact aux1_positive_coefficients (InexactRealizations.Balanced.ChebPositive.scale _
    (InexactRealizations.Balanced.normalizer_pos I hN j.isLt).le (InexactRealizations.Balanced.factor_positive hN j.isLt))

theorem text_balanced_both_peaks (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (hN : 2 ≤ N) (j : Fin N) (lam : ℝ) (hlam : lam ∈ Set.Icc I.mu I.L) :
    |((InexactRealizations.Balanced.history I N hN).response j).eval lam| ≤
        -((InexactRealizations.Balanced.history I N hN).response j).eval I.mu ∧
      |((InexactRealizations.Balanced.history I N hN).query j).eval lam| ≤
        ((InexactRealizations.Balanced.history I N hN).query j).eval I.mu := by
  rw [InexactRealizations.Balanced.response_endpoint, neg_neg, InexactRealizations.Balanced.query_endpoint_physical]
  exact ⟨InexactRealizations.Balanced.response_bound I N hN j hlam,
    InexactRealizations.Balanced.query_bound_physical I N hN j hlam⟩

theorem display_21_energy : ∀ {N : ℕ},
  2 ≤ N → ∑ s ∈ Finset.range N, (if Even N then (N : ℝ) / 2 else if Even s then ((N : ℝ) ^ 2 + 1) / (2 * ((N : ℝ) + 1)) else ((N : ℝ) + 1) / 2) ^ 2 = ↑N ^ 3 / 4 * InexactRealizations.Lower.linearCorrectionSq N :=
  @InexactRealizations.Balanced.classMass_energy

theorem text_balanced_weights_positive : ∀ {N s : ℕ}, 2 ≤ N → s < N → 0 < InexactRealizations.Balanced.omega N s :=
  @InexactRealizations.Balanced.omega_pos

theorem text_balanced_weights_decrease : ∀ {N s : ℕ},
  2 ≤ N → s + 2 < N → InexactRealizations.Balanced.omega N (s + 2) ≤ InexactRealizations.Balanced.omega N s :=
  @InexactRealizations.Balanced.omega_add_two_le

theorem text_balanced_normalizers : ∀ {N s : ℕ},
  2 ≤ N → s < N → ∀ {x : ℝ}, 1 ≤ x → 1 ≤ Polynomial.eval x (InexactRealizations.Balanced.psi N s) :=
  @InexactRealizations.Balanced.one_le_psi_eval

end


section
/-! ## Algorithm 2 (Balanced Chebyshev in averaged-Prefix form), p. 9

`AveragedBalanced.program` is the actual printed nine-register program. It implements the concrete Balanced history for every oracle, with safe ratio preparation and exactly N calls.
-/

theorem algorithm_2_preparation : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  2 ≤ N →
    0 < I.eta ∧
      0 < I.L + I.mu ∧
        0 < I.delta ∧
          (∀ (j : ℕ), 0 < 2 * I.eta - InexactRealizations.Algorithms.AveragedBalanced.ratio I j) ∧
            (∀ (s : Fin N),
                0 < InexactRealizations.Algorithms.AveragedBalanced.zeta I N ↑s ∧
                  0 < InexactRealizations.Algorithms.AveragedBalanced.theta I N ↑s) ∧
              ∀ (s : ℕ),
                2 ≤ s → s + 2 < N → 0 < InexactRealizations.Algorithms.AveragedBalanced.zeta I N s - InexactRealizations.Balanced.omega N (s + 2) :=
  @InexactRealizations.Algorithms.AveragedBalanced.preparation_defined

theorem algorithm_2_queries : ∀ {E : Type u_1} [_inst : AddCommGroup E]
  [_inst_1 : Module ℝ E] (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (oracle : Fin N → E → E) (initial : E)
  (s : Fin N),
  (InexactRealizations.Algorithms.AveragedBalanced.journalProgram I N).queryAt oracle initial s =
    (InexactRealizations.Balanced.history I N hN).oracleQuery initial oracle s :=
  @InexactRealizations.Algorithms.AveragedBalanced.journal_balanced_queries

theorem algorithm_2_output : ∀ {E : Type u_1} [_inst : AddCommGroup E]
  [_inst_1 : Module ℝ E] (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (oracle : Fin N → E → E) (initial : E),
  (InexactRealizations.Algorithms.AveragedBalanced.journalProgram I N).output oracle initial =
    (InexactRealizations.Balanced.history I N hN).oracleOutput initial oracle :=
  @InexactRealizations.Algorithms.AveragedBalanced.journal_balanced_output

theorem algorithm_2_physical_response : ∀ {E : Type u_1} [_inst : AddCommGroup E]
  [_inst_1 : Module ℝ E] (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (H : E →ₗ[ℝ] E) (initial : E)
  (noise : Fin N → E),
  (InexactRealizations.Algorithms.AveragedBalanced.journalProgram I N).output (fun s y => H y + noise s) initial =
    ((Polynomial.aeval H) (I.residual N)) initial +
      ∑ s, ((Polynomial.aeval H) ((InexactRealizations.Balanced.history I N hN).response s)) (noise s) :=
  @InexactRealizations.Algorithms.AveragedBalanced.journal_balanced_physical_response

theorem algorithm_2_calls : ∀ {E : Type u_1} [_inst : AddCommGroup E]
  [_inst_1 : Module ℝ E] (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (oracle : Fin N → E → E) (initial : E),
  ((InexactRealizations.Algorithms.AveragedBalanced.journalProgram I N).run oracle initial).calls = N :=
  @InexactRealizations.Algorithms.AveragedBalanced.journal_balanced_oracle_calls

theorem algorithm_2_storage : Fintype.card (Fin 9) = 9 :=
  @InexactRealizations.Algorithms.AveragedBalanced.journal_balanced_vector_slots

theorem algorithm_2_all_prefix_states {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (oracle : Fin N → E → E)
    (initial : E) (j : ℕ) (hj : j ≤ N) :
    ∃ values : Fin 9 → E, (InexactRealizations.Algorithms.AveragedBalanced.journalProgram I N).runPrefix oracle initial j =
      ⟨values, j⟩ := by
  refine ⟨((InexactRealizations.Algorithms.AveragedBalanced.journalProgram I N).runPrefix oracle initial j).vectors, ?_⟩
  apply InexactRealizations.Algorithms.RegisterState.ext
  · rfl
  · exact InexactRealizations.Algorithms.RegisterProgram.runPrefix_calls _ _ _ j hj

theorem algorithm_2_ratio : ∀ (I : InexactRealizations.Operators.SpectralInterval) (j : ℕ),
  InexactRealizations.Algorithms.AveragedBalanced.ratio I j = I.den j / I.den (j + 1) :=
  @InexactRealizations.Algorithms.AveragedBalanced.ratio_eq

theorem algorithm_2_zeta : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ),
  InexactRealizations.Algorithms.AveragedBalanced.zeta I N s = InexactRealizations.Balanced.normalizer I N s / I.den s :=
  @InexactRealizations.Algorithms.AveragedBalanced.zeta_eq

theorem algorithm_2_theta : ∀ (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ},
  2 ≤ N →
    s < N →
      InexactRealizations.Algorithms.AveragedBalanced.theta I N s =
        InexactRealizations.Balanced.omega N s * I.den s / InexactRealizations.Balanced.normalizer I N s :=
  @InexactRealizations.Algorithms.AveragedBalanced.theta_eq

end

section
/-! ## Section 4, p. 9, text before Display (22) (convex Prefix averages)

The formula is for the query of the constructed Balanced history itself.
The lower-parity Prefix weights, their positivity and the total normalized
mass are explicit; no chosen average or assumed invariant is an input.
The printed M_j is the mass identity in the preceding block.
-/
theorem text_balanced_query_average (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (hN : 2 ≤ N) (j : Fin N) (lam : ℝ) :
    ((InexactRealizations.Balanced.history I N hN).query j).eval lam =
      ((∑ i ∈ Finset.range j.val,
        if i % 2 = j.val % 2 then
          (InexactRealizations.Balanced.omega N i - InexactRealizations.Balanced.omega N (i + 2)) *
            (I.den i * (I.residual i).eval lam) else 0) +
          InexactRealizations.Balanced.omega N j.val * (I.den j.val * (I.residual j.val).eval lam)) /
        InexactRealizations.Balanced.normalizer I N j.val := by
  rw [InexactRealizations.Balanced.history_query_eval, display_19_balanced_expansion]
  simp only [eval_add, eval_finsetSum, eval_mul, eval_C]
  simp_rw [apply_ite (Polynomial.eval (I.z lam))]
  simp only [eval_mul, eval_C, eval_zero]
  simp_rw [← InexactRealizations.Algorithms.AveragedBalanced.prefix_scaled I _ lam]

theorem text_balanced_average_coefficients_nonnegative (I : InexactRealizations.Operators.SpectralInterval)
    (N : ℕ) (hN : 2 ≤ N) (j : Fin N) (i : ℕ) (hij : i < j.val)
    (hp : i % 2 = j.val % 2) :
    0 ≤ (InexactRealizations.Balanced.omega N i - InexactRealizations.Balanced.omega N (i + 2)) * I.den i /
      InexactRealizations.Balanced.normalizer I N j.val := by
  have hs : i + 2 < N := by omega
  have hd := sub_nonneg.mpr (InexactRealizations.Balanced.omega_add_two_le hN hs)
  have hc := (I.den_pos i).le
  have hz := (InexactRealizations.Balanced.normalizer_pos I hN j.isLt).le
  exact div_nonneg (mul_nonneg hd hc) hz

theorem text_balanced_query_coefficients_total (I : InexactRealizations.Operators.SpectralInterval)
    (N : ℕ) (hN : 2 ≤ N) (j : Fin N) :
    ((∑ i ∈ Finset.range j.val,
        if i % 2 = j.val % 2 then
          (InexactRealizations.Balanced.omega N i - InexactRealizations.Balanced.omega N (i + 2)) * I.den i else 0) +
        InexactRealizations.Balanced.omega N j.val * I.den j.val) /
      InexactRealizations.Balanced.normalizer I N j.val = 1 := by
  have hh := text_balanced_query_average I N hN j 0
  simpa only [InexactRealizations.History.query_eval_zero, InexactRealizations.Operators.SpectralInterval.residual_eval_zero,
    mul_one] using hh.symm

theorem text_balanced_theta_interval (I : InexactRealizations.Operators.SpectralInterval)
    (N : ℕ) (hN : 2 ≤ N) (j : Fin N) :
    0 < InexactRealizations.Algorithms.AveragedBalanced.theta I N j.val ∧
      InexactRealizations.Algorithms.AveragedBalanced.theta I N j.val ≤ 1 :=
  InexactRealizations.Algorithms.AveragedBalanced.theta_unit I hN j.isLt

theorem text_balanced_ratio_ranges (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (hN : 2 ≤ N) (j : Fin N) :
    (0 < InexactRealizations.Algorithms.AveragedBalanced.ratio I j.val ∧
      InexactRealizations.Algorithms.AveragedBalanced.ratio I j.val < 1) ∧
    (0 < InexactRealizations.Algorithms.AveragedBalanced.zeta I N j.val ∧
      InexactRealizations.Algorithms.AveragedBalanced.zeta I N j.val ≤ 1) ∧
    (0 < InexactRealizations.Algorithms.AveragedBalanced.alpha I j.val ∧
      InexactRealizations.Algorithms.AveragedBalanced.alpha I j.val < 4 / I.delta) ∧
    (0 ≤ InexactRealizations.Algorithms.AveragedBalanced.beta I j.val ∧
      InexactRealizations.Algorithms.AveragedBalanced.beta I j.val < 1) :=
  ⟨InexactRealizations.Algorithms.AveragedBalanced.ratio_unit I j.val,
    InexactRealizations.Algorithms.AveragedBalanced.zeta_unit I hN j.isLt,
    InexactRealizations.Algorithms.AveragedBalanced.alpha_bounds I j.val,
    InexactRealizations.Algorithms.AveragedBalanced.beta_bounds I j.val⟩

theorem text_balanced_phi_interval (I : InexactRealizations.Operators.SpectralInterval) (N j : ℕ)
    (hN : 2 ≤ N) (hj : 2 ≤ j) (hjN : j + 2 < N) :
    0 < InexactRealizations.Algorithms.AveragedBalanced.phi I N j ∧
      InexactRealizations.Algorithms.AveragedBalanced.phi I N j ≤ 1 :=
  InexactRealizations.Algorithms.AveragedBalanced.phi_unit I hN hj hjN

theorem text_balanced_even_startup (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (hN : 0 < N) (hEven : Even N) :
    InexactRealizations.Balanced.normalizer I N 0 - InexactRealizations.Balanced.omega N 2 * I.den 0 = 0 ∧
      InexactRealizations.Algorithms.AveragedBalanced.theta I N 2 = 1 := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hw : InexactRealizations.Balanced.omega N 2 = 1 := by
    simp [InexactRealizations.Balanced.omega, hEven, hn]
  constructor
  · simp [hw]
  · simp [InexactRealizations.Algorithms.AveragedBalanced.theta, InexactRealizations.Algorithms.AveragedBalanced.zeta, hw]
end

section
/-! ## Section 4, p. 9, Display (22) (Prefix gain)

The Prefix spectral and physical gains have the printed exact finite expression and asymptotic constant. The sine-Jacobi decimal comparison is a cited numerical illustration and is excluded.
-/

theorem display_22_classical_gain : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  0 < N →
    (InexactRealizations.Classical.history I N).spectralGain I =
      I.epsilon N / I.delta * √(4 * ↑N ^ 2 + 16 * ∑ m ∈ Finset.range N, (m : ℝ) ^ 2) :=
  @InexactRealizations.Classical.spectralGain_exact

theorem text_classical_operator : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  0 < N →
    ∀ (symmetric : Bool),
      InexactRealizations.Gains.operatorGain (InexactRealizations.Classical.history I N) I symmetric =
        (InexactRealizations.Classical.history I N).spectralGain I :=
  @InexactRealizations.Classical.operatorGain_eq

theorem text_classical_relative : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  0 < N →
    InexactRealizations.Gains.localRelativeGain (InexactRealizations.Classical.history I N) I = (InexactRealizations.Classical.history I N).spectralGain I :=
  @InexactRealizations.Classical.localRelativeGain_eq

theorem display_22_classical_asymptotic : ∀ (I : InexactRealizations.Operators.SpectralInterval),
  Filter.Tendsto (fun N => (InexactRealizations.Classical.history I N).spectralGain I * I.delta / (I.epsilon N * ↑N * √↑N))
    Filter.atTop (nhds (4 / √3)) :=
  @InexactRealizations.Classical.gain_asymptotic

end

section
/-! ## Section 4, p. 9, text after Display (22) (incompatible optima)

The exact endpoint scales have S_N > D_N at every N >= 2. For even horizons the additive MSE and linear optima cannot both hold. The direct positive-mass proof establishes the same printed conclusion.
-/

theorem text_scales_strict : ∀ (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ},
  2 ≤ N → (2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) < ((1 - I.epsilon N) / I.mu) :=
  @InexactRealizations.Properties.derivativeScale_lt_additiveScale

theorem text_even_incompatible : ∀ {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
  h.ChebyshevExact I →
    2 ≤ N →
      Even N →
        ∀ (r σ : ℝ),
          0 ≤ r →
            0 < σ →
              ¬(InexactRealizations.Risk.mseRisk h I r σ = ((I.epsilon N) ^ 2 * r ^ 2 + σ ^ 2 * ((1 - I.epsilon N) / I.mu) ^ 2 / N) ∧
                  h.spectralGain I = ((2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) / Real.sqrt N * Real.sqrt (if Odd N then 1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2) else 1))) :=
  @InexactRealizations.Properties.even_optima_incompatible

theorem text_scale_ratio : ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
  0 < N → ((1 - I.epsilon N) / I.mu) / (2 * I.epsilon N * (N : ℝ) ^ 2 / I.delta) = (I.den N - 1) / (↑N ^ 2 * (I.eta - 1)) :=
  @InexactRealizations.Prose.corner_scale_ratio

end

end Part1

section Part2
/-! Exact journal statements for rounding, call budgets, spectral averages,
the general experimental models and Appendix A. Numerical observations and
bibliographic background are the author-excluded material described at their
printed locations. All notation refers to the actual library constructions. -/

open Polynomial MeasureTheory Filter Topology Real
open scoped BigOperators ENNReal NNReal
universe uP2a uP2b uP2c uP2d
section
/-! ## Display (23) and Theorem 4.2 (Exact error identity), p. 10

The six-register recursion constructs the actual execution from the initial state
and arbitrary oracle and local error streams. The operational equations and the
terminal identity refer to this concrete execution. Every solution agrees with it
on the printed indices. Values beyond the active averaging range are total
extensions and are not part of the uniqueness claim. The stored state is centered
only in the final formula.
-/

open InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Roundoff

structure LocalRegisters (E : Type*) where
  current : E
  previous : E
  olderAverage : E
  newerAverage : E
  olderGradient : E
  newerGradient : E

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def localQuery (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ)
    (ell : LocalErrorStreams E) (r : LocalRegisters E) : E :=
  computedQuery (theta I N s) r.current r.olderAverage (ell.query s)

def localAnswer (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ)
    (H : E →ₗ[ℝ] E) (target : E) (ell : LocalErrorStreams E) (r : LocalRegisters E) : E :=
  computedAnswer H target (localQuery I N s ell r) (ell.oracle s)

def localRecovered (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ)
    (H : E →ₗ[ℝ] E) (target : E) (ell : LocalErrorStreams E) (r : LocalRegisters E) : E :=
  recoveredGradient (theta I N s) r.olderGradient
    (localAnswer I N s H target ell r) (ell.recovery s)

def localAverage (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ)
    (ell : LocalErrorStreams E) (r : LocalRegisters E) : E :=
  updatedAverage (phi I N s) r.olderAverage r.current (ell.average s)

def localGradient (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ)
    (H : E →ₗ[ℝ] E) (target : E) (ell : LocalErrorStreams E) (r : LocalRegisters E) : E :=
  updatedAverage (phi I N s) r.olderGradient
    (localRecovered I N s H target ell r) (ell.gradient s)

def localAdvance (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ)
    (H : E →ₗ[ℝ] E) (target : E) (ell : LocalErrorStreams E) (r : LocalRegisters E) :
    LocalRegisters E where
  current := (1 + beta I s) • r.current - beta I s • r.previous -
    alpha I s • localRecovered I N s H target ell r + ell.state (s + 1)
  previous := r.current
  olderAverage := r.newerAverage
  newerAverage := localAverage I N s ell r
  olderGradient := r.newerGradient
  newerGradient := localGradient I N s H target ell r

def canonicalLocalRegisters (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (H : E →ₗ[ℝ] E) (initial target : E) (ell : LocalErrorStreams E) : ℕ → LocalRegisters E
  | 0 => ⟨initial, initial, 0, 0, 0, 0⟩
  | s + 1 => localAdvance I N s H target ell
      (canonicalLocalRegisters I N H initial target ell s)

private theorem canonical_previous (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (H : E →ₗ[ℝ] E) (initial target : E) (ell : LocalErrorStreams E) (s : ℕ) :
    (canonicalLocalRegisters I N H initial target ell s).previous =
      (canonicalLocalRegisters I N H initial target ell (s - 1)).current := by
  cases s <;> rfl

private theorem canonical_older_average (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (H : E →ₗ[ℝ] E) (initial target : E) (ell : LocalErrorStreams E) (s : ℕ) :
    (canonicalLocalRegisters I N H initial target ell s).olderAverage =
      earlierAverage (fun t => localAverage I N t ell
        (canonicalLocalRegisters I N H initial target ell t)) s := by
  cases s with
  | zero => rfl
  | succ s =>
    cases s with
    | zero => rfl
    | succ s =>
      simp only [earlierAverage, show ¬s + 1 + 1 < 2 by omega, ite_false,
        show s + 1 + 1 - 2 = s by omega]
      rfl

private theorem canonical_older_gradient (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (H : E →ₗ[ℝ] E) (initial target : E) (ell : LocalErrorStreams E) (s : ℕ) :
    (canonicalLocalRegisters I N H initial target ell s).olderGradient =
      earlierAverage (fun t => localGradient I N t H target ell
        (canonicalLocalRegisters I N H initial target ell t)) s := by
  cases s with
  | zero => rfl
  | succ s =>
    cases s with
    | zero => rfl
    | succ s =>
      simp only [earlierAverage, show ¬s + 1 + 1 < 2 by omega, ite_false,
        show s + 1 + 1 - 2 = s by omega]
      rfl

/-- The deterministic execution constructed from the six printed operations. -/
def canonicalLocalExecution (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (H : E →ₗ[ℝ] E) (initial target : E) (ell : LocalErrorStreams E) :
    LocalExecution I N H initial target ell where
  x s := (canonicalLocalRegisters I N H initial target ell s).current
  y s := localQuery I N s ell (canonicalLocalRegisters I N H initial target ell s)
  g s := localAnswer I N s H target ell (canonicalLocalRegisters I N H initial target ell s)
  recovered s := localRecovered I N s H target ell (canonicalLocalRegisters I N H initial target ell s)
  average s := localAverage I N s ell (canonicalLocalRegisters I N H initial target ell s)
  gradient s := localGradient I N s H target ell (canonicalLocalRegisters I N H initial target ell s)
  initial_eq := rfl
  query_eq s _ := by rw [← canonical_older_average]; rfl
  answer_eq _ _ := rfl
  recovered_eq s _ := by rw [← canonical_older_gradient]; rfl
  average_eq s _ := by rw [← canonical_older_average]; rfl
  gradient_eq s _ := by rw [← canonical_older_gradient]; rfl
  state_eq s _ := by rw [← canonical_previous]; rfl

private theorem localExecution_agree_prefix (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (H : E →ₗ[ℝ] E) (initial target : E) (ell : LocalErrorStreams E)
    (v w : LocalExecution I N H initial target ell) :
    ∀ s, s ≤ N → v.x s = w.x s ∧
      (s < N → v.y s = w.y s ∧ v.g s = w.g s ∧ v.recovered s = w.recovered s ∧
        (s + 2 < N → v.average s = w.average s ∧ v.gradient s = w.gradient s)) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro hs
    have hx : v.x s = w.x s := by
      cases s with
      | zero => rw [v.initial_eq, w.initial_eq]
      | succ s =>
        have hsN : s < N := by omega
        have hprev := ih s (by omega) (by omega)
        have hprevious := ih (s - 1) (by omega) (by omega)
        rw [v.state_eq s hsN, w.state_eq s hsN, hprev.1, hprevious.1,
          (hprev.2 hsN).2.2.1]
    refine ⟨hx, ?_⟩
    intro hsN
    have ha : earlierAverage v.average s = earlierAverage w.average s := by
      by_cases hsmall : s < 2
      · simp only [earlierAverage, hsmall, ite_true]
      · have hprev := (ih (s - 2) (by omega) (by omega)).2 (by omega)
        simp only [earlierAverage, hsmall, ite_false]
        exact (hprev.2.2.2 (by omega)).1
    have hg : earlierAverage v.gradient s = earlierAverage w.gradient s := by
      by_cases hsmall : s < 2
      · simp only [earlierAverage, hsmall, ite_true]
      · have hprev := (ih (s - 2) (by omega) (by omega)).2 (by omega)
        simp only [earlierAverage, hsmall, ite_false]
        exact (hprev.2.2.2 (by omega)).2
    have hy : v.y s = w.y s := by rw [v.query_eq s hsN, w.query_eq s hsN, ha, hx]
    have hanswer : v.g s = w.g s := by rw [v.answer_eq s hsN, w.answer_eq s hsN, hy]
    have hrec : v.recovered s = w.recovered s := by
      rw [v.recovered_eq s hsN, w.recovered_eq s hsN, hg, hanswer]
    refine ⟨hy, hanswer, hrec, ?_⟩
    intro hsav
    constructor
    · rw [v.average_eq s hsav, w.average_eq s hsav, ha, hx]
    · rw [v.gradient_eq s hsav, w.gradient_eq s hsav, hg, hrec]

/-- The prescribed data have exactly one execution on all article-used indices. -/
theorem canonicalLocalExecution_unique (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (H : E →ₗ[ℝ] E) (initial target : E) (ell : LocalErrorStreams E)
    (v : LocalExecution I N H initial target ell) :
    (∀ s, s ≤ N → v.x s = (canonicalLocalExecution I N H initial target ell).x s) ∧
    (∀ s, s < N → v.y s = (canonicalLocalExecution I N H initial target ell).y s ∧
      v.g s = (canonicalLocalExecution I N H initial target ell).g s ∧
      v.recovered s = (canonicalLocalExecution I N H initial target ell).recovered s) ∧
    (∀ s, s + 2 < N → v.average s = (canonicalLocalExecution I N H initial target ell).average s ∧
      v.gradient s = (canonicalLocalExecution I N H initial target ell).gradient s) := by
  have hp := localExecution_agree_prefix I N H initial target ell v
    (canonicalLocalExecution I N H initial target ell)
  refine ⟨fun s hs => (hp s hs).1, ?_, ?_⟩
  · intro s hs
    have h := (hp s hs.le).2 hs
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · intro s hs
    exact ((hp s (by omega)).2 (by omega)).2.2.2 hs

/-- Display (23), p. 10, for the recursively constructed execution. -/
theorem display_23_operational_equations
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E) (initial target : E)
    (ell : LocalErrorStreams E) :
    let v := canonicalLocalExecution I N H initial target ell
    v.x 0 = initial ∧
    (∀ s, s < N → v.y s = earlierAverage v.average s + theta I N s •
      (v.x s - earlierAverage v.average s) + ell.query s) ∧
    (∀ s, s < N → v.g s = H (v.y s - target) + ell.oracle s) ∧
    (∀ s, s < N → v.recovered s = earlierAverage v.gradient s +
      (theta I N s)⁻¹ • (v.g s - earlierAverage v.gradient s) + ell.recovery s) ∧
    (∀ s, s + 2 < N → v.average s = earlierAverage v.average s +
      phi I N s • (v.x s - earlierAverage v.average s) + ell.average s) ∧
    (∀ s, s + 2 < N → v.gradient s = earlierAverage v.gradient s +
      phi I N s • (v.recovered s - earlierAverage v.gradient s) + ell.gradient s) ∧
    (∀ s, s < N → v.x (s + 1) = (1 + beta I s) • v.x s - beta I s • v.x (s - 1) -
      alpha I s • v.recovered s + ell.state (s + 1)) := by
  let v := canonicalLocalExecution I N H initial target ell
  exact ⟨v.initial_eq, v.query_eq, v.answer_eq, v.recovered_eq,
    v.average_eq, v.gradient_eq, v.state_eq⟩

theorem theorem_4_2_effective_errors {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E)
    (ell : InexactRealizations.Roundoff.LocalErrorStreams E) (s : ℕ) :
    InexactRealizations.Roundoff.hatNoise I N H ell s =
      ell.oracle s + H (ell.query s) + InexactRealizations.Algorithms.AveragedBalanced.theta I N s • ell.recovery s ∧
    InexactRealizations.Roundoff.averageNoise H ell s = ell.gradient s - H (ell.average s) := ⟨rfl, rfl⟩

/-- Theorem 4.2, p. 10: exact identity for the actual constructed execution,
with arbitrary prescribed errors and no solution supplied as an input. -/
theorem theorem_4_2_exact_identity
    (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (initial target : E) (ell : LocalErrorStreams E) :
    (canonicalLocalExecution I N H initial target ell).x N - target =
      ((Polynomial.aeval H) (I.residual N)) (initial - target) +
        ∑ s : Fin N, ((Polynomial.aeval H) ((InexactRealizations.Balanced.history I N hN).response s))
          (hatNoise I N H ell s.val) +
        ∑ s : Fin (N - 2), ((Polynomial.aeval H) (averageResponse I N s.val))
          (averageNoise H ell s.val) -
        ∑ s : Fin N, (alpha I s.val)⁻¹ •
          ((Polynomial.aeval H) ((InexactRealizations.Classical.history I N).response s)) (ell.state (s.val + 1)) :=
  InexactRealizations.Roundoff.exact_local_error_identity I hN H initial target ell
    (canonicalLocalExecution I N H initial target ell)


theorem theorem_4_2_response_peaks :
    ∀ (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N),
      (∀ (s : Fin N),
          ∀ lam ∈ Set.Icc I.mu I.L,
            |Polynomial.eval lam ((InexactRealizations.Balanced.history I N hN).response s)| ≤
              |Polynomial.eval I.mu ((InexactRealizations.Balanced.history I N hN).response s)|) ∧
        (∀ (s : Fin N),
            ∀ lam ∈ Set.Icc I.mu I.L,
              |Polynomial.eval lam ((InexactRealizations.Classical.history I N).response s)| ≤
                |Polynomial.eval I.mu ((InexactRealizations.Classical.history I N).response s)|) ∧
          (∀ (s : Fin (N - 2)),
              ∀ lam ∈ Set.Icc I.mu I.L,
                |Polynomial.eval lam (InexactRealizations.Roundoff.averageResponse I N ↑s)| ≤
                  Polynomial.eval I.mu (InexactRealizations.Roundoff.averageResponse I N ↑s)) ∧
            ∑ s : Fin N, |Polynomial.eval I.mu ((InexactRealizations.Balanced.history I N hN).response s)| = InexactRealizations.Lower.additiveScale I N ∧
              (∀ (s : Fin N),
                  |(InexactRealizations.Algorithms.AveragedBalanced.alpha I ↑s)⁻¹ *
                        Polynomial.eval I.mu ((InexactRealizations.Classical.history I N).response s)| =
                    (↑N - ↑↑s) * I.den (↑s + 1) / I.den N) ∧
                ∀ (s : Fin (N - 2)),
                  Polynomial.eval I.mu (InexactRealizations.Roundoff.averageResponse I N ↑s) =
                    4 * InexactRealizations.Algorithms.AveragedBalanced.mass I N (↑s + 2) * (((N - 1 - s.val) ^ 2 / 4 : ℕ) : ℝ) /
                      (I.delta * InexactRealizations.Balanced.omega N (↑s + 2) * I.den N) :=
  @InexactRealizations.Roundoff.journal_response_peaks

theorem text_4_printed_average_mass (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    InexactRealizations.Algorithms.AveragedBalanced.mass I N (s + 2) =
      InexactRealizations.Balanced.normalizer I N s - InexactRealizations.Balanced.omega N (s + 2) * I.den s := by
  rw [InexactRealizations.Algorithms.AveragedBalanced.mass_step, InexactRealizations.Algorithms.AveragedBalanced.mass]
  ring

theorem text_4_average_coefficient (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    InexactRealizations.Roundoff.averageScale I N s =
      4 * (InexactRealizations.Balanced.normalizer I N s - InexactRealizations.Balanced.omega N (s + 2) * I.den s) /
        (I.delta * InexactRealizations.Balanced.omega N (s + 2) * I.den N) := by
  unfold InexactRealizations.Roundoff.averageScale
  rw [text_4_printed_average_mass]

theorem display_23_startup (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (hs : s ≤ 1) :
    InexactRealizations.Algorithms.AveragedBalanced.theta I N s = 1 ∧
      InexactRealizations.Algorithms.AveragedBalanced.phi I N s = 1 := by
  simp only [InexactRealizations.Algorithms.AveragedBalanced.theta, InexactRealizations.Algorithms.AveragedBalanced.phi,
    show s < 2 by omega, ite_true, and_self]

theorem text_4_average_response :
    ∀ (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ),
      InexactRealizations.Roundoff.averageResponse I N s =
        ∑ i : Fin ((N - 1 - s) / 2), Polynomial.C (InexactRealizations.Roundoff.averageScale I N s) * InexactRealizations.Roundoff.physicalU I (N - 1 - s - 2 * (↑i + 1)) :=
  @InexactRealizations.Roundoff.averageResponse_polynomial

end

section
/-! ## Corollary 4.3 (Attainable accuracy), p. 10

Componentwise.Run records every individual rounded instruction, its componentwise relative error bound, the one-time scalar preparation and the actual step equations. The Compensated flag selects the printed compensated branch at every averaging step. The explicit constants make the printed first-order and quadratic terms uniform in dimension. Small nonnegative roundoff parameters are bounded by 1/2 and 1 only to give a concrete neighborhood for the printed expansion.
-/

theorem corollary_4_3_compensated :
    ∀ {ι : Type uP2a} [Fintype ι]
      {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ} {p : InexactRealizations.Accuracy.Execution.Prepared I N u}
      {H : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι} {initial target : EuclideanSpace ℝ ι} {hu : 0 ≤ u}
      (v : InexactRealizations.Accuracy.Componentwise.Run p H initial target uO hu),
      (∀ (s : Fin N) (hs : 2 ≤ s.val) (hv : s.val + 2 < N),
        ∃ op, (v.toNormed.stages s).averageOperations hs hv = Sum.inl op) →
        2 ≤ N →
          u ≤ 1 / 2 →
            0 ≤ uO →
              uO ≤ 1 →
                InexactRealizations.Analysis.Admissible I H →
                  ‖v.states N 0 - target‖ ≤
                    I.epsilon N * (1 + InexactRealizations.Accuracy.Execution.cubicConstant I.kappa * (u + uO) * ↑N ^ 3) *
                          ‖initial - target‖ +
                        (2 * (u + uO) * I.L * InexactRealizations.Lower.additiveScale I N + 8 * u * InexactRealizations.Accuracy.prefixFactor I N) *
                          ‖target‖ +
                      (u + uO) ^ 2 * InexactRealizations.Accuracy.Execution.quadraticConstant I.kappa N * (‖initial - target‖ + ‖target‖) :=
  @InexactRealizations.Accuracy.Componentwise.compensated_accuracy

theorem corollary_4_3_prefix_factor_definition (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    InexactRealizations.Accuracy.prefixFactor I N =
      ∑ s : Fin N, ((N : ℝ) - s.val) * I.den (s.val + 1) / I.den N := rfl

theorem corollary_4_3_additive_factor :
    ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
      I.L * InexactRealizations.Lower.additiveScale I N < I.kappa :=
  @InexactRealizations.Accuracy.additive_condition_bound

theorem corollary_4_3_prefix_factor :
    ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
      InexactRealizations.Accuracy.prefixFactor I N < (√I.kappa + 1) ^ 2 / 4 :=
  @InexactRealizations.Accuracy.prefixFactor_condition_bound

theorem corollary_4_3_uncompensated :
    ∀ {ι : Type uP2a} [Fintype ι]
      {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ} {p : InexactRealizations.Accuracy.Execution.Prepared I N u}
      {H : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι} {initial target : EuclideanSpace ℝ ι} {hu : 0 ≤ u}
      (v : InexactRealizations.Accuracy.Componentwise.Run p H initial target uO hu),
      (∀ (s : Fin N) (hs : 2 ≤ s.val) (hv : s.val + 2 < N),
        ∃ op, (v.toNormed.stages s).averageOperations hs hv = Sum.inr op) →
        2 ≤ N →
          u ≤ 1 / 2 →
            0 ≤ uO →
              uO ≤ 1 →
                InexactRealizations.Analysis.Admissible I H →
                  ‖v.states N 0 - target‖ ≤
                    I.epsilon N * (1 + 2 * InexactRealizations.Accuracy.Execution.cubicConstant I.kappa * (u + uO) * ↑N ^ 3) *
                          ‖initial - target‖ +
                        (2 * (u + uO) * I.L * InexactRealizations.Lower.additiveScale I N + 8 * u * InexactRealizations.Accuracy.prefixFactor I N +
                            u * I.L * InexactRealizations.Accuracy.UncompensatedWitness.averageFactor I N) *
                          ‖target‖ +
                      (u + uO) ^ 2 * InexactRealizations.Accuracy.Execution.uncompensatedQuadraticConstant I.kappa N *
                        (‖initial - target‖ + ‖target‖) :=
  @InexactRealizations.Accuracy.Componentwise.uncompensated_accuracy

theorem corollary_4_3_uncompensated_zero_corrections {J : Type*} [Fintype J]
    {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ} {u uO : ℝ}
    {p : InexactRealizations.Accuracy.Execution.Prepared I N u}
    {H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J} {initial target : EuclideanSpace ℝ J} {hu : 0 ≤ u}
    (v : InexactRealizations.Accuracy.Componentwise.Run p H initial target uO hu)
    (hc : ∀ (s : Fin N) (hs : 2 ≤ s.val) (hv : s.val + 2 < N),
      ∃ op, (v.toNormed.stages s).averageOperations hs hv = Sum.inr op)
    (n : ℕ) (hn : n ≤ N) : v.states n 4 = 0 ∧ v.states n 5 = 0 :=
  InexactRealizations.Accuracy.Execution.Run.uncompensated_corrections_zero v.toNormed hc n hn

theorem corollary_4_3_uncompensated_order :
    ∀ (I : InexactRealizations.Operators.SpectralInterval),
      4 ≤ I.kappa →
        ∀ᶠ (N : ℕ) in Filter.atTop,
          I.kappa * √I.kappa / 64 ≤ I.L * InexactRealizations.Accuracy.UncompensatedWitness.averageFactor I N ∧
            I.L * InexactRealizations.Accuracy.UncompensatedWitness.averageFactor I N ≤ I.kappa * √I.kappa / 2 :=
  @InexactRealizations.Accuracy.Uncompensated.averageFactor_eventual_order

theorem corollary_4_3_finite_and_attained_factors :
    ∀ (I : InexactRealizations.Operators.SpectralInterval),
      (∀ (N : ℕ),
          2 ≤ N →
            I.L * InexactRealizations.Accuracy.UncompensatedWitness.averageFactor I N ≤ ↑N * (I.kappa - 1) * √I.kappa / (4 * ↑N - 4)) ∧
        (∀ (eps : ℝ),
            0 < eps →
              ∀ᶠ (N : ℕ) in Filter.atTop,
                (√I.kappa - 1) ^ 2 * √I.kappa / 8 - eps ≤ I.L * InexactRealizations.Accuracy.UncompensatedWitness.averageFactor I N) ∧
          ∀ (N : ℕ),
            2 ≤ N →
              ∀ (rho : ℝ),
                0 ≤ rho →
                  Filter.Tendsto (fun u => |(InexactRealizations.Accuracy.UncompensatedWitness.atScale I N rho u).x N - rho| / u)
                    (nhdsWithin 0 (Set.Ioi 0)) (nhds (I.L * InexactRealizations.Accuracy.UncompensatedWitness.averageFactor I N * rho)) :=
  @InexactRealizations.Accuracy.Uncompensated.journal_average_factors

theorem corollary_4_3_admissible_instruction :
    ∀ (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) (rho : ℝ)
      {u : ℝ} (hu : 0 ≤ u),
      2 ≤ s →
        s + 2 < N →
          have v :=
            InexactRealizations.Accuracy.AverageExecution.states I N (InexactRealizations.Accuracy.UncompensatedWitness.hessian I.L)
              (Polynomial.C rho) (Polynomial.C rho) (InexactRealizations.Accuracy.UncompensatedWitness.rounding N) s;
          (InexactRealizations.Accuracy.UncompensatedWitness.atScale I N rho u).average s =
            (InexactRealizations.Accuracy.Uncompensated.lastAdditionStep N s (Polynomial.eval u v.x)
                (Polynomial.eval u (InexactRealizations.Accuracy.AverageExecution.oldAverage s v))
                (InexactRealizations.Algorithms.AveragedBalanced.phi I N s) u hu).result :=
  @InexactRealizations.Accuracy.Uncompensated.journal_witness_admissible

end

section
/-! ## Section 4, p. 10, text after Corollary 4.3 (classical recurrence)

The forced classical recurrence has no average channel, and its actual output uses precisely the Prefix physical responses. The two-sided order in Corollary 4.3 supplies the stated square-root condition-number penalty.
-/

theorem text_4_first_order_coefficient (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (u uO : ℝ) (hu : 0 < u) (huO : 0 ≤ uO) :
    2 * (u + uO) * I.L * InexactRealizations.Lower.additiveScale I N + 8 * u * InexactRealizations.Accuracy.prefixFactor I N <
      2 * (u + uO) * I.kappa + 2 * u * (Real.sqrt I.kappa + 1) ^ 2 := by
  have ha := InexactRealizations.Accuracy.additive_condition_bound I N
  have hf := InexactRealizations.Accuracy.prefixFactor_condition_bound I N
  have hmul := mul_lt_mul_of_pos_left ha (show 0 < 2 * (u + uO) by linarith)
  have hmulF := mul_lt_mul_of_pos_left hf (show 0 < 8 * u by positivity)
  nlinarith

theorem text_4_classical_roundoff :
    ∀ {E : Type uP2a} [AddCommGroup E] [Module ℝ E]
      (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (H : E →ₗ[ℝ] E) (initial : E) (e : ℕ → E),
      (InexactRealizations.Roundoff.prefixPair I H initial e N).1 =
        ((Polynomial.aeval H) (I.residual N)) initial +
          ∑ s : Fin N, ((Polynomial.aeval H) ((InexactRealizations.Classical.history I N).response s)) (e ↑s) :=
  @InexactRealizations.Roundoff.prefixPair_response

end

section
/-! ## Theorem 5.1 (Budgets across calls), p. 11, parts (a)–(b) and Display (25)

The call exponent p is the printed gamma and dualExponent p is its Holder conjugate. The per-call optimum and peak criterion are stated explicitly. Histories in the printed class have terminal I.residual N. r>0 in relative statements is the normalization domain specified in Section2.
-/

theorem theorem_5_1_a_flat :
    ∀ {N : ℕ} (p : ENNReal),
      1 ≤ p →
        ∀ (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) {r t : ℝ},
          0 ≤ r →
            0 ≤ t →
              InexactRealizations.Budgets.additiveRisk p (InexactRealizations.Flat.history I N hN) I r t =
                I.epsilon N * r + t * ↑N ^ (-(1 / p).toReal) * InexactRealizations.Lower.additiveScale I N :=
  @InexactRealizations.Budgets.flat_all_gamma

theorem theorem_5_1_b_peak_criterion :
    ∀ {N : ℕ} (h : InexactRealizations.History N)
      (I : InexactRealizations.Operators.SpectralInterval),
      h.ChebyshevExact I →
        0 < N → ((∀ r t : ℝ, 0 ≤ r → 0 ≤ t → InexactRealizations.Budgets.additiveRisk ⊤ h I r t = I.epsilon N * r + t * InexactRealizations.Lower.additiveScale I N) ↔ ((∀ s : Fin N, Polynomial.eval I.mu (h.response s) < 0) ∧
        ∀ lam ∈ Set.Icc I.mu I.L, ∑ s : Fin N,
          Polynomial.eval lam (h.response s) ^ 2 / |Polynomial.eval I.mu (h.response s)| ≤ InexactRealizations.Lower.additiveScale I N)) :=
  @InexactRealizations.Budgets.PeakCriterion.perCallOptimal_iff_criterion

theorem theorem_5_1_b_peak_sufficient :
    ∀ {N : ℕ} (h : InexactRealizations.History N)
      (I : InexactRealizations.Operators.SpectralInterval),
      h.ChebyshevExact I →
        0 < N → (∀ (s : Fin N) (lam : ℝ), lam ∈ Set.Icc I.mu I.L → |Polynomial.eval lam (h.response s)| ≤ -Polynomial.eval I.mu (h.response s)) → (∀ r t : ℝ, 0 ≤ r → 0 ≤ t → InexactRealizations.Budgets.additiveRisk ⊤ h I r t = I.epsilon N * r + t * InexactRealizations.Lower.additiveScale I N) :=
  @InexactRealizations.Budgets.PeakCriterion.responsePeaks_optimal

theorem theorem_5_1_b_common_peaks :
    ∀ {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
      h.ChebyshevExact I →
        0 < N →
          (∀ (s : Fin N) (lam : ℝ), lam ∈ Set.Icc I.mu I.L → |Polynomial.eval lam (h.response s)| ≤ -Polynomial.eval I.mu (h.response s)) →
            (∀ (s : Fin N) (lam : ℝ), lam ∈ Set.Icc I.mu I.L → |Polynomial.eval lam (h.query s)| ≤ Polynomial.eval I.mu (h.query s)) →
              ∀ (r : ℝ), 0 < r → InexactRealizations.Budgets.localRelativeGain ⊤ h I r = InexactRealizations.Lower.derivativeScale I N :=
  @InexactRealizations.Budgets.PeakCriterion.commonPeaks_relative

theorem theorem_5_1_b_prefix_response_peak {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) :
    ∀ (s : Fin N) (lam : ℝ), lam ∈ Set.Icc I.mu I.L →
      |((InexactRealizations.Comparisons.Competitors.Prefix.history I N).response s).eval lam| ≤ -((InexactRealizations.Comparisons.Competitors.Prefix.history I N).response s).eval I.mu :=
  InexactRealizations.Budgets.PeakExamples.prefix_responsePeaks I (by omega)

theorem theorem_5_1_b_prefix_query_peak {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval) :
    ∀ (s : Fin N) (lam : ℝ), lam ∈ Set.Icc I.mu I.L →
      |((InexactRealizations.Comparisons.Competitors.Prefix.history I N).query s).eval lam| ≤ ((InexactRealizations.Comparisons.Competitors.Prefix.history I N).query s).eval I.mu :=
  InexactRealizations.Budgets.PeakExamples.prefix_queryPeaks I

theorem theorem_5_1_b_sine_response_peak {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) :
    ∀ (s : Fin N) (lam : ℝ), lam ∈ Set.Icc I.mu I.L →
      |((InexactRealizations.Comparisons.Competitors.Sine.history I N).response s).eval lam| ≤ -((InexactRealizations.Comparisons.Competitors.Sine.history I N).response s).eval I.mu :=
  InexactRealizations.Budgets.PeakExamples.Sine.responsePeaks I (by omega)

theorem theorem_5_1_b_sine_query_peak {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) :
    ∀ (s : Fin N) (lam : ℝ), lam ∈ Set.Icc I.mu I.L →
      |((InexactRealizations.Comparisons.Competitors.Sine.history I N).query s).eval lam| ≤ ((InexactRealizations.Comparisons.Competitors.Sine.history I N).query s).eval I.mu :=
  InexactRealizations.Budgets.PeakExamples.Sine.queryPeaks I (by omega)

theorem theorem_5_1_b_balanced_response_peak {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) :
    ∀ (s : Fin N) (lam : ℝ), lam ∈ Set.Icc I.mu I.L →
      |((InexactRealizations.Balanced.history I N hN).response s).eval lam| ≤ -((InexactRealizations.Balanced.history I N hN).response s).eval I.mu :=
  InexactRealizations.Budgets.PeakExamples.balanced_responsePeaks I hN

theorem theorem_5_1_b_balanced_query_peak {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) :
    ∀ (s : Fin N) (lam : ℝ), lam ∈ Set.Icc I.mu I.L →
      |((InexactRealizations.Balanced.history I N hN).query s).eval lam| ≤ ((InexactRealizations.Balanced.history I N hN).query s).eval I.mu :=
  InexactRealizations.Budgets.PeakExamples.balanced_queryPeaks I hN

theorem theorem_5_1_b_flat_response_peak {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) :
    ∀ (s : Fin N) (lam : ℝ), lam ∈ Set.Icc I.mu I.L →
      |((InexactRealizations.Flat.history I N hN).response s).eval lam| ≤ -((InexactRealizations.Flat.history I N hN).response s).eval I.mu :=
  InexactRealizations.Budgets.PeakExamples.flat_responsePeaks I hN

theorem theorem_5_1_b_prefix :
    ∀ {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval),
      2 ≤ N →
        ∀ (r : ℝ),
          0 < r →
            (∀ r t : ℝ, 0 ≤ r → 0 ≤ t → InexactRealizations.Budgets.additiveRisk ⊤ (InexactRealizations.Comparisons.Competitors.Prefix.history I N) I r t = I.epsilon N * r + t * InexactRealizations.Lower.additiveScale I N) ∧
              InexactRealizations.Budgets.localRelativeGain ⊤ (InexactRealizations.Comparisons.Competitors.Prefix.history I N) I r =
                InexactRealizations.Lower.derivativeScale I N :=
  @InexactRealizations.Budgets.PeakExamples.prefix_perCall_optima

theorem theorem_5_1_b_sine :
    ∀ {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval),
      2 ≤ N →
        ∀ (r : ℝ),
          0 < r →
            (∀ r t : ℝ, 0 ≤ r → 0 ≤ t → InexactRealizations.Budgets.additiveRisk ⊤ (InexactRealizations.Comparisons.Competitors.Sine.history I N) I r t = I.epsilon N * r + t * InexactRealizations.Lower.additiveScale I N) ∧
              InexactRealizations.Budgets.localRelativeGain ⊤ (InexactRealizations.Comparisons.Competitors.Sine.history I N) I r =
                InexactRealizations.Lower.derivativeScale I N :=
  @InexactRealizations.Budgets.PeakExamples.sine_perCall_optima

theorem theorem_5_1_b_balanced :
    ∀ {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (r : ℝ),
      0 < r →
        (∀ r t : ℝ, 0 ≤ r → 0 ≤ t → InexactRealizations.Budgets.additiveRisk ⊤ (InexactRealizations.Balanced.history I N hN) I r t = I.epsilon N * r + t * InexactRealizations.Lower.additiveScale I N) ∧
          InexactRealizations.Budgets.localRelativeGain ⊤ (InexactRealizations.Balanced.history I N hN) I r = InexactRealizations.Lower.derivativeScale I N :=
  @InexactRealizations.Budgets.PeakExamples.balanced_perCall_optima

theorem theorem_5_1_b_flat :
    ∀ {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N),
      (∀ r t : ℝ, 0 ≤ r → 0 ≤ t → InexactRealizations.Budgets.additiveRisk ⊤ (InexactRealizations.Flat.history I N hN) I r t = I.epsilon N * r + t * InexactRealizations.Lower.additiveScale I N) :=
  @InexactRealizations.Budgets.PeakExamples.flat_perCall_optimal

end

section
/-! ## Theorem 5.1 (Budgets across calls), p. 11, parts (c)–(e)

All constructed histories are the actual Flat, Balanced and Prefix histories. The infimum ranges the full class of histories realizing the prescribed terminal. No sign, memory or independence restriction is added.
-/

theorem theorem_5_1_c_balanced_even :
    ∀ {N : ℕ} (p : ENNReal),
      1 ≤ p →
        ∀ (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N),
          Even N →
            ∀ (r : ℝ),
              0 < r →
                InexactRealizations.Budgets.localRelativeGain p (InexactRealizations.Balanced.history I N hN) I r =
                  ↑N ^ (-(1 / p).toReal) * InexactRealizations.Lower.derivativeScale I N :=
  @InexactRealizations.Budgets.balanced_even_all_gamma

theorem theorem_5_1_c_strict_prefix_comparison :
    ∀ (p : ENNReal),
      1 ≤ p →
        p ≠ ⊤ →
          ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 4 ≤ N) (r : ℝ),
            0 < r →
              InexactRealizations.Budgets.localRelativeGain p (InexactRealizations.Balanced.history I N (by omega)) I r <
                InexactRealizations.Budgets.localRelativeGain p (InexactRealizations.Comparisons.Competitors.Prefix.history I N) I r :=
  @InexactRealizations.Budgets.PrefixComparison.balanced_lt_prefix_all_finite_gamma

theorem theorem_5_1_d_flat :
    ∀ {N : ℕ} (p : ENNReal),
      1 ≤ p →
        ∀ (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (r : ℝ),
          0 < r →
            InexactRealizations.Budgets.localRelativeGain p (InexactRealizations.Flat.history I N hN) I r =
              InexactRealizations.Lower.additiveScale I N / ↑N *
                InexactRealizations.Budgets.callNorm (InexactRealizations.Budgets.dualExponent p) fun s : Fin N => InexactRealizations.Budgets.FlatQuery.peak I N ↑s :=
  @InexactRealizations.Budgets.flat_all_gamma_relative

theorem theorem_5_1_d_peak_formula (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    InexactRealizations.Budgets.FlatQuery.peak I N s =
      (1 + InexactRealizations.Flat.tau I N s) * ((s : ℝ) + 1) / InexactRealizations.Flat.u I s +
        InexactRealizations.Flat.tau I N s * (s : ℝ) / InexactRealizations.Flat.u I (s - 1) := rfl

theorem theorem_5_1_d_zero_call :
    ∀ {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval),
      2 ≤ N → InexactRealizations.Budgets.FlatQuery.peak I N 0 = 1 :=
  @InexactRealizations.Budgets.FlatQuery.peak_zero

theorem theorem_5_1_d_query_peak :
    ∀ {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (s : Fin N),
      |Polynomial.eval I.L ((InexactRealizations.Flat.history I N hN).query s)| = InexactRealizations.Budgets.FlatQuery.peak I N ↑s :=
  @InexactRealizations.Budgets.FlatQuery.query_at_L

theorem theorem_5_1_e_odd_gap :
    ∀ {N : ℕ} (p : ENNReal),
      1 ≤ p →
        p ≠ ⊤ →
          ∀ (I : InexactRealizations.Operators.SpectralInterval),
            2 ≤ N →
              Odd N →
                ∀ (r : ℝ),
                  0 < r →
                    ↑N ^ (-(1 / p).toReal) * InexactRealizations.Lower.derivativeScale I N <
                      sInf ({v : ℝ | ∃ h : InexactRealizations.History N, h.ChebyshevExact I ∧ v = InexactRealizations.Budgets.localRelativeGain p h I r}) :=
  @InexactRealizations.Budgets.OddGap.odd_infimum_gap

end

section
/-! ## Proposition 5.2 (Centered relative errors) and Display (26), p. 11

rawRisk is the supremum of the actual centered relative-noise MSE under the printed adapted conditional law. Its raw second-moment law derives square integrability. responsePeak is the maximum modulus of the actual response polynomial. centeredCoefficient is the maximum of the displayed sum, with both an upper property and an actual attaining spectral point stated below.
-/

theorem proposition_5_2_maximum :
    ∀ {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
      (∀ ν ∈ Set.Icc I.mu I.L,
          ∑ s : Fin N, InexactRealizations.Centered.responsePeak h I s ^ 2 * Polynomial.eval ν (h.query s) ^ 2 ≤
            InexactRealizations.Centered.centeredCoefficient h I) ∧
        ∃ ν ∈ Set.Icc I.mu I.L,
          InexactRealizations.Centered.centeredCoefficient h I =
            ∑ s : Fin N, InexactRealizations.Centered.responsePeak h I s ^ 2 * Polynomial.eval ν (h.query s) ^ 2 :=
  @InexactRealizations.Centered.coefficient_maximum

theorem proposition_5_2_limsup_and_lower :
    ∀ {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
      h.ChebyshevExact I →
        2 ≤ N →
          ∀ (r : ℝ),
            0 < r →
              Filter.limsup (fun t => InexactRealizations.Centered.rawRisk h I r t / (t ^ 2 * r ^ 2)) (nhdsWithin 0 (Set.Ioi 0)) =
                  InexactRealizations.Centered.centeredCoefficient h I ∧
                h.spectralGain I ^ 2 ≤ InexactRealizations.Centered.centeredCoefficient h I ∧
                  InexactRealizations.Lower.linearGain I N ^ 2 ≤ h.spectralGain I ^ 2 :=
  @InexactRealizations.Centered.journal_centered

theorem proposition_5_2_balanced_equality :
    ∀ {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval) (hN : 2 ≤ N) (r : ℝ),
      0 < r →
        Filter.limsup (fun t => InexactRealizations.Centered.rawRisk (InexactRealizations.Balanced.history I N hN) I r t / (t ^ 2 * r ^ 2))
              (nhdsWithin 0 (Set.Ioi 0)) =
            InexactRealizations.Lower.linearGain I N ^ 2 ∧
          InexactRealizations.Centered.centeredCoefficient (InexactRealizations.Balanced.history I N hN) I = InexactRealizations.Lower.linearGain I N ^ 2 ∧
            (InexactRealizations.Balanced.history I N hN).spectralGain I ^ 2 = InexactRealizations.Lower.linearGain I N ^ 2 :=
  @InexactRealizations.Centered.journal_centered_balanced

end

section
/-! ## Section 5.1, p. 12, text before Table 1 (Flat relative growth)

The computed entries of Table1 are excluded. The analytic Flat lower bound, exact printed ratio, and exponential penalty are proved for the actual histories and every call budget.
-/

theorem text_5_flat_corner_lower :
    ∀ (p : ENNReal),
      1 ≤ p →
        ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) (r : ℝ),
          0 < r → InexactRealizations.Lower.additiveScale I N / ↑N ≤ InexactRealizations.Budgets.localRelativeGain p (InexactRealizations.Flat.history I N hN) I r :=
  @InexactRealizations.Prose.flat_relative_corner_lower

theorem text_5_flat_corner_ratio :
    ∀ (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ),
      0 < N →
        InexactRealizations.Lower.additiveScale I N / (↑N * InexactRealizations.Lower.derivativeScale I N) = (I.den N - 1) / (↑N ^ 3 * (I.eta - 1)) :=
  @InexactRealizations.Prose.flat_corner_scale_ratio

theorem text_5_flat_exponential :
    ∀ (I : InexactRealizations.Operators.SpectralInterval),
      ∃ b,
        1 < b ∧
          ∀ᶠ (N : ℕ) in Filter.atTop,
            ∀ (hN : 2 ≤ N) (p : ENNReal),
              1 ≤ p →
                ∀ (r : ℝ),
                  0 < r →
                    b ^ N * InexactRealizations.Budgets.localRelativeGain p (InexactRealizations.Balanced.history I N hN) I r ≤
                      InexactRealizations.Budgets.localRelativeGain p (InexactRealizations.Flat.history I N hN) I r :=
  @InexactRealizations.Prose.flat_exponential_vs_balanced

end

section
/-! ## Section 5.2, p. 12, spectral-average definitions and isotropic MSE

A spectral law is any probability measure supported on the full spectral interval, including measures with singular moment matrices. The empirical law is constructed from the actual self-adjoint Hessian. Isotropy is the printed conditional covariance with trace sigma squared, expressed by its quadratic forms.
-/

theorem text_5_isotropic_mse :
    ∀ {N : ℕ} {E : Type uP2a} {Ω : Type uP2b} [NormedAddCommGroup E]
      [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
      [mΩ : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ] (h : InexactRealizations.History N)
      (I : InexactRealizations.Operators.SpectralInterval) (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (initial : E)
      (𝓕 : MeasureTheory.Filtration ℕ mΩ) (w : ℕ → Ω → E) (σ : ℝ),
      InexactRealizations.Prose.RawAdditiveLaw N 𝓕 w μ σ →
        (∀ s < N,
            ∀ (v : E), μ[fun ω => inner ℝ v (w s ω) ^ 2 | 𝓕 s] =ᵐ[μ] fun _ => σ ^ 2 / ↑(Module.finrank ℝ E) * ‖v‖ ^ 2) →
          ∫ (ω : Ω), ‖h.stochasticOutput H initial w ω‖ ^ 2 ∂μ =
            ‖((Polynomial.aeval H) h.terminal) initial‖ ^ 2 + σ ^ 2 * (InexactRealizations.Prose.eigenLaw I H hH).variance h :=
  @InexactRealizations.Prose.isotropic_mse_average

def cornerLaw2 (I : InexactRealizations.Operators.SpectralInterval) : InexactRealizations.Averages.SpectralLaw I where
  measure := Measure.dirac I.mu
  probability := inferInstance
  spectral := by
    rw [ae_dirac_iff]
    · exact ⟨le_rfl, I.mu_lt_L.le⟩
    · exact measurableSet_Icc

theorem text_5_corner_spectral_variance {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval)
    (h : InexactRealizations.History N) :
    (cornerLaw2 I).variance h = ∑ s : Fin N, (h.response s).eval I.mu ^ 2 := by
  simp [InexactRealizations.Averages.SpectralLaw.variance, InexactRealizations.Averages.SpectralLaw.energy, cornerLaw2]

theorem text_5_corner_christoffel (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) :
    (cornerLaw2 I).christoffel k = 1 := by
  have he (p : ℝ[X]) : (cornerLaw2 I).energy p = p.eval I.mu ^ 2 := by
    simp [InexactRealizations.Averages.SpectralLaw.energy, cornerLaw2]
  have hs : (cornerLaw2 I).christoffelValues k = {1} := by
    ext v
    constructor
    · rintro ⟨p, _, hp, rfl⟩
      simp only [he, hp, one_pow, Set.mem_singleton_iff]
    · intro hv
      have hv' : v = 1 := Set.mem_singleton_iff.mp hv
      subst v
      exact ⟨1, by simp, by simp, by simp [he]⟩
  rw [InexactRealizations.Averages.SpectralLaw.christoffel, hs, csInf_singleton]

theorem text_5_uniform_law_definition (I : InexactRealizations.Operators.SpectralInterval) :
    (InexactRealizations.Averages.uniform I).measure =
      Measure.map (fun u : ℝ ↦ I.mu + I.delta * u) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := rfl

theorem text_5_arcsine_law_definition (I : InexactRealizations.Operators.SpectralInterval) :
    (InexactRealizations.Averages.arcsine I).measure =
      Measure.map (fun z : ℝ ↦ (I.L + I.mu - I.delta * z) / 2)
        (ENNReal.ofReal Real.pi⁻¹ • Polynomial.Chebyshev.measureT) := rfl

theorem text_5_uniform_measure :
    ∀ (I : InexactRealizations.Operators.SpectralInterval) {f : ℝ → ℝ},
      Continuous f → ∫ (x : ℝ), f x ∂(InexactRealizations.Averages.uniform I).measure = ∫ (u : ℝ) in 0..1, f (I.mu + I.delta * u) :=
  @InexactRealizations.Averages.integral_uniform

theorem text_5_arcsine_measure :
    ∀ (I : InexactRealizations.Operators.SpectralInterval) {f : ℝ → ℝ},
      Continuous f →
        ∫ (x : ℝ), f x ∂(InexactRealizations.Averages.arcsine I).measure =
          Real.pi⁻¹ * ∫ (z : ℝ), f ((I.L + I.mu - I.delta * z) / 2) ∂Polynomial.Chebyshev.measureT :=
  @InexactRealizations.Averages.integral_arcsine

end

section
/-! ## Theorem 5.3 (Spectral averages), p. 12, part (a)

The moment and variance symbols denote their literal integrals. Uniform and arcsine are the named measures just defined; no density or quadrature certificate is supplied as a hypothesis.
-/

theorem text_5_spectral_variance {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval)
    (rho : InexactRealizations.Averages.SpectralLaw I) (h : InexactRealizations.History N) :
    rho.variance h = ∑ s : Fin N, ∫ x, (h.response s).eval x ^ 2 ∂rho.measure := rfl

theorem text_5_moment (I : InexactRealizations.Operators.SpectralInterval)
    (rho : InexactRealizations.Averages.SpectralLaw I) (k : ℕ) :
    InexactRealizations.Averages.moment rho k =
      ∫ x, (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (I.z x) ^ 2 ∂rho.measure := rfl

theorem text_5_odd_harmonic (k : ℕ) : InexactRealizations.Averages.oddHarmonic k =
    ∑ j ∈ Finset.range k, (2 * (j : ℝ) + 1)⁻¹ := rfl

theorem theorem_5_3_a_prefix :
    ∀ {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval) (ρ : InexactRealizations.Averages.SpectralLaw I),
      2 ≤ N →
        ρ.variance (InexactRealizations.Classical.history I N) =
          16 * I.epsilon N ^ 2 / I.delta ^ 2 *
            (InexactRealizations.Averages.moment ρ N / 4 + ∑ k ∈ Finset.Ico 1 N, I.den (N - k) ^ 2 * InexactRealizations.Averages.moment ρ k) :=
  @InexactRealizations.Averages.journal_prefix

theorem theorem_5_3_a_moments_and_constants :
    ∀ (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ),
      InexactRealizations.Averages.moment (InexactRealizations.Averages.arcsine I) k = ↑k ∧
        InexactRealizations.Averages.moment (InexactRealizations.Averages.uniform I) k = InexactRealizations.Averages.oddHarmonic k ∧
          (InexactRealizations.Averages.uniform I).christoffel k = (((k + 1 : ℕ) : ℝ) ^ 2)⁻¹ ∧
            (InexactRealizations.Averages.arcsine I).christoffel k = (2 * (k : ℝ) + 1)⁻¹ :=
  @InexactRealizations.Averages.journal_named_measures

theorem theorem_5_3_a_arcsine_limit :
    ∀ (I : InexactRealizations.Operators.SpectralInterval),
      Filter.Tendsto (fun N => (InexactRealizations.Averages.arcsine I).variance (InexactRealizations.Classical.history I N)) Filter.atTop
        (nhds (I.kappa / I.L ^ 2)) :=
  @InexactRealizations.Averages.journal_arcsine_limit

theorem theorem_5_3_a_uniform_limit :
    ∀ (I : InexactRealizations.Operators.SpectralInterval),
      Filter.Tendsto (fun N => (InexactRealizations.Averages.uniform I).variance (InexactRealizations.Classical.history I N)) Filter.atTop
        (nhds (√I.kappa * Real.log I.kappa / ((1 - I.kappa⁻¹) * I.L ^ 2))) :=
  @InexactRealizations.Averages.journal_uniform_limit

end

section
/-! ## Theorem 5.3 (Spectral averages), p. 12, parts (b)–(c)

The additive-optimum premise is the printed disjunction of positive-noise deterministic or stochastic attained optima. The joint range and pi/sqrt6 threshold are exactly the printed ones. The lower Christoffel bound holds for every history, a stronger domain than the prescribed-terminal class.
-/

def christoffelPolynomial2 (I : InexactRealizations.Operators.SpectralInterval)
    (rho : InexactRealizations.Averages.SpectralLaw I) (k : ℕ) : ℝ[X] :=
  Classical.choose (rho.exists_christoffel_minimizer k)

theorem text_5_christoffel_minimizer (I : InexactRealizations.Operators.SpectralInterval)
    (rho : InexactRealizations.Averages.SpectralLaw I) (k : ℕ) :
    (christoffelPolynomial2 I rho k).natDegree ≤ k ∧
      (christoffelPolynomial2 I rho k).eval I.mu = 1 ∧
      (∫ x, (christoffelPolynomial2 I rho k).eval x ^ 2 ∂rho.measure) = rho.christoffel k :=
  Classical.choose_spec (rho.exists_christoffel_minimizer k)

theorem text_5_christoffel_minimum (I : InexactRealizations.Operators.SpectralInterval)
    (rho : InexactRealizations.Averages.SpectralLaw I) (k : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ k) (hvalue : p.eval I.mu = 1) :
    (∫ x, (christoffelPolynomial2 I rho k).eval x ^ 2 ∂rho.measure) ≤
      ∫ x, p.eval x ^ 2 ∂rho.measure := by
  rw [(text_5_christoffel_minimizer I rho k).2.2]
  exact rho.christoffel_le k p hp hvalue

theorem theorem_5_3_b_christoffel_lower :
    ∀ {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval)
      (ρ : InexactRealizations.Averages.SpectralLaw I) (h : InexactRealizations.History N),
      ∑ s : Fin N, ρ.christoffel (N - 1 - ↑s) * Polynomial.eval I.mu (h.response s) ^ 2 ≤ ρ.variance h :=
  @InexactRealizations.Averages.journal_christoffel_lower

theorem theorem_5_3_b_additive_optima :
    ∀ {N : ℕ} (I : InexactRealizations.Operators.SpectralInterval)
      (ρ : InexactRealizations.Averages.SpectralLaw I) (h : InexactRealizations.History N),
      h.ChebyshevExact I →
        2 ≤ N →
          ((∃ r t : ℝ, 0 ≤ r ∧ 0 < t ∧ InexactRealizations.Risk.additiveRisk h I r t =
    I.epsilon N * r + t * InexactRealizations.Lower.additiveScale I N / Real.sqrt N) ∨
  (∃ r sigma : ℝ, 0 ≤ r ∧ 0 < sigma ∧ InexactRealizations.Risk.mseRisk h I r sigma =
    I.epsilon N ^ 2 * r ^ 2 + sigma ^ 2 * InexactRealizations.Lower.additiveScale I N ^ 2 / N)) →
            (InexactRealizations.Lower.additiveScale I N / ↑N) ^ 2 * ∑ k ∈ Finset.range N, ρ.christoffel k ≤ ρ.variance h :=
  @InexactRealizations.Averages.journal_additive_optimal_spectral

theorem theorem_5_3_c_joint_range :
    ∀ (c δ : ℝ),
      0 < c →
        0 < δ →
          δ < Real.pi / √6 →
            ∃ κ0,
              ∀ (I : InexactRealizations.Operators.SpectralInterval),
                κ0 ≤ I.kappa →
                  ∀ (N : ℕ),
                    2 ≤ N →
                      c * √I.kappa ≤ ↑N →
                        ↑N ≤ (Real.pi / √6 - δ) * I.kappa ^ (3 / 4 : ℝ) / √(Real.log I.kappa) →
                          ∀ (h : InexactRealizations.History N),
                            h.ChebyshevExact I →
                              ((∃ r t : ℝ, 0 ≤ r ∧ 0 < t ∧ InexactRealizations.Risk.additiveRisk h I r t =
    I.epsilon N * r + t * InexactRealizations.Lower.additiveScale I N / Real.sqrt N) ∨
  (∃ r sigma : ℝ, 0 ≤ r ∧ 0 < sigma ∧ InexactRealizations.Risk.mseRisk h I r sigma =
    I.epsilon N ^ 2 * r ^ 2 + sigma ^ 2 * InexactRealizations.Lower.additiveScale I N ^ 2 / N)) →
                                (InexactRealizations.Averages.uniform I).variance (InexactRealizations.Classical.history I N) <
                                  (InexactRealizations.Averages.uniform I).variance h :=
  @InexactRealizations.Averages.journal_joint_range

end

section
/-! ## Section 6, p. 13, quantized regression and Display (27)

The direction is the printed constant vector in64 dimensions, the worker count is4, the initial point is0, and the noise-to-lower-eigenvalue ratio is3/10. The exact worker quantizer covariance and Display(27) refer to those constructed objects. The symbolic condition number ranges over kappa>1, a stronger family containing both displayed experiments. Measured comparisons are excluded.
-/

/-- The exact direction, Hessian and noise level of the printed regression. -/
def regressionDirection2 : EuclideanSpace ℝ (Fin 64) := WithLp.toLp 2 (fun _ ↦ (1 / 8 : ℝ))

def regressionHessian2 (kappa : ℝ) : EuclideanSpace ℝ (Fin 64) →L[ℝ] EuclideanSpace ℝ (Fin 64) :=
  InexactRealizations.Models.Ridge.spectralMap regressionDirection2 (1 / kappa) 1

def regressionNoise2 (kappa : ℝ) : ℝ := 3 / (10 * kappa)

theorem text_6_regression_direction (j : Fin 64) : regressionDirection2 j = (1 / 8 : ℝ) := rfl

theorem text_6_regression_direction_norm : ‖regressionDirection2‖ = 1 := by
  have hh : ‖regressionDirection2‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    norm_num [regressionDirection2, Real.norm_eq_abs]
  nlinarith [norm_nonneg regressionDirection2]

theorem text_6_regression_hessian (kappa : ℝ) (x : EuclideanSpace ℝ (Fin 64)) :
    regressionHessian2 kappa x = (1 / kappa) • x +
      ((1 - 1 / kappa) * inner ℝ regressionDirection2 x) • regressionDirection2 :=
  InexactRealizations.Models.Ridge.spectralMap_apply _ _ _ _

theorem text_6_regression_quantizer_step (kappa : ℝ) :
    InexactRealizations.Probability.Dither.workerStep (J := Fin 64) 4 (regressionNoise2 kappa) =
      (Real.sqrt 3 / 2) * regressionNoise2 kappa := by
  unfold InexactRealizations.Probability.Dither.workerStep
  norm_num [Real.sqrt_div]
  ring

theorem text_6_regression_covariance {N : ℕ} (R : InexactRealizations.History N)
    (kappa : ℝ) (hkappa : 1 < kappa) (c : Fin 4 → EuclideanSpace ℝ (Fin 64)) (s : Fin N) :
    InexactRealizations.Probability.covarianceMatrix
      (InexactRealizations.Probability.Dither.quantizedStream R (regressionHessian2 kappa).toLinearMap c
        ((Real.sqrt 3 / 2) * regressionNoise2 kappa) 0 s.val)
      (InexactRealizations.Probability.Dither.Temporal.law N 4) =
      ((regressionNoise2 kappa) ^ 2 / 64) • (1 : Matrix (Fin 64) (Fin 64) ℝ) := by
  have hk : 0 < kappa := by linarith
  have hsigma : regressionNoise2 kappa ≠ 0 := by unfold regressionNoise2; positivity
  have hstep := InexactRealizations.Probability.Dither.workerStep_ne_zero (J := Fin 64) 4
    (by norm_num) (by norm_num) (regressionNoise2 kappa) hsigma
  have hh := InexactRealizations.Probability.Dither.quantizedStream_covariance R (by norm_num : 0 < 4)
    (regressionHessian2 kappa).toLinearMap c
    (InexactRealizations.Probability.Dither.workerStep (J := Fin 64) 4 (regressionNoise2 kappa)) hstep 0 s
  have hv := InexactRealizations.Probability.Dither.workerStep_variance (J := Fin 64) 4 (by norm_num)
    (regressionNoise2 kappa)
  rw [hv] at hh
  rw [text_6_regression_quantizer_step] at hh
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using hh

theorem display_27_regression_mse {N : ℕ} (R : InexactRealizations.History N)
    (kappa : ℝ) (hkappa : 1 < kappa) (c : Fin 4 → EuclideanSpace ℝ (Fin 64))
    (xstar : EuclideanSpace ℝ (Fin 64)) (hnorm : ‖xstar‖ ^ 2 = 1)
    (henergy : inner ℝ regressionDirection2 xstar ^ 2 = 1 / 10)
    (hmean : (4 : ℝ)⁻¹ • (∑ i : Fin 4, c i) = regressionHessian2 kappa xstar) :
    (∫ omega, ‖InexactRealizations.Probability.Dither.quantizedOutput R (regressionHessian2 kappa).toLinearMap c
        ((Real.sqrt 3 / 2) * regressionNoise2 kappa) 0 omega - xstar‖ ^ 2
      ∂InexactRealizations.Probability.Dither.Temporal.law N 4) =
      (9 / 10 : ℝ) * R.terminal.eval (1 / kappa) ^ 2 + (1 / 10 : ℝ) * R.terminal.eval 1 ^ 2 +
      regressionNoise2 kappa ^ 2 / 64 *
        (63 * (∑ s : Fin N, (R.response s).eval (1 / kappa) ^ 2) +
          ∑ s : Fin N, (R.response s).eval 1 ^ 2) := by
  have hk : 0 < kappa := by linarith
  have hsigma : regressionNoise2 kappa ≠ 0 := by unfold regressionNoise2; positivity
  have hh := InexactRealizations.Probability.Dither.integral_quantizedOutput_rankOne (J := Fin 64) R
    (by norm_num : 0 < 4) (by norm_num) regressionDirection2 text_6_regression_direction_norm
    (1 / kappa) 1 (regressionNoise2 kappa) hsigma c 0 xstar hmean
  rw [text_6_regression_quantizer_step] at hh
  simp only [zero_sub, norm_neg, inner_neg_right, neg_sq, hnorm, henergy,
    Fintype.card_fin, InexactRealizations.Probability.varianceProfile] at hh
  norm_num at hh ⊢
  simpa only [regressionHessian2, one_div] using hh

end

section
/-! ## Section 6, p. 14, Displays (28)–(29) (coupled cyclic network)

The actual projector and two-block Hessian preserve the antisymmetric subspace. The cycle has a constructed real orthonormal eigenbasis. Experimental parameter choices and measurements in Figures2–3 are excluded; the general physical model and sharp prediction are stated.
-/

theorem text_6_projector :
    ∀ {E : Type uP2a} [AddCommGroup E] [Module ℝ E] (z : E),
      InexactRealizations.Models.Network.projector (InexactRealizations.Models.Network.antisymmetric z) = InexactRealizations.Models.Network.antisymmetric z :=
  @InexactRealizations.Models.Network.projector_antisymmetric

theorem text_6_projector_idempotent :
    ∀ {E : Type uP2a} [AddCommGroup E] [Module ℝ E]
      (x : E × E), InexactRealizations.Models.Network.projector (InexactRealizations.Models.Network.projector x) = InexactRealizations.Models.Network.projector x :=
  @InexactRealizations.Models.Network.projector_idempotent

theorem text_6_active_endpoints :
    ∀ (κ : ℝ),
      1 < κ →
        (0 + 2 * (2 / (κ - 1))) / (4 + 2 * (2 / (κ - 1))) = 1 / κ ∧ (4 + 2 * (2 / (κ - 1))) / (4 + 2 * (2 / (κ - 1))) = 1 :=
  @InexactRealizations.Models.Network.active_endpoints

theorem text_6_real_cycle_spectrum :
    ∀ (m : ℕ) [NeZero m] (u : EuclideanSpace ℝ (ZMod m))
      (j : Fin m),
      ((InexactRealizations.Models.Network.realEigenbasis m).repr ((InexactRealizations.Models.Network.cycleOperator m) u)).ofLp j =
        InexactRealizations.Models.Network.realEigenvalue m j * ((InexactRealizations.Models.Network.realEigenbasis m).repr u).ofLp j :=
  @InexactRealizations.Models.Network.realEigenbasis_diagonalization

theorem text_6_network_derivative :
    ∀ (m : ℕ) [NeZero m] {N : ℕ} (h : InexactRealizations.History N) (κ : ℝ)
      (initial : EuclideanSpace ℝ (Fin m)) (e : EuclideanSpace ℝ (Fin N)),
      HasDerivAt
        (fun t =>
          h.oracleOutput
            (InexactRealizations.Models.Network.activeEmbedding ((InexactRealizations.Models.Network.realEigenbasis m).repr.symm initial))
            (InexactRealizations.Models.Network.ambientOracle (InexactRealizations.Models.Network.cycleLaplacian m) (2 / (κ - 1)) t fun s =>
              e.ofLp s))
        (InexactRealizations.Models.Network.activeEmbedding
          ((InexactRealizations.Models.Network.realEigenbasis m).repr.symm
            ((InexactRealizations.Channel.signalOperator h (InexactRealizations.Models.Network.activeSpectralValue m κ) initial.ofLp) e)))
        0 :=
  @InexactRealizations.Models.Network.cycle_network_hasDerivAt

/-- The literal cycle Hessian and the fixed active-space realization of the channel. -/
def networkBlockHessian2 (kappa : ℝ) :
    ((ZMod 16 → ℝ) × (ZMod 16 → ℝ)) → ((ZMod 16 → ℝ) × (ZMod 16 → ℝ)) :=
  InexactRealizations.Models.Network.hessian (InexactRealizations.Models.Network.cycleLaplacian 16) (2 / (kappa - 1))

def networkSpectralHessian2 (kappa : ℝ) :
    EuclideanSpace ℝ (Fin 16) →ₗ[ℝ] EuclideanSpace ℝ (Fin 16) :=
  InexactRealizations.History.matrixEnd (Matrix.diagonal (InexactRealizations.Models.Network.activeSpectralValue 16 kappa))

def networkEmbedding2 : EuclideanSpace ℝ (Fin 16) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2 × ZMod 16) :=
  InexactRealizations.Models.Network.activeEmbedding.comp
    (InexactRealizations.Models.Network.realEigenbasis 16).repr.symm.toLinearIsometry

def networkSignOutput2 {N : ℕ} (h : InexactRealizations.History N) (kappa : ℝ)
    (initial : EuclideanSpace ℝ (Fin 16)) (delta : ℝ) (omega : Fin N → Bool) :
    EuclideanSpace ℝ (Fin 2 × ZMod 16) :=
  h.oracleOutput (networkEmbedding2 initial)
    (InexactRealizations.Models.Network.ambientOracle (InexactRealizations.Models.Network.cycleLaplacian 16)
      (2 / (kappa - 1)) delta (fun s ↦ InexactRealizations.Probability.Signs.stream N 1 s.val omega))

theorem display_28_actual_hessian (kappa : ℝ) (hkappa : 1 < kappa)
    (x : (ZMod 16 → ℝ) × (ZMod 16 → ℝ)) :
    networkBlockHessian2 kappa x =
      ((4 * kappa)⁻¹ • ((kappa - 1) • InexactRealizations.Models.Network.cycleLaplacian 16 x.1 +
          2 • (x.1 - x.2)),
       (4 * kappa)⁻¹ • ((kappa - 1) • InexactRealizations.Models.Network.cycleLaplacian 16 x.2 +
          2 • (x.2 - x.1))) := by
  have hk : kappa ≠ 0 := by linarith
  have hkm : kappa - 1 ≠ 0 := by linarith
  have hd : 4 + 2 * (2 / (kappa - 1)) = 4 * kappa / (kappa - 1) := by
    field_simp
    ring
  ext j <;> simp only [networkBlockHessian2, InexactRealizations.Models.Network.hessian, hd,
    Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  all_goals field_simp
  all_goals ring

theorem display_29_actual_output {N : ℕ} (h : InexactRealizations.History N) (kappa : ℝ)
    (initial : EuclideanSpace ℝ (Fin 16)) (delta : ℝ) (omega : Fin N → Bool) :
    networkSignOutput2 h kappa initial delta omega = networkEmbedding2
      (InexactRealizations.Channel.finiteSignOutput h (networkSpectralHessian2 kappa)
        (fun _ ↦ LinearMap.id) initial delta omega) := by
  rw [networkSignOutput2, show networkEmbedding2 initial =
    InexactRealizations.Models.Network.activeEmbedding ((InexactRealizations.Models.Network.realEigenbasis 16).repr.symm initial) from rfl,
    InexactRealizations.Models.Network.cycle_network_output_spectral]
  change networkEmbedding2 _ = networkEmbedding2 _
  apply congrArg networkEmbedding2
  unfold InexactRealizations.Channel.finiteSignOutput InexactRealizations.Channel.finiteNoiseOutput
  rw [InexactRealizations.Models.Network.spectralOracle_eq_perturbed]
  congr 1
  funext s v
  simp only [InexactRealizations.History.perturbedOracle, networkSpectralHessian2, LinearMap.smul_apply,
    LinearMap.id_apply, smul_smul]

theorem text_6_actual_eigenvalue_formula (kappa : ℝ) (hkappa : 1 < kappa) (j : Fin 16) :
    InexactRealizations.Models.Network.activeSpectralValue 16 kappa j =
      (4 + (kappa - 1) * InexactRealizations.Models.Network.realEigenvalue 16 j) / (4 * kappa) := by
  have hk : kappa ≠ 0 := by linarith
  have hkm : kappa - 1 ≠ 0 := by linarith
  have hd : 4 + 2 * (2 / (kappa - 1)) = 4 * kappa / (kappa - 1) := by field_simp; ring
  unfold InexactRealizations.Models.Network.activeSpectralValue
  rw [hd]
  field_simp
  ring

theorem text_6_actual_extreme_eigenvalues (kappa : ℝ) (hkappa : 1 < kappa) :
    InexactRealizations.Models.Network.activeSpectralValue 16 kappa (InexactRealizations.Models.Network.lowerMode 16) = 1 / kappa ∧
    InexactRealizations.Models.Network.activeSpectralValue 16 kappa (InexactRealizations.Models.Network.upperMode 16) = 1 ∧
    ∀ j : Fin 16, InexactRealizations.Models.Network.activeSpectralValue 16 kappa j ∈ Set.Icc (1 / kappa) 1 := by
  have hk : 0 < kappa := by linarith
  have hden : 0 < 4 * kappa := by positivity
  refine ⟨?_, ?_, ?_⟩
  · unfold InexactRealizations.Models.Network.activeSpectralValue
    rw [InexactRealizations.Models.Network.lowerMode_value]
    exact (InexactRealizations.Models.Network.active_endpoints kappa hkappa).1
  · unfold InexactRealizations.Models.Network.activeSpectralValue
    rw [InexactRealizations.Models.Network.upperMode_value 16 (by decide)]
    exact (InexactRealizations.Models.Network.active_endpoints kappa hkappa).2
  · intro j
    obtain ⟨z, hz⟩ := InexactRealizations.Models.Network.realEigenvalue_cosine 16 j
    have hb := InexactRealizations.Models.Network.cycleEigenvalue_mem 16 z
    rw [← hz] at hb
    rw [text_6_actual_eigenvalue_formula kappa hkappa j]
    constructor
    · apply (le_div_iff₀ hden).mpr
      have he : (1 / kappa) * (4 * kappa) = 4 := by field_simp
      rw [he]
      nlinarith [mul_nonneg (show 0 ≤ kappa - 1 by linarith) hb.1]
    · apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg (show 0 ≤ kappa - 1 by linarith) (sub_nonneg.mpr hb.2)]

theorem text_6_actual_fourier_frequencies (kappa : ℝ) (hkappa : 1 < kappa) (z : ZMod 16) :
    ∃ j : Fin 16, InexactRealizations.Models.Network.activeSpectralValue 16 kappa j =
      (4 + (kappa - 1) * InexactRealizations.Models.Network.cycleEigenvalue 16 z) / (4 * kappa) := by
  obtain ⟨j, hj⟩ := InexactRealizations.Models.Network.realEigenvalue_exists 16 z
  exact ⟨j, (text_6_actual_eigenvalue_formula kappa hkappa j).trans (by rw [hj])⟩

def physicalNetworkHessian2 (kappa : ℝ)
    (x : EuclideanSpace ℝ (Fin 2 × ZMod 16)) : EuclideanSpace ℝ (Fin 2 × ZMod 16) :=
  InexactRealizations.Models.Network.ambientOracle (N := 1) (InexactRealizations.Models.Network.cycleLaplacian 16)
    (2 / (kappa - 1)) 0 (fun _ ↦ 0) 0 x

theorem text_6_actual_antisymmetric_space (x : EuclideanSpace ℝ (Fin 2 × ZMod 16)) :
    (∃ z : EuclideanSpace ℝ (Fin 16), networkEmbedding2 z = x) ↔
      ∀ j : ZMod 16, x (1, j) = -x (0, j) := by
  constructor
  · rintro ⟨z, rfl⟩ j
    change -(Real.sqrt 2)⁻¹ * ((InexactRealizations.Models.Network.realEigenbasis 16).repr.symm z) j =
      -((Real.sqrt 2)⁻¹ * ((InexactRealizations.Models.Network.realEigenbasis 16).repr.symm z) j)
    ring
  · intro hx
    let y : EuclideanSpace ℝ (ZMod 16) :=
      Real.sqrt 2 • WithLp.toLp 2 (fun j ↦ x (0, j))
    let z := (InexactRealizations.Models.Network.realEigenbasis 16).repr y
    refine ⟨z, ?_⟩
    have hz : networkEmbedding2 z = InexactRealizations.Models.Network.activeEmbedding y := by
      change InexactRealizations.Models.Network.activeEmbedding
        ((InexactRealizations.Models.Network.realEigenbasis 16).repr.symm
          ((InexactRealizations.Models.Network.realEigenbasis 16).repr y)) = _
      rw [LinearIsometryEquiv.symm_apply_apply]
    rw [hz]
    have hs : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    ext ij
    rcases ij with ⟨i, j⟩
    fin_cases i
    · change (Real.sqrt 2)⁻¹ * (Real.sqrt 2 * x (0, j)) = x (0, j)
      field_simp
    · change -(Real.sqrt 2)⁻¹ * (Real.sqrt 2 * x (0, j)) = x (1, j)
      rw [hx j]
      field_simp

theorem text_6_physical_hessian_coordinates (kappa : ℝ) (z : EuclideanSpace ℝ (Fin 16)) :
    physicalNetworkHessian2 kappa (networkEmbedding2 z) =
      networkEmbedding2 (networkSpectralHessian2 kappa z) := by
  change InexactRealizations.Models.Network.ambientOracle _ _ 0 (fun _ : Fin 1 ↦ 0) 0
      (InexactRealizations.Models.Network.activeEmbedding ((InexactRealizations.Models.Network.realEigenbasis 16).repr.symm z)) =
    InexactRealizations.Models.Network.activeEmbedding ((InexactRealizations.Models.Network.realEigenbasis 16).repr.symm _)
  rw [InexactRealizations.Models.Network.ambientOracle_embedding]
  apply congrArg InexactRealizations.Models.Network.activeEmbedding
  apply (InexactRealizations.Models.Network.realEigenbasis 16).repr.injective
  rw [InexactRealizations.Models.Network.cycleOracle_spectral, LinearIsometryEquiv.apply_symm_apply,
    InexactRealizations.Models.Network.spectralOracle_eq_perturbed]
  simp only [InexactRealizations.History.perturbedOracle, zero_smul, add_zero, networkSpectralHessian2]

private theorem aux2_spectral_hessian_coordinate (kappa : ℝ)
    (z : EuclideanSpace ℝ (Fin 16)) (j : Fin 16) :
    networkSpectralHessian2 kappa z j = InexactRealizations.Models.Network.activeSpectralValue 16 kappa j * z j := by
  change (Matrix.diagonal (InexactRealizations.Models.Network.activeSpectralValue 16 kappa)).mulVec z.ofLp j = _
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal]

private theorem aux2_spectral_quadratic_lower (kappa : ℝ) (hkappa : 1 < kappa)
    (z : EuclideanSpace ℝ (Fin 16)) :
    (1 / kappa) * ‖z‖ ^ 2 ≤ inner ℝ z (networkSpectralHessian2 kappa z) := by
  have he : inner ℝ z (networkSpectralHessian2 kappa z) =
      ∑ j : Fin 16, InexactRealizations.Models.Network.activeSpectralValue 16 kappa j * (z j) ^ 2 := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
    apply Finset.sum_congr rfl
    intro j _
    rw [aux2_spectral_hessian_coordinate]
    ring
  rw [he, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  simp only [Real.norm_eq_abs, sq_abs]
  exact Finset.sum_le_sum fun j _ ↦
    mul_le_mul_of_nonneg_right ((text_6_actual_extreme_eigenvalues kappa hkappa).2.2 j).1 (sq_nonneg _)

private theorem aux2_actual_network_energy_minimum (kappa : ℝ) (hkappa : 1 < kappa)
    (x : EuclideanSpace ℝ (Fin 2 × ZMod 16))
    (hx : ∀ j : ZMod 16, x (1, j) = -x (0, j)) :
    0 ≤ inner ℝ x (physicalNetworkHessian2 kappa x) ∧
      (inner ℝ x (physicalNetworkHessian2 kappa x) = 0 ↔ x = 0) := by
  obtain ⟨z, rfl⟩ := (text_6_actual_antisymmetric_space x).mpr hx
  have hk : 0 < kappa := by linarith
  have hq := aux2_spectral_quadratic_lower kappa hkappa z
  rw [text_6_physical_hessian_coordinates, networkEmbedding2.inner_map_map]
  refine ⟨(mul_nonneg (one_div_pos.mpr hk).le (sq_nonneg ‖z‖)).trans hq, ?_⟩
  constructor
  · intro hz
    have hn : ‖z‖ = 0 := by
      by_contra hn
      have hpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hn)
      have hp := mul_pos (one_div_pos.mpr hk) (sq_pos_of_pos hpos)
      linarith
    rw [norm_eq_zero.mp hn, map_zero]
  · intro hz
    have he : z = 0 := networkEmbedding2.injective (by simpa only [map_zero] using hz)
    rw [he, inner_zero_left]

theorem text_6_actual_network_unique_minimum (kappa : ℝ) (hkappa : 1 < kappa)
    (x : EuclideanSpace ℝ (Fin 2 × ZMod 16))
    (hx : ∀ j : ZMod 16, x (1, j) = -x (0, j)) :
    0 ≤ inner ℝ x (physicalNetworkHessian2 kappa x) / 2 ∧
      (inner ℝ x (physicalNetworkHessian2 kappa x) / 2 = 0 ↔ x = 0) := by
  have hh := aux2_actual_network_energy_minimum kappa hkappa x hx
  refine ⟨div_nonneg hh.1 (by norm_num), ?_⟩
  simpa only [div_eq_zero_iff, show (2 : ℝ) ≠ 0 by norm_num, or_false] using hh.2

theorem text_6_actual_cycle_signal {N : ℕ} (h : InexactRealizations.History N) (kappa : ℝ)
    (initial : EuclideanSpace ℝ (Fin 16)) (j : Fin 16) (s : Fin N) :
    InexactRealizations.Channel.signalMatrix h (InexactRealizations.Models.Network.activeSpectralValue 16 kappa) initial.ofLp j s =
      initial j * (h.response s).eval (InexactRealizations.Models.Network.activeSpectralValue 16 kappa j) *
        (h.query s).eval (InexactRealizations.Models.Network.activeSpectralValue 16 kappa j) := by
  unfold InexactRealizations.Channel.signalMatrix InexactRealizations.Lower.physicalKernel
  ring

theorem text_6_actual_cycle_sharp_gain {N : ℕ} (h : InexactRealizations.History N) (hN : 0 < N)
    (kappa : ℝ) (initial : EuclideanSpace ℝ (Fin 16)) :
    (∀ e : EuclideanSpace ℝ (Fin N), ‖e‖ ≤ 1 →
      ‖InexactRealizations.Channel.signalOperator h (InexactRealizations.Models.Network.activeSpectralValue 16 kappa) initial.ofLp e‖ ≤
        ‖InexactRealizations.Channel.signalOperator h (InexactRealizations.Models.Network.activeSpectralValue 16 kappa) initial.ofLp‖) ∧
    ∃ e : EuclideanSpace ℝ (Fin N), ‖e‖ = 1 ∧
      ‖InexactRealizations.Channel.signalOperator h (InexactRealizations.Models.Network.activeSpectralValue 16 kappa) initial.ofLp e‖ =
        ‖InexactRealizations.Channel.signalOperator h (InexactRealizations.Models.Network.activeSpectralValue 16 kappa) initial.ofLp‖ :=
  InexactRealizations.Channel.signalOperator_sharp h hN _ _

theorem text_6_actual_cycle_mean {N : ℕ} (h : InexactRealizations.History N) (kappa : ℝ)
    (initial : EuclideanSpace ℝ (Fin 16)) (delta : ℝ) :
    (∫ omega, networkSignOutput2 h kappa initial delta omega ∂InexactRealizations.Probability.Signs.law N) =
      networkEmbedding2 ((Polynomial.aeval (networkSpectralHessian2 kappa) h.terminal) initial) := by
  simp_rw [display_29_actual_output]
  rw [networkEmbedding2.integral_comp_comm, InexactRealizations.Channel.finiteSignOutput_mean]

theorem text_6_actual_cycle_variance {N : ℕ} (h : InexactRealizations.History N) (kappa : ℝ)
    (initial : EuclideanSpace ℝ (Fin 16)) (delta : ℝ) :
    (∫ omega, ‖networkSignOutput2 h kappa initial delta omega -
        networkEmbedding2 ((Polynomial.aeval (networkSpectralHessian2 kappa) h.terminal) initial)‖ ^ 2
        ∂InexactRealizations.Probability.Signs.law N) =
      delta ^ 2 * (∑ j : Fin 16, ∑ s : Fin N,
        (InexactRealizations.Channel.signalMatrix h (InexactRealizations.Models.Network.activeSpectralValue 16 kappa) initial.ofLp j s) ^ 2) +
      InexactRealizations.Channel.finiteNoiseRemainder h (networkSpectralHessian2 kappa)
        (fun _ ↦ LinearMap.id) initial delta := by
  simp_rw [display_29_actual_output, ← networkEmbedding2.map_sub, networkEmbedding2.norm_map]
  exact InexactRealizations.Channel.finiteSignOutput_signal_variance h _ initial delta

theorem text_6_actual_cycle_remainder {N : ℕ} (h : InexactRealizations.History N) (kappa : ℝ)
    (initial : EuclideanSpace ℝ (Fin 16)) :
    (∀ delta : ℝ, 0 ≤ InexactRealizations.Channel.finiteNoiseRemainder h (networkSpectralHessian2 kappa)
      (fun _ ↦ LinearMap.id) initial delta) ∧
    Asymptotics.IsBigOWith
      (InexactRealizations.Channel.finiteNoiseRemainderConstant h (networkSpectralHessian2 kappa) (fun _ ↦ LinearMap.id) initial)
      (nhds (0 : ℝ))
      (InexactRealizations.Channel.finiteNoiseRemainder h (networkSpectralHessian2 kappa) (fun _ ↦ LinearMap.id) initial)
      (fun delta : ℝ ↦ delta ^ 4) :=
  ⟨fun _ ↦ InexactRealizations.Channel.finiteNoiseRemainder_nonneg _ _ _ _ _,
    InexactRealizations.Channel.finiteNoiseRemainder_isBigO _ _ _ _⟩

end

section
/-! ## Appendix A, p. 16, spectral-measure norm identity

The finitely supported probability measure is an actual measure. The spectral law of a vector is constructed from the actual self-adjoint Hessian; the printed norm identity is stated for that constructed finite spectrum.
-/

theorem text_A_vector_spectral_norm :
    ∀ {I : InexactRealizations.Operators.SpectralInterval} {E : Type uP2a}
      [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (H : E →ₗ[ℝ] E)
      (hH : InexactRealizations.Analysis.Admissible I H) (e : E) (he : ‖e‖ = 1) (p : Polynomial ℝ),
      (InexactRealizations.Budgets.FiniteSpectrum.ofVector H hH e he).polynomialNorm p = ‖((Polynomial.aeval H) p) e‖ :=
  @InexactRealizations.Budgets.FiniteSpectrum.ofVector_polynomialNorm

end

section
/-! ## Lemma A.1 (Budget duality), p. 16, Displays (30)–(31)

The suprema below range actual finitely supported probability measures. polynomialNorm is the square root of the integral of the squared polynomial. The relative limsup and operator norm are the actual dimension-uniform execution quantities; both arbitrary and symmetric perturbations are included.
-/

theorem lemma_A_1_additive :
    ∀ {N : ℕ} (p : ENNReal),
      1 ≤ p →
        ∀ (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
          h.ChebyshevExact I →
            0 < N →
              ∀ (r t : ℝ),
                0 ≤ r →
                  0 ≤ t →
                    InexactRealizations.Budgets.additiveRisk p h I r t =
                      sSup (Set.range fun alpha : InexactRealizations.Budgets.FiniteSpectralMeasure I ↦
          r * alpha.polynomialNorm h.terminal + t * InexactRealizations.Budgets.callNorm (InexactRealizations.Budgets.dualExponent p)
            (fun s : Fin N ↦ alpha.polynomialNorm (h.response s))) :=
  @InexactRealizations.Budgets.journal_additive_duality

theorem lemma_A_1_relative :
    ∀ {N : ℕ} (p : ENNReal),
      1 ≤ p →
        ∀ (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
          0 < N →
            ∀ (r : ℝ),
              0 < r →
                ∀ (symmetric : Bool),
                  InexactRealizations.Budgets.localRelativeGain p h I r = InexactRealizations.Budgets.operatorGain p h I symmetric ∧
                    InexactRealizations.Budgets.operatorGain p h I symmetric =
                      sSup {v : ℝ | ∃ alpha beta : InexactRealizations.Budgets.FiniteSpectralMeasure I,
          v = InexactRealizations.Budgets.callNorm (InexactRealizations.Budgets.dualExponent p)
            (fun s : Fin N ↦ alpha.polynomialNorm (h.response s) * beta.polynomialNorm (h.query s))} :=
  @InexactRealizations.Budgets.journal_relative_duality

theorem lemma_A_1_actual_operator_norm :
    ∀ {N : ℕ} (p : ENNReal),
      1 ≤ p →
        ∀ (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
          0 < N →
            ∀ (r : ℝ),
              0 < r →
                ∀ (symmetric : Bool),
                  InexactRealizations.Budgets.localRelativeGain p h I r = InexactRealizations.Budgets.operatorNormGain p h I symmetric ∧
                    InexactRealizations.Budgets.operatorNormGain p h I symmetric =
                      sSup {v : ℝ | ∃ alpha beta : InexactRealizations.Budgets.FiniteSpectralMeasure I,
          v = InexactRealizations.Budgets.callNorm (InexactRealizations.Budgets.dualExponent p)
            (fun s : Fin N ↦ alpha.polynomialNorm (h.response s) * beta.polynomialNorm (h.query s))} :=
  @InexactRealizations.Budgets.journal_relative_operatorNorm_duality

end

section
/-! ## Appendix A, p. 17, text after Lemma A.1 (single-call and pooled budgets)

At gamma1 the exact gain is the maximum product of response and query peaks. At gamma2 the actual operator and relative gains equal the spectral kernel gain. The relative-error linearization has a remainder constant depending only on the history, L and the fixed scale cap.
-/

theorem text_A_single_call_operator :
    ∀ {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
      0 < N →
        ∀ (symmetric : Bool),
          InexactRealizations.Budgets.operatorGain 1 h I symmetric =
            InexactRealizations.Budgets.callNorm ⊤ fun s => InexactRealizations.Centered.responsePeak h I s * InexactRealizations.Prose.queryPeak h I s :=
  @InexactRealizations.Prose.singleCall_operatorGain

theorem text_A_single_call_relative :
    ∀ {N : ℕ} (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval),
      0 < N →
        ∀ (r : ℝ),
          0 < r →
            InexactRealizations.Budgets.localRelativeGain 1 h I r =
              InexactRealizations.Budgets.callNorm ⊤ fun s => InexactRealizations.Centered.responsePeak h I s * InexactRealizations.Prose.queryPeak h I s :=
  @InexactRealizations.Prose.singleCall_relativeGain

theorem text_A_uniform_relative_remainder {N : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (p : ENNReal) (hp : 1 ≤ p) (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (initial : E) (noise : Fin N → E)
    (v : h.Execution H initial noise) (t t0 : ℝ) (ht : 0 < t) (htt0 : t ≤ t0) (hi : ‖initial‖ ≤ 1)
    (delta : Fin N → ℝ) (hw : InexactRealizations.Budgets.RelativeErrors p h H initial noise v t delta) :
    ∃ D : Fin N → E →ₗ[ℝ] E, (∀ s : Fin N, ‖(D s).toContinuousLinearMap‖ ≤ delta s) ∧
      ‖v.output - ((Polynomial.aeval H) h.terminal) initial - t • h.firstVariation H D initial‖ ≤
        t ^ 2 * InexactRealizations.Prose.uniformRelativeRemainder h I.L t0 := by
  let : p.HolderConjugate (InexactRealizations.Budgets.dualExponent p) := InexactRealizations.Budgets.holder_dualExponent p hp
  exact InexactRealizations.Prose.relative_linearization_uniform (p := p) (q := InexactRealizations.Budgets.dualExponent p)
    h I H hH initial noise v t t0 ht htt0 hi delta hw

end

section
/-! ## Appendix A, p. 17, text following Lemma A.1 (pooled-energy identity)

For the pooled energy budget the two actual gains equal the spectral maximum
for every causal history. The preceding main-text theorem proves the finite
spectral-average bound and its point-mass attainment for both perturbation classes.
-/
theorem text_A_pooled_energy_identity {N : ℕ} (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (hN : 0 < N) (r : ℝ) (hr : 0 < r)
    (symmetric : Bool) :
    InexactRealizations.Budgets.localRelativeGain 2 h I r =
        InexactRealizations.Budgets.operatorNormGain 2 h I symmetric ∧
      InexactRealizations.Budgets.operatorNormGain 2 h I symmetric = h.spectralGain I :=
  theorem_4_1_actual_relative_operator_spectral h I hN r hr symmetric
end

end Part2

section Part3

open Polynomial Polynomial.Chebyshev MeasureTheory Filter Topology
open scoped BigOperators Matrix

section
/-! ## Display (32), p. 17 (the Chebyshev tensor expansion)
`chebyshevBezout N` is the half divided difference of the first-kind
Chebyshev polynomial, including its continuous diagonal value. The zero-degree
source has weight one half. This is the finite expansion used by the actual
Flat construction. -/
theorem display_32_tensor (n : ℕ) (x y : ℝ) :
    InexactRealizations.chebyshevBezout (n + 1) x y =
      ∑ m ∈ Finset.range (n + 1),
        (if m = 0 then (1 / 2 : ℝ) else (T ℝ m).eval x) *
          (U ℝ ((n - m : ℕ) : ℤ)).eval y := by
  exact InexactRealizations.hall_expansion n x y
end

section
/-! ## Proof of Theorem 3.1, p. 17 (exact stochastic response identity)
The raw conditional second-moment law derives square integrability, so the
statement adds no integrability premise. `initial` is the initial error,
`stochasticOutput` the actual terminal error, and `responseOperator` is
polynomial functional calculus of the physical response. Conditional
centering suffices for the exact identity. -/
variable {N : ℕ} {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : Filtration ℕ mΩ}
  {w : ℕ → Ω → E}
theorem text_B_stochastic_response (h : InexactRealizations.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (σ : ℝ) (hw : InexactRealizations.Prose.RawAdditiveLaw N 𝓕 w μ σ) :
    (∫ ω, ‖h.stochasticOutput H initial w ω‖ ^ 2 ∂μ) =
      ‖(aeval H h.terminal) initial‖ ^ 2 +
        ∑ s : Fin N, ∫ ω, ‖h.responseOperator H s (w s.val ω)‖ ^ 2 ∂μ :=
  h.integral_stochasticOutput_norm_sq H initial hw.martingale
end

section
/-! ## Lemma B.1 (Implementation of Flat), p. 17
`ratioProgram` is Algorithm 1 with its printed ratio preparation. The statements
use this concrete four-register program and the concrete Flat history.
The all-oracle statement includes every possible oracle-error stream. Vector
slots include the current query/answer register; scalars and oracle workspace
are excluded, as in the article. -/
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
theorem lemma_B_1_queries (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) (s : Fin N) :
    (InexactRealizations.Algorithms.Flat.ratioProgram I N).queryAt oracle initial s =
      (InexactRealizations.Flat.history I N hN).oracleQuery initial oracle s :=
  InexactRealizations.Algorithms.Flat.ratioProgram_query I N hN oracle initial s

theorem lemma_B_1_output (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) :
    (InexactRealizations.Algorithms.Flat.ratioProgram I N).output oracle initial =
      (InexactRealizations.Flat.history I N hN).oracleOutput initial oracle :=
  InexactRealizations.Algorithms.Flat.ratioProgram_output I N hN oracle initial

theorem lemma_B_1_terminal_and_responses (I : InexactRealizations.Operators.SpectralInterval)
    (N : ℕ) (hN : 2 ≤ N) (H : E →ₗ[ℝ] E) (initial : E) (w : Fin N → E) :
    (InexactRealizations.Algorithms.Flat.ratioProgram I N).output (fun s y ↦ H y + w s) initial =
      (aeval H (I.residual N)) initial +
        ∑ s, (aeval H ((InexactRealizations.Flat.history I N hN).response s)) (w s) :=
  InexactRealizations.Algorithms.Flat.journal_flat_physical_response I N hN H initial w

theorem lemma_B_1_calls (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (oracle : Fin N → E → E) (initial : E) :
    ((InexactRealizations.Algorithms.Flat.ratioProgram I N).run oracle initial).calls = N :=
  InexactRealizations.Algorithms.Flat.journal_flat_oracle_calls I N oracle initial

theorem lemma_B_1_vectors : Fintype.card (Fin 4) = 4 :=
  InexactRealizations.Algorithms.Flat.journal_flat_vector_slots
end

section
/-! ## Proof of Theorem 3.1, p. 18 (the Prefix variance limit)
`Classical.history` is the actual Prefix history. `decay I` is exp(-theta)
for eta = cosh(theta). The exact finite coefficient and its positive limiting
series are stated without numerical parameters. -/
theorem text_B_prefix_variance (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    InexactRealizations.Classical.variance I N = (16 * I.epsilon N ^ 2 / I.delta ^ 2) *
      ((N : ℝ) ^ 2 / 4 + ∑ s ∈ Finset.Ico 1 N, ((N : ℝ) - s) ^ 2 * I.den s ^ 2) :=
  InexactRealizations.Classical.variance_exact I N hN

theorem text_B_prefix_variance_limit (I : InexactRealizations.Operators.SpectralInterval) :
    Tendsto (InexactRealizations.Classical.variance I) atTop
      (𝓝 ((16 / I.delta ^ 2) * ∑' k : ℕ, (k : ℝ) ^ 2 * InexactRealizations.Classical.decay I ^ (2 * k))) :=
  InexactRealizations.Classical.variance_tendsto I

theorem text_B_prefix_variance_limit_positive (I : InexactRealizations.Operators.SpectralInterval) :
    0 < (16 / I.delta ^ 2) * ∑' k : ℕ, (k : ℝ) ^ 2 * InexactRealizations.Classical.decay I ^ (2 * k) :=
  InexactRealizations.Classical.varianceLimit_pos I
end

section
/-! ## Lemma C.1 (Separation of two masses), p. 19, Display (33)
The displayed quantities are the article's W-plus, W-minus and squared Theta.
`IsLeast` states an attained minimum over all feasible profiles. The signed
integrand is written with its two literal branches. The proof uses supporting
quadratics and integer cone counts; the printed minimum and its domain are
unchanged. -/
theorem lemma_C_1_nonnegative (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N) :
    IsLeast {E : ℝ | ∃ α β : Fin N → ℝ,
      (∀ s, 0 ≤ α s) ∧ (∀ s, 0 ≤ β s) ∧
      (∑ s, α s = ((N : ℝ) ^ 2 + 1) / 4) ∧
      (∑ s, β s = ((N : ℝ) ^ 2 - 1) / 4) ∧
      E = ∑ s, ((α s) ^ 2 + (β s) ^ 2 + 4 * α s * β s)}
      ((N : ℝ) ^ 3 / 4 * (1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2))) := by
  simpa only [InexactRealizations.Lower.evenMass, InexactRealizations.Lower.oddMass,
    InexactRealizations.Lower.oddEnergy_eq_correction (by omega : 0 < N), InexactRealizations.Lower.oddCorrectionSq]
    using InexactRealizations.Lower.nonnegative_mass_minimum N hN hodd (Fintype.card_fin N)

theorem lemma_C_1_signed (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N) :
    IsLeast {E : ℝ | ∃ α β : Fin N → ℝ,
      (∑ s, α s = ((N : ℝ) ^ 2 + 1) / 4) ∧
      (∑ s, β s = ((N : ℝ) ^ 2 - 1) / 4) ∧
      E = ∑ s, if 0 ≤ α s * β s then (α s) ^ 2 + (β s) ^ 2 + 4 * α s * β s
        else (α s) ^ 2 + (β s) ^ 2 + α s * β s}
      ((N : ℝ) ^ 3 / 4 * (1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2))) := by
  simpa only [InexactRealizations.Lower.evenMass, InexactRealizations.Lower.oddMass, InexactRealizations.Lower.massEnergy,
    InexactRealizations.Lower.oddEnergy_eq_correction (by omega : 0 < N), InexactRealizations.Lower.oddCorrectionSq]
    using InexactRealizations.Lower.signed_mass_minimum N hN hodd (Fintype.card_fin N)

theorem lemma_C_1_value (N : ℕ) (hN : 3 ≤ N) :
    (((N : ℝ) ^ 2 + 1) / 4) ^ 2 / (((N : ℝ) + 1) / 2) +
      (((N : ℝ) ^ 2 - 1) / 4) ^ 2 / (((N : ℝ) - 1) / 2) =
      (N : ℝ) ^ 3 / 4 * (1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2)) := by
  simpa only [InexactRealizations.Lower.evenMass, InexactRealizations.Lower.oddMass,
    InexactRealizations.Lower.oddEnergy_eq_correction (by omega : 0 < N), InexactRealizations.Lower.oddCorrectionSq]
    using InexactRealizations.Lower.mass_value_quotient N hN

theorem text_C_signed_energy_coercive (α β : ℝ) :
    (α ^ 2 + β ^ 2) / 2 ≤
      if 0 ≤ α * β then α ^ 2 + β ^ 2 + 4 * α * β else α ^ 2 + β ^ 2 + α * β :=
  InexactRealizations.Lower.massEnergy_coercive α β
end

section
/-! ## Lemma C.2 (Four-corner bound), pp. 19–20, Displays (34)–(35)
The separated factors are arbitrary real functions; the article imposes no
polynomial degree, sign or normalization restriction. The hypothesis is the
printed universal factorization of the actual Chebyshev tensor. -/
theorem lemma_C_2_ordinary (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (f q : Fin N → ℝ → ℝ)
    (hf : ∀ x y, (∑ s, f s x * q s y) = InexactRealizations.chebyshevBezout N x y) :
    (N : ℝ) ^ 3 / 4 * (1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2)) ≤
      (3 / 8 : ℝ) * ∑ s, ((f s 1) ^ 2 * (q s 1) ^ 2 + (f s (-1)) ^ 2 * (q s (-1)) ^ 2) +
      (1 / 8 : ℝ) * ∑ s, ((f s 1) ^ 2 * (q s (-1)) ^ 2 + (f s (-1)) ^ 2 * (q s 1) ^ 2) := by
  simpa only [InexactRealizations.Lower.fourCornerEnergy, mul_pow,
    InexactRealizations.Lower.oddEnergy_eq_correction (by omega : 0 < N), InexactRealizations.Lower.oddCorrectionSq]
    using InexactRealizations.Lower.chebyshev_four_corner_lower N hN hodd f q hf

theorem lemma_C_2_symmetric (N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (f q : Fin N → ℝ → ℝ)
    (hf : ∀ x y, (∑ s, f s x * q s y) = InexactRealizations.chebyshevBezout N x y) :
    (N : ℝ) ^ 3 / 4 * (1 + ((N : ℝ) - 1) / (((N : ℝ) + 1) * (N : ℝ) ^ 2)) ≤
      (3 / 8 : ℝ) * ∑ s, ((f s 1) ^ 2 * (q s 1) ^ 2 + (f s (-1)) ^ 2 * (q s (-1)) ^ 2) +
      (1 / 16 : ℝ) * ∑ s, (f s 1 * q s (-1) + f s (-1) * q s 1) ^ 2 := by
  simpa only [InexactRealizations.Lower.symmetricCornerEnergy, mul_pow,
    InexactRealizations.Lower.oddEnergy_eq_correction (by omega : 0 < N), InexactRealizations.Lower.oddCorrectionSq]
    using InexactRealizations.Lower.chebyshev_symmetric_four_corner_lower N hN hodd f q hf
end

section
/-! ## Lemma C.3 (Implementation of Balanced), p. 21
`journalProgram` is the concrete nine-vector averaged-Prefix Algorithm 2,
including the compensated updates and its printed ratio preparation. Its
actual queries and physical responses agree for arbitrary oracle streams.
The terminal polynomial and physical responses are displayed in the actual
output identity. -/
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
theorem lemma_C_3_queries (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) (s : Fin N) :
    (InexactRealizations.Algorithms.AveragedBalanced.journalProgram I N).queryAt oracle initial s =
      (InexactRealizations.Balanced.history I N hN).oracleQuery initial oracle s :=
  InexactRealizations.Algorithms.AveragedBalanced.journal_balanced_queries I N hN oracle initial s

theorem lemma_C_3_output (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) :
    (InexactRealizations.Algorithms.AveragedBalanced.journalProgram I N).output oracle initial =
      (InexactRealizations.Balanced.history I N hN).oracleOutput initial oracle :=
  InexactRealizations.Algorithms.AveragedBalanced.journal_balanced_output I N hN oracle initial

theorem lemma_C_3_terminal_and_responses (I : InexactRealizations.Operators.SpectralInterval)
    (N : ℕ) (hN : 2 ≤ N) (H : E →ₗ[ℝ] E) (initial : E) (w : Fin N → E) :
    (InexactRealizations.Algorithms.AveragedBalanced.journalProgram I N).output (fun s y ↦ H y + w s) initial =
      (aeval H (I.residual N)) initial +
        ∑ s, (aeval H ((InexactRealizations.Balanced.history I N hN).response s)) (w s) :=
  InexactRealizations.Algorithms.AveragedBalanced.journal_balanced_physical_response I N hN H initial w

theorem lemma_C_3_calls (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (oracle : Fin N → E → E) (initial : E) :
    ((InexactRealizations.Algorithms.AveragedBalanced.journalProgram I N).run oracle initial).calls = N :=
  InexactRealizations.Algorithms.AveragedBalanced.journal_balanced_oracle_calls I N oracle initial

theorem lemma_C_3_vectors : Fintype.card (Fin 9) = 9 :=
  InexactRealizations.Algorithms.AveragedBalanced.journal_balanced_vector_slots
end

section
/-! ## Proof of Theorem 4.2 and Corollary 4.3, pp. 21–23 (the forced Prefix recurrence)
`prefixPair` is the actual forced two-register recurrence used by Algorithm 2.
Its exact physical response is the Prefix response; its first component is
not an assumed solution of the recurrence. The remaining arithmetic in this
proof establishes the bounds already stated with Corollary 4.3. -/
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
theorem text_D_forced_prefix (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (H : E →ₗ[ℝ] E) (initial : E) (e : ℕ → E) :
    (InexactRealizations.Roundoff.prefixPair I H initial e N).1 =
      (aeval H (I.residual N)) initial +
        ∑ s : Fin N, (aeval H ((InexactRealizations.Classical.history I N).response s)) (e s.val) :=
  InexactRealizations.Roundoff.prefixPair_response I N H initial e
end


section StrictGap2
/-! ## Appendix D, pp. 22–23 (the exact initial-error coefficient)

The same actual componentwise execution has the printed finite coefficient 8.
The Chebyshev ratios, parity-weight sum and all three error-channel sums are
proved below; the quadratic remainder retains its allowed dependence on N and kappa.
-/
open scoped BigOperators
open InexactRealizations.Algorithms.AveragedBalanced InexactRealizations.Accuracy.Execution

private theorem den_cassini (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) :
    I.den s * I.den (s + 2) - I.den (s + 1) ^ 2 = I.eta ^ 2 - 1 := by
  induction s with
  | zero => rw [I.den_zero, I.den_one, I.den_add_two]; simp; ring
  | succ s ih =>
    have h₁ := I.den_add_two s
    have h₂ := I.den_add_two (s + 1)
    rw [show s + 1 + 1 = s + 2 by omega, show s + 1 + 2 = s + 3 by omega]
    linear_combination I.den (s + 1) * h₂ - I.den (s + 2) * h₁ + ih

private theorem den_ratio_mono (I : InexactRealizations.Operators.SpectralInterval) :
    Monotone (fun s : ℕ => I.den (s + 1) / I.den s) := by
  apply monotone_nat_of_le_succ
  intro s
  apply (div_le_div_iff₀ (I.den_pos s) (I.den_pos (s + 1))).mpr
  have h := den_cassini I s
  have he := I.eta_gt_one
  have hs := sq_nonneg (I.eta - 1)
  nlinarith

private theorem den_ratio_two (I : InexactRealizations.Operators.SpectralInterval) {a b : ℕ} (hab : a ≤ b) :
    I.den (a + 2) / I.den a ≤ I.den (b + 2) / I.den b := by
  have h₁ := den_ratio_mono I hab
  have h₂ := den_ratio_mono I (Nat.add_le_add_right hab 1)
  have h := mul_le_mul h₁ h₂
    (div_nonneg (I.den_pos (a + 2)).le (I.den_pos (a + 1)).le)
    (div_nonneg (I.den_pos (b + 1)).le (I.den_pos b).le)
  convert h using 1 <;> field_simp [I.den_ne (a + 1), I.den_ne (b + 1)]

private theorem den_product (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hs2 : 2 ≤ s) (hs : s ≤ N) :
    I.den s * I.den (N - 2) ≤ I.den (s - 2) * I.den N := by
  have h := den_ratio_two I (show s - 2 ≤ N - 2 by omega)
  rw [Nat.sub_add_cancel hs2, Nat.sub_add_cancel (show 2 ≤ N by omega)] at h
  have h' := (div_le_div_iff₀ (I.den_pos (s - 2)) (I.den_pos (N - 2))).mp h
  nlinarith

private theorem sharp_distance (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hs : s ≤ N) :
    I.epsilon N * I.den s * distanceCoefficient I N s ≤
      ((N : ℝ) + 3) / (2 * I.den (N - 2)) := by
  by_cases hs2 : s < 2
  · simp only [distanceCoefficient, hs2, ite_true, mul_zero]
    exact div_nonneg (by positivity) (by positivity [I.den_pos (N - 2)])
  · have hp := den_product I (show 2 ≤ s by omega) hs
    have hr : I.den s / (I.den N * I.den (s - 2)) ≤ 1 / I.den (N - 2) := by
      apply (div_le_div_iff₀ (mul_pos (I.den_pos N) (I.den_pos (s - 2)))
        (I.den_pos (N - 2))).mpr
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ ((N : ℝ) + 3) / 2)
    convert hh using 1 <;> simp only [distanceCoefficient, hs2, ite_false,
      InexactRealizations.Operators.SpectralInterval.epsilon, div_eq_mul_inv, mul_inv_rev] <;> ring

private theorem prefix_point (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) :
    I.den (s + 1) * prefixInitialCoefficient I s ≤ 20 * I.L / I.delta := by
  have hL : 0 < I.L := lt_trans I.mu_pos I.mu_lt_L
  have heta : I.eta = 2 * I.L / I.delta - 1 := by
    unfold InexactRealizations.Operators.SpectralInterval.eta
    field_simp [I.delta_pos.ne']
    unfold InexactRealizations.Operators.SpectralInterval.delta
    ring
  cases s with
  | zero =>
    have hsum : I.L + I.mu ≠ 0 := ne_of_gt (add_pos hL I.mu_pos)
    have hid : I.eta * (3 + 4 * I.L / (I.L + I.mu)) + 1 =
        3 * I.eta + 1 + 4 * I.L / I.delta := by
      rw [InexactRealizations.Operators.SpectralInterval.eta]
      field_simp
      ring
    simp only [prefixInitialCoefficient, beta, alpha, Nat.zero_sub, Nat.zero_add,
      I.den_zero, I.den_one, mul_zero, add_zero, div_one]
    have hp : 0 < I.L / I.delta := div_pos hL I.delta_pos
    convert (show I.eta * (3 + 4 * I.L / (I.L + I.mu)) + 1 ≤
        20 * I.L / I.delta by rw [hid, heta]; simp only [div_eq_mul_inv] at *; linarith) using 1
    field_simp [ne_of_gt (lt_trans zero_lt_one I.eta_gt_one), hsum]
    ring
  | succ s =>
    have hprev : I.den s / I.den (s + 1) ≤ 1 :=
      (div_le_one (I.den_pos (s + 1))).mpr ((den_strictMono I).monotone (by omega))
    have hid : I.den (s + 1 + 1) * prefixInitialCoefficient I (s + 1) =
        6 * I.eta + I.den s / I.den (s + 1) + 4 + 8 * I.L / I.delta := by
      rw [prefixInitialCoefficient, beta_succ_eq, alpha_eq]
      simp only [InexactRealizations.Operators.Prefix.beta, InexactRealizations.Operators.Prefix.gamma, Nat.add_sub_cancel]
      rw [show s + 1 + 1 = s + 2 by omega]
      field_simp [I.den_ne s, I.den_ne (s + 1), I.den_ne (s + 2), I.delta_pos.ne']
      rw [I.den_add_two]
      ring
    rw [hid, heta]
    simp only [div_eq_mul_inv] at *
    linarith

private theorem sum_linear_profile (N : ℕ) :
    (∑ s : Fin N, ((N : ℝ) - s.val)) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => (N : ℝ) - s) N, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hh : (∑ s ∈ Finset.range N, (s : ℝ)) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [hh]
  ring

private theorem prefix_sum (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} :
    (∑ s : Fin N, stateWeight I N s.val * prefixInitialCoefficient I s.val) ≤
      10 * (N : ℝ) * ((N : ℝ) + 1) * I.L / (I.delta * I.den (N - 2)) := by
  have hp (s : Fin N) : stateWeight I N s.val * prefixInitialCoefficient I s.val ≤
      ((N : ℝ) - s.val) * (20 * I.L / I.delta) / I.den N := by
    have hh := mul_le_mul_of_nonneg_left (prefix_point I s.val)
      (div_nonneg (sub_nonneg.mpr (by exact_mod_cast s.isLt.le : (s.val : ℝ) ≤ N)) (I.den_pos N).le)
    change ((N : ℝ) - s.val) * I.den (s.val + 1) / I.den N * _ ≤ _
    convert hh using 1 <;> ring
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hp s)
  have he : (∑ s : Fin N, ((N : ℝ) - s.val) * (20 * I.L / I.delta) / I.den N) =
      10 * (N : ℝ) * ((N : ℝ) + 1) * I.L / (I.delta * I.den N) := by
    rw [← Finset.sum_div, ← Finset.sum_mul, sum_linear_profile]
    ring
  rw [he] at hh
  refine hh.trans ?_
  have hm := (den_strictMono I).monotone (show N - 2 ≤ N by omega)
  apply div_le_div_of_nonneg_left (by positivity [lt_trans I.mu_pos I.mu_lt_L])
    (mul_pos I.delta_pos (I.den_pos (N - 2))) (mul_le_mul_of_nonneg_left hm I.delta_pos.le)

private theorem oracle_theta_weight (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ}
    (hN : 2 ≤ N) (s : Fin N) :
    oracleWeight I N hN s * theta I N s.val ≤
      2 * ((N : ℝ) + 1) * I.epsilon N * InexactRealizations.Balanced.omega N s.val * I.den s.val / I.delta := by
  have hw := (InexactRealizations.Balanced.omega_pos hN s.isLt).le
  have he : 0 ≤ 4 * I.epsilon N / I.delta := by
    have hdN := I.den_pos N
    have hd := I.delta_pos
    unfold InexactRealizations.Operators.SpectralInterval.epsilon
    positivity
  have hh := mul_le_mul_of_nonneg_left (classMass_upper (s := s.val) hN)
    (mul_nonneg (mul_nonneg he (I.den_pos s.val).le) hw)
  rw [oracleWeight_eq I hN s, theta_eq I hN s.isLt]
  convert hh using 1
  all_goals field_simp [(InexactRealizations.Balanced.normalizer_pos I hN s.isLt).ne']
  all_goals ring

private theorem oracle_distance_point (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ}
    (hN : 2 ≤ N) (s : Fin N) :
    oracleWeight I N hN s * I.L * (6 * theta I N s.val * distanceCoefficient I N s.val) ≤
      (6 * ((N : ℝ) + 1) * ((N : ℝ) + 3) * I.L / (I.delta * I.den (N - 2))) *
        (if s.val < 2 then 0 else InexactRealizations.Balanced.omega N s.val) := by
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  by_cases hs2 : s.val < 2
  · simp [distanceCoefficient, hs2]
  · simp only [hs2, ite_false]
    have h₁ := mul_le_mul_of_nonneg_right (oracle_theta_weight I hN s)
      (mul_nonneg (by positivity : 0 ≤ 6 * I.L) (distanceCoefficient_nonneg I N s.val))
    have h₂ := mul_le_mul_of_nonneg_left (sharp_distance I s.isLt.le)
      (show 0 ≤ 12 * ((N : ℝ) + 1) * InexactRealizations.Balanced.omega N s.val * I.L / I.delta by
        exact div_nonneg (mul_nonneg (mul_nonneg (by positivity)
          (InexactRealizations.Balanced.omega_pos hN s.isLt).le) hL) I.delta_pos.le)
    calc
      _ ≤ (2 * ((N : ℝ) + 1) * I.epsilon N * InexactRealizations.Balanced.omega N s.val * I.den s.val /
          I.delta) * (6 * I.L * distanceCoefficient I N s.val) := by
        convert h₁ using 1
        all_goals ring
      _ ≤ _ := by
        convert h₂ using 1
        all_goals ring

private theorem oracle_normalizer_sum (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ}
    (hN : 2 ≤ N) :
    (∑ s : Fin N, oracleWeight I N hN s * I.L * (3 / InexactRealizations.Balanced.normalizer I N s.val)) ≤
      6 * (N : ℝ) * ((N : ℝ) + 1) * I.L / (I.delta * I.den (N - 2)) := by
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hp (s : Fin N) : oracleWeight I N hN s * I.L *
      (3 / InexactRealizations.Balanced.normalizer I N s.val) ≤
      6 * ((N : ℝ) + 1) * I.L / (I.delta * I.den N) := by
    have hh := mul_le_mul_of_nonneg_right (oracleWeight_normalizer I hN s)
      (show 0 ≤ 3 * I.L by positivity)
    simp only [InexactRealizations.Operators.SpectralInterval.epsilon] at hh
    convert hh using 1 <;> ring
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hp s)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  have hm := (den_strictMono I).monotone (show N - 2 ≤ N by omega)
  refine hh.trans ?_
  have hd := div_le_div_of_nonneg_left (show 0 ≤ 6 * (N : ℝ) * ((N : ℝ) + 1) * I.L by positivity)
    (mul_pos I.delta_pos (I.den_pos (N - 2))) (mul_le_mul_of_nonneg_left hm I.delta_pos.le)
  convert hd using 1
  all_goals ring


private def auxG2O_tail (N j : ℕ) : ℝ := if 2 ≤ j then InexactRealizations.Balanced.omega N j else 0

private theorem auxG2O_tail_zero (N : ℕ) : auxG2O_tail N 0 = 0 := rfl
private theorem auxG2O_tail_one (N : ℕ) : auxG2O_tail N 1 = 0 := rfl

private theorem auxG2O_pair_sum (f : ℕ → ℝ) (m : ℕ) :
    (∑ j ∈ Finset.range (2 * m), f j) =
      ∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

private theorem auxG2O_sum_affine (a b : ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range m, (a - b * k)) =
      (m : ℝ) * a - b * ((m : ℝ) * ((m : ℝ) - 1) / 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem auxG2O_even_pair (n k : ℕ) :
    auxG2O_tail (2 * (n + 1)) (2 * (k + 1)) +
      auxG2O_tail (2 * (n + 1)) (2 * (k + 1) + 1) =
        ((2 * (n : ℝ) + 1) - 2 * k) / (n + 1) := by
  have he : Even (2 * (n + 1)) := even_two_mul _
  have hk : 2 ≤ 2 * (k + 1) := by omega
  have hk' : 2 ≤ 2 * (k + 1) + 1 := by omega
  simp only [auxG2O_tail, hk, hk', ite_true, InexactRealizations.Balanced.omega,
    show ¬2 * (k + 1) < 2 by omega, show ¬2 * (k + 1) + 1 < 2 by omega,
    ite_false, he]
  rw [show (2 * (k + 1)) % 2 = 0 by omega,
    show (2 * (k + 1) + 1) % 2 = 1 by omega]
  norm_num only [Nat.cast_zero, Nat.cast_one]
  push_cast
  field_simp
  ring

private theorem auxG2O_even_sum (n : ℕ) :
    (∑ j ∈ Finset.range (2 * (n + 1)), auxG2O_tail (2 * (n + 1)) j) =
      (n + 1 : ℝ) - 1 / (n + 1) := by
  rw [auxG2O_pair_sum, Finset.sum_range_succ']
  simp only [Nat.mul_zero, auxG2O_tail_zero, auxG2O_tail_one, zero_add, add_zero]
  simp_rw [auxG2O_even_pair]
  rw [← Finset.sum_div, auxG2O_sum_affine]
  field_simp
  ring

private theorem auxG2O_odd_pair (n k : ℕ) :
    auxG2O_tail (2 * (n + 1) + 1) (2 * (k + 1)) +
      auxG2O_tail (2 * (n + 1) + 1) (2 * (k + 1) + 1) =
        (((2 * (n + 1 : ℝ) + 2) / ((2 * (n + 1 : ℝ) + 1) ^ 2 + 1)) +
          1 / (2 * (n + 1 : ℝ) + 2)) * (2 * (n + 1 : ℝ) - 2 * k) := by
  have he : ¬Even (2 * (n + 1) + 1) := by simp
  have hk : 2 ≤ 2 * (k + 1) := by omega
  have hk' : 2 ≤ 2 * (k + 1) + 1 := by omega
  have hke : Even (2 * (k + 1)) := even_two_mul _
  have hko : ¬Even (2 * (k + 1) + 1) := by simp
  simp only [auxG2O_tail, hk, hk', ite_true, InexactRealizations.Balanced.omega,
    show ¬2 * (k + 1) < 2 by omega, show ¬2 * (k + 1) + 1 < 2 by omega,
    ite_false, he, hke, hko]
  push_cast
  ring

private theorem auxG2O_odd_last (n : ℕ) :
    auxG2O_tail (2 * (n + 1) + 1) (2 * (n + 1)) =
      2 * (2 * (n + 1 : ℝ) + 2) / ((2 * (n + 1 : ℝ) + 1) ^ 2 + 1) := by
  have he : ¬Even (2 * (n + 1) + 1) := by simp
  have hk : 2 ≤ 2 * (n + 1) := by omega
  have hke : Even (2 * (n + 1)) := even_two_mul _
  simp only [auxG2O_tail, hk, ite_true, InexactRealizations.Balanced.omega,
    show ¬2 * (n + 1) < 2 by omega, ite_false, he, hke]
  push_cast
  ring

private theorem auxG2O_odd_sum (n : ℕ) :
    (∑ j ∈ Finset.range (2 * (n + 1) + 1), auxG2O_tail (2 * (n + 1) + 1) j) =
      (2 * (n + 1 : ℝ) + 1) / 2 -
        ((n + 2 : ℝ) / (2 * (2 * (n + 1 : ℝ) ^ 2 + 2 * (n + 1 : ℝ) + 1)) +
          1 / (n + 2)) := by
  rw [Finset.sum_range_succ, auxG2O_pair_sum, Finset.sum_range_succ']
  simp only [Nat.mul_zero, auxG2O_tail_zero, auxG2O_tail_one, zero_add, add_zero]
  simp_rw [auxG2O_odd_pair]
  rw [← Finset.mul_sum, auxG2O_sum_affine, auxG2O_odd_last]
  field_simp
  ring

private theorem auxG2O_omega_sum_lt (N : ℕ) (hN : 2 ≤ N) :
    (∑ s : Fin N, if 2 ≤ s.val then InexactRealizations.Balanced.omega N s.val else 0) < (N : ℝ) / 2 := by
  change (∑ s : Fin N, auxG2O_tail N s.val) < _
  rw [Fin.sum_univ_eq_sum_range (auxG2O_tail N) N]
  rcases Nat.even_or_odd N with he | ho
  · obtain ⟨m, hm⟩ := he
    have hNm : N = 2 * m := by omega
    have hmpos : 0 < m := by omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    rw [hNm, auxG2O_even_sum]
    push_cast
    have hn : 0 < (1 : ℝ) / (n + 1) := by positivity
    linarith
  · obtain ⟨m, hm⟩ := ho
    have hNm : N = 2 * m + 1 := by omega
    have hmpos : 0 < m := by omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    rw [hNm, auxG2O_odd_sum]
    push_cast
    have ha : 0 < ((n : ℝ) + 2) /
        (2 * (2 * ((n : ℝ) + 1) ^ 2 + 2 * ((n : ℝ) + 1) + 1)) := by positivity
    have hb : 0 < (1 : ℝ) / (n + 2) := by positivity
    linarith

private theorem auxG2O_omega_sum_bound (N : ℕ) (hN : 2 ≤ N) :
    (∑ s : Fin N, if 2 ≤ s.val then InexactRealizations.Balanced.omega N s.val else 0) ≤ (N : ℝ) / 2 :=
  (auxG2O_omega_sum_lt N hN).le

private theorem auxG2O_omega_sum_bound_if_lt (N : ℕ) (hN : 2 ≤ N) :
    (∑ s : Fin N, if s.val < 2 then 0 else InexactRealizations.Balanced.omega N s.val) ≤ (N : ℝ) / 2 := by
  simpa only [← not_lt, ite_not] using auxG2O_omega_sum_bound N hN


private theorem oracle_sum_from_weights (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ}
    (hN : 2 ≤ N)
    (hω : (∑ s : Fin N, if s.val < 2 then (0 : ℝ) else InexactRealizations.Balanced.omega N s.val) ≤ (N : ℝ) / 2) :
    (∑ s : Fin N, oracleWeight I N hN s * I.L * hatInitialCoefficient I N s.val) ≤
      (6 * (N : ℝ) * ((N : ℝ) + 1) + 3 * (N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 3)) *
        I.L / (I.delta * I.den (N - 2)) := by
  have hL := (lt_trans I.mu_pos I.mu_lt_L).le
  have hdist := Finset.sum_le_sum (s := Finset.univ) (fun s _ => oracle_distance_point I hN s)
  rw [← Finset.mul_sum] at hdist
  have hs := mul_le_mul_of_nonneg_left hω
    (show 0 ≤ 6 * ((N : ℝ) + 1) * ((N : ℝ) + 3) * I.L / (I.delta * I.den (N - 2)) by
      exact div_nonneg (by positivity) (mul_pos I.delta_pos (I.den_pos (N - 2))).le)
  have hn := oracle_normalizer_sum I hN
  have hh := add_le_add hn (hdist.trans hs)
  convert hh using 1
  · simp only [hatInitialCoefficient, mul_add, Finset.sum_add_distrib]
  · ring

private theorem oracle_sum (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 2 ≤ N) :
    (∑ s : Fin N, oracleWeight I N hN s * I.L * hatInitialCoefficient I N s.val) ≤
      (6 * (N : ℝ) * ((N : ℝ) + 1) + 3 * (N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 3)) *
        I.L / (I.delta * I.den (N - 2)) :=
  oracle_sum_from_weights I hN (auxG2O_omega_sum_bound_if_lt N hN)

private theorem auxG2A_average_point (I : InexactRealizations.Operators.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs2 : 2 ≤ s) (hs : s + 2 < N)
    (hsharp : ∀ j, j ≤ N → I.epsilon N * I.den j * distanceCoefficient I N j ≤
      ((N : ℝ) + 3) / (2 * I.den (N - 2))) :
    averageWeight I N s * I.L * averageInitialCoefficient I N s ≤
      ((N : ℝ) * (9 * ((N : ℝ) + 3) / ((N : ℝ) - 1) + 1) *
        (I.L / (I.delta * I.den (N - 2)))) * (N - 1 - s : ℕ) := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : 0 < (N : ℝ) - 1 := by linarith
  have hL : 0 ≤ I.L := (I.mu_pos.trans I.mu_lt_L).le
  have hdel := I.delta_pos
  have hden := I.den_pos N
  have hden2 := I.den_pos (N - 2)
  have hd := distanceCoefficient_nonneg I N s
  have hφ := mul_le_mul_of_nonneg_right (averageWeight_phi I hN hs2 hs) hd
  have hdist := mul_le_mul_of_nonneg_left (hsharp s (by omega))
    (show 0 ≤ 2 * (N : ℝ) * (N - 1 - s : ℕ) / (((N : ℝ) - 1) * I.delta) by positivity)
  have hdist' :
      (2 * (N : ℝ) * (N - 1 - s : ℕ) * I.den s /
        (((N : ℝ) - 1) * I.delta * I.den N)) * distanceCoefficient I N s ≤
      (N : ℝ) * (N - 1 - s : ℕ) * ((N : ℝ) + 3) /
        (((N : ℝ) - 1) * I.delta * I.den (N - 2)) := by
    convert hdist using 1 <;>
      simp only [InexactRealizations.Operators.SpectralInterval.epsilon, div_eq_mul_inv, mul_inv_rev] <;> ring
  have hfirst := mul_le_mul_of_nonneg_left (hφ.trans hdist')
    (show 0 ≤ 9 * I.L by positivity)
  have hmass := mul_le_mul_of_nonneg_left (averageWeight_over_mass I hN hs2 hs) hL
  have hmono := (den_strictMono I).monotone (Nat.sub_le N 2)
  have hinv : 1 / I.den N ≤ 1 / I.den (N - 2) :=
    one_div_le_one_div_of_le hden2 hmono
  have hmass2 := mul_le_mul_of_nonneg_left hinv
    (show 0 ≤ I.L * (N : ℝ) * (N - 1 - s : ℕ) / I.delta by positivity)
  have hsecond : I.L * (averageWeight I N s / mass I N (s + 2)) ≤
      I.L * (N : ℝ) * (N - 1 - s : ℕ) / (I.delta * I.den (N - 2)) := by
    apply hmass.trans
    convert hmass2 using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring
  have hh := add_le_add hfirst hsecond
  convert hh using 1
  · simp only [averageInitialCoefficient, show ¬s < 2 by omega, ite_false]
    ring
  · simp only [div_eq_mul_inv, mul_inv_rev]
    ring

private theorem auxG2A_sum_range (m : ℕ) :
    (∑ j ∈ Finset.range m, (j : ℝ)) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

private theorem auxG2A_active_distance_sum (N : ℕ) (hN : 5 ≤ N) :
    (∑ s : Fin (N - 2), if 2 ≤ s.val then ((N - 1 - s.val : ℕ) : ℝ) else 0) ≤
      ((N : ℝ) - 3) * ((N : ℝ) - 2) / 2 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun s : ℕ ↦ if 2 ≤ s then ((N - 1 - s : ℕ) : ℝ) else 0) (N - 2)]
  have hf : (Finset.range (N - 2)).filter (fun s ↦ 2 ≤ s) = Finset.Ico 2 (N - 2) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [← Finset.sum_filter, hf]
  have hr : (∑ s ∈ Finset.Ico 2 (N - 2), ((N - 1 - s : ℕ) : ℝ)) =
      ∑ s ∈ Finset.Ico 2 (N - 2), (s : ℝ) := by
    apply Finset.sum_bij (fun s _ ↦ N - 1 - s)
    · intro s hs
      simp only [Finset.mem_Ico] at hs ⊢
      omega
    · intro a ha b hb he
      simp only [Finset.mem_Ico] at ha hb
      omega
    · intro b hb
      refine ⟨N - 1 - b, ?_, ?_⟩
      · simp only [Finset.mem_Ico] at hb ⊢
        omega
      · simp only [Finset.mem_Ico] at hb
        omega
    · intro s _
      rfl
  rw [hr]
  have hd := Finset.sum_range_add_sum_Ico (fun s : ℕ ↦ (s : ℝ)) (by omega : 2 ≤ N - 2)
  have hh : (∑ s ∈ Finset.Ico 2 (N - 2), (s : ℝ)) ≤ ∑ s ∈ Finset.range (N - 2), (s : ℝ) := by
    have hp : 0 ≤ ∑ s ∈ Finset.range 2, (s : ℝ) := Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
    linarith
  apply hh.trans
  rw [auxG2A_sum_range, Nat.cast_sub (by omega : 2 ≤ N)]
  norm_num
  ring_nf
  exact le_refl _

private theorem auxG2A_average_sum (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ}
    (hN : 2 ≤ N)
    (hsharp : ∀ j, j ≤ N → I.epsilon N * I.den j * distanceCoefficient I N j ≤
      ((N : ℝ) + 3) / (2 * I.den (N - 2))) :
    (∑ s : Fin (N - 2), averageWeight I N s.val * I.L * averageInitialCoefficient I N s.val) ≤
      5 * (N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) - 2) * I.L /
        (I.delta * I.den (N - 2)) := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : 0 < (N : ℝ) - 1 := by linarith
  have hL : 0 ≤ I.L := (I.mu_pos.trans I.mu_lt_L).le
  have hdel := I.delta_pos
  have hden2 := I.den_pos (N - 2)
  by_cases hlarge : 5 ≤ N
  · let P := I.L / (I.delta * I.den (N - 2))
    let C := (N : ℝ) * (9 * ((N : ℝ) + 3) / ((N : ℝ) - 1) + 1) * P
    have hP : 0 ≤ P := by dsimp only [P]; positivity
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    have hp (s : Fin (N - 2)) :
        averageWeight I N s.val * I.L * averageInitialCoefficient I N s.val ≤
          C * (if 2 ≤ s.val then ((N - 1 - s.val : ℕ) : ℝ) else 0) := by
      by_cases hs2 : 2 ≤ s.val
      · rw [ite_eq_left hs2]
        exact auxG2A_average_point I hN hs2 (by have := s.isLt; omega) hsharp
      · simp only [averageInitialCoefficient, show s.val < 2 by omega,
          ite_true, hs2, ite_false, mul_zero, le_refl]
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun s _ ↦ hp s)
    rw [← Finset.mul_sum] at hsum
    have hdist := mul_le_mul_of_nonneg_left (auxG2A_active_distance_sum N hlarge) hC
    apply hsum.trans (hdist.trans ?_)
    have hr : ((N : ℝ) - 3) * (9 * ((N : ℝ) + 3) / ((N : ℝ) - 1) + 1) ≤
        10 * ((N : ℝ) + 1) := by
      have he : ((N : ℝ) - 3) * (9 * ((N : ℝ) + 3) / ((N : ℝ) - 1) + 1) =
          (((N : ℝ) - 3) * (10 * (N : ℝ) + 26)) / ((N : ℝ) - 1) := by
        field_simp
        ring
      rw [he]
      apply (div_le_iff₀ hn1).mpr
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hr
      (show 0 ≤ (N : ℝ) * ((N : ℝ) - 2) * P / 2 by positivity)
    convert hh using 1 <;> dsimp only [C, P] <;> ring
  · have hz : (∑ s : Fin (N - 2), averageWeight I N s.val * I.L * averageInitialCoefficient I N s.val) = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      have hs : s.val < 2 := by have := s.isLt; omega
      simp only [averageInitialCoefficient, hs, ite_true, mul_zero]
    rw [hz]
    positivity


private theorem coefficient_arithmetic {n : ℝ} (hn : 0 ≤ n) :
    6 * n * (n + 1) + 3 * n * (n + 1) * (n + 3) +
        5 * n * (n + 1) * (n - 2) + 10 * n * (n + 1) ≤ 8 * (n + 1) ^ 3 := by
  nlinarith [sq_nonneg n]


/-- Appendix D, pp. 22–23: the finite coefficient has the printed constant 8. -/
theorem appendix_D_finite_initial_coefficient (I : InexactRealizations.Operators.SpectralInterval)
    {N : ℕ} (hN : 2 ≤ N) :
    finiteInitialCoefficient I N hN ≤
      8 * ((N : ℝ) + 1) ^ 3 * I.L / (I.delta * I.den (N - 2)) := by
  have ho := oracle_sum I hN
  have ha := auxG2A_average_sum I hN (fun _ hs => sharp_distance I hs)
  have hx := prefix_sum (N := N) I
  have hh := add_le_add (add_le_add ho ha) hx
  have hc := mul_le_mul_of_nonneg_right
    (coefficient_arithmetic (n := (N : ℝ)) (Nat.cast_nonneg N))
    (show 0 ≤ I.L / (I.delta * I.den (N - 2)) from
      div_nonneg (I.mu_pos.trans I.mu_lt_L).le (mul_pos I.delta_pos (I.den_pos (N - 2))).le)
  refine hh.trans ?_
  convert hc using 1 <;> ring

/-- Appendix D, pp. 22–23: the literal componentwise run has the stated first-order
initial-error coefficient; the displayed quadratic remainder is uniform in dimension. -/
theorem appendix_D_actual_componentwise_initial_coefficient
    {ι : Type*} [Fintype ι] {I : InexactRealizations.Operators.SpectralInterval} {N : ℕ}
    {u uO : ℝ} {p : Prepared I N u}
    {H : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι}
    {initial target : EuclideanSpace ℝ ι} {hu : 0 ≤ u}
    (v : InexactRealizations.Accuracy.Componentwise.Run p H initial target uO hu)
    (hc : ∀ (s : Fin N) (hs : 2 ≤ s.val) (hv : s.val + 2 < N),
      ∃ op, (v.toNormed.stages s).averageOperations hs hv = Sum.inl op)
    (hN : 2 ≤ N) (hu2 : u ≤ 1 / 2) (huO : 0 ≤ uO) (huO1 : uO ≤ 1)
    (hH : InexactRealizations.Analysis.Admissible I H) :
    ‖v.states N 0 - target‖ ≤
      (I.epsilon N + 8 * (u + uO) * ((N : ℝ) + 1) ^ 3 * I.L /
        (I.delta * I.den (N - 2))) * ‖initial - target‖ +
      (2 * (u + uO) * I.L * InexactRealizations.Lower.additiveScale I N +
        8 * u * InexactRealizations.Accuracy.prefixFactor I N) * ‖target‖ +
      (u + uO) ^ 2 * quadraticConstant I.kappa N * (‖initial - target‖ + ‖target‖) := by
  have hh := v.toNormed.finite_accuracy hc hN hu hu2 huO huO1 hH
  have hi := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (appendix_D_finite_initial_coefficient I hN) (add_nonneg hu huO))
    (norm_nonneg (initial - target))
  have hq := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (finiteQuadraticCoefficient_bound I hN) (sq_nonneg (u + uO)))
    (add_nonneg (norm_nonneg (initial - target)) (norm_nonneg target))
  have hb := hh.trans (add_le_add (add_le_add (add_le_add le_rfl hi) le_rfl) hq)
  convert hb using 1
  all_goals first | rfl | ring
end StrictGap2

section
/-! ## Appendix F, p. 25 (the concrete Prefix momentum coefficients)
Natural indices encode the startup separately. The later-step statement uses
s+1 to avoid subtraction at zero. The first-kind normalization is `I.den`.
All coefficients below belong to the concrete executed Prefix configuration. -/
open InexactRealizations.Comparisons.Competitors
theorem text_F_prefix_initial (I : InexactRealizations.Operators.SpectralInterval) :
    (Prefix.config I).alpha 0 = 2 / (I.L + I.mu) ∧ (Prefix.config I).beta 0 = 0 :=
  Prefix.initial_coefficients I

theorem text_F_prefix_coefficients (I : InexactRealizations.Operators.SpectralInterval) (s : ℕ) :
    (Prefix.config I).alpha (s + 1) = 4 * I.den (s + 1) / (I.delta * I.den (s + 2)) ∧
      (Prefix.config I).beta (s + 1) = I.den s / I.den (s + 2) :=
  Prefix.coefficients_succ I s

theorem text_F_prefix_transfer (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (lam : ℝ) :
    (Prefix.history I N).terminal.eval lam =
      (InexactRealizations.Operators.orderedProduct (fun s ↦ (Prefix.config I).matrix s lam) N *ᵥ ![1, 1]) 0 ∧
    ∀ s : Fin N, ((Prefix.history I N).response s).eval lam =
      -(Prefix.config I).alpha s.val *
        (InexactRealizations.Operators.orderedProduct (fun i ↦ (Prefix.config I).matrix (s.val + 1 + i) lam)
          (N - (s.val + 1)) *ᵥ ![1, 0]) 0 :=
  ⟨Momentum.terminal_eval (Prefix.config I) N lam,
    fun s ↦ Momentum.response_eval (Prefix.config I) N s lam⟩
end

section
/-! ## Appendix F, p. 25 (the concrete LF/fractal dyadic schedule)
The exact doubling permutation is constructed, and the steps are its reciprocal
cosine roots. The extension to general horizons mentioned in the article is a
cited construction. The finite configurations compared here at dyadic horizons
use this actual permutation. -/
open InexactRealizations.Comparisons.Competitors InexactRealizations.Channel.Roots
theorem text_F_LF_coefficients (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) (s : Fin (2 ^ k)) :
    (LF.config I k).alpha s.val = 1 / ((I.L + I.mu) / 2 - I.delta / 2 *
      Real.cos (angle (2 ^ k) (dyadicPermutation k s))) ∧
      (LF.config I k).beta s.val = 0 :=
  LF.coefficients I k s

theorem text_F_LF_permutation (k : ℕ) : Function.Bijective (dyadicPermutation k) :=
  dyadicPermutation_bijective k

theorem text_F_LF_terminal (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) :
    (LF.history I k).terminal = I.residual (2 ^ k) := LF.terminal I k

theorem text_F_root_order_terminal (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (e : Equiv.Perm (Fin N)) :
    (InexactRealizations.Channel.Roots.history (steps I N e)).terminal = I.residual N :=
  InexactRealizations.Channel.Roots.history_exact I N e

theorem text_F_LF_transfer (I : InexactRealizations.Operators.SpectralInterval) (k : ℕ) (lam : ℝ) :
    (LF.history I k).terminal.eval lam =
      (InexactRealizations.Operators.orderedProduct (fun s ↦ (LF.config I k).matrix s lam) (2 ^ k) *ᵥ ![1, 1]) 0 ∧
    ∀ s : Fin (2 ^ k), ((LF.history I k).response s).eval lam =
      -(LF.config I k).alpha s.val *
        (InexactRealizations.Operators.orderedProduct (fun i ↦ (LF.config I k).matrix (s.val + 1 + i) lam)
          (2 ^ k - (s.val + 1)) *ᵥ ![1, 0]) 0 :=
  ⟨Momentum.terminal_eval (LF.config I k) (2 ^ k) lam,
    fun s ↦ Momentum.response_eval (LF.config I k) (2 ^ k) s lam⟩
end

section
/-! ## Appendix F, p. 25 (the concrete sine–Jacobi preparation)
`Sine.ratio I N s` is the printed eta_s, and `couplingSq N s` is c_s.
The sine polynomial identification is imported from the cited preceding work;
the statements here concern the actual coefficients and executed history. -/
open InexactRealizations.Comparisons.Competitors
theorem text_F_sine_initial (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    (Sine.config I N).alpha 0 = 2 / (I.L + I.mu) ∧
      (Sine.config I N).beta 0 = 0 ∧ Sine.ratio I N 1 = I.eta :=
  ⟨(Sine.initial_coefficients I N).1, (Sine.initial_coefficients I N).2, Sine.ratio_one I N⟩

theorem text_F_sine_ratio (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (s : ℕ) (hs : 0 < s) (hsN : s < N) :
    Sine.ratio I N (s + 1) = I.eta - InexactRealizations.Operators.SineJacobi.couplingSq N s / Sine.ratio I N s :=
  Sine.ratio_step I N hN s hs hsN

theorem text_F_sine_coefficients (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (s : ℕ) (hs : 0 < s) (hsN : s < N) :
    (Sine.config I N).alpha s = 2 / (I.delta * Sine.ratio I N (s + 1)) ∧
      (Sine.config I N).beta s = InexactRealizations.Operators.SineJacobi.couplingSq N s /
        (Sine.ratio I N s * Sine.ratio I N (s + 1)) :=
  Sine.coefficients I N hN s hs hsN

theorem text_F_sine_terminal (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N) :
    (Sine.history I N).terminal = I.residual N := Sine.terminal I N hN

theorem text_F_sine_transfer (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (lam : ℝ) :
    (Sine.history I N).terminal.eval lam =
      (InexactRealizations.Operators.orderedProduct (fun s ↦ (Sine.config I N).matrix s lam) N *ᵥ ![1, 1]) 0 ∧
    ∀ s : Fin N, ((Sine.history I N).response s).eval lam =
      -(Sine.config I N).alpha s.val *
        (InexactRealizations.Operators.orderedProduct (fun i ↦ (Sine.config I N).matrix (s.val + 1 + i) lam)
          (N - (s.val + 1)) *ᵥ ![1, 0]) 0 :=
  ⟨Momentum.terminal_eval (Sine.config I N) N lam,
    fun s ↦ Momentum.response_eval (Sine.config I N) N s lam⟩
end

section
/-! ## Appendix F, p. 25 (DFB's actual averaged terminal and response)
`DFB.d` is the defined scalar sequence rho_j, including rho_0=1 and the
rho_{-1}=1 startup. `DFB.history` is the actual accelerated averaging program,
with its extrapolated queries, momentum one and step 1/L. The interval domain
implies the nonzero denominators needed by the printed response formula. -/
open InexactRealizations.Comparisons.Competitors
theorem text_F_DFB_scalar_recurrence (L lam : ℝ) (j : ℕ) :
    DFB.d L lam 0 = 1 ∧
      DFB.d L lam (j + 1) = (1 - lam / L) * (2 * DFB.d L lam j - DFB.dPrevious L lam j) :=
  ⟨rfl, DFB.d_step L lam j⟩

theorem text_F_DFB_terminal (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (lam : ℝ) :
    (DFB.history I.L N).terminal.eval lam =
      (∑ j ∈ Finset.range (N + 1), DFB.d I.L lam j) / ((N : ℝ) + 1) :=
  DFB.terminal_eval I.L lam N

theorem text_F_DFB_response (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (s : Fin N) (lam : ℝ) (hlam : lam ∈ Set.Icc I.mu I.L) :
    ((DFB.history I.L N).response s).eval lam =
      -(1 - DFB.d I.L lam (N - s.val)) / (lam * ((N : ℝ) + 1)) := by
  exact DFB.response_eval I.L lam (ne_of_gt (I.mu_pos.trans I.mu_lt_L))
    (ne_of_gt (I.mu_pos.trans_le hlam.1)) N s
end

section
/-! ## Appendix F, p. 25 (Prefix with tail averaging)
The output is the arithmetic mean from K=ceil(N/2) through N on one actual
Prefix trajectory. The same weights average the terminal polynomials and
physical responses, with each shorter response extended by zero. -/
open InexactRealizations.Prose.Tail
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
theorem text_F_tail_output (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ)
    (initial : E) (oracle : Fin N → E → E) :
    (history I N).oracleOutput initial oracle =
      ((indices N).card : ℝ)⁻¹ • ∑ j ∈ indices N,
        if hj : j.val < N then (InexactRealizations.Classical.history I N).oracleQuery initial oracle ⟨j.val, hj⟩
        else (InexactRealizations.Classical.history I N).oracleOutput initial oracle :=
  actual_tail_mean I N initial oracle

theorem text_F_tail_terminal (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    (history I N).terminal = ∑ j : Fin (N + 1), weights N j • I.residual j.val :=
  terminal I N

theorem text_F_tail_response (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (s : Fin N) :
    (history I N).response s = ∑ j : Fin (N + 1), weights N j • extendedResponse I j.val s :=
  response I N s
end

section
/-! ## Appendix F, p. 25 (the exact covariance-trace prediction)
The formula is for the actual stochastic execution of an arbitrary history,
with its own terminal polynomial. The raw conditional model derives the
integrability needed by the covariance calculation. Its conclusion holds
under conditional centering, which includes the printed independent errors. -/
variable {N : ℕ} {Ω J : Type*} [Fintype J] [DecidableEq J]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → EuclideanSpace ℝ J}
theorem text_F_covariance_prediction (h : InexactRealizations.History N) (H : Matrix J J ℝ)
    (initial : EuclideanSpace ℝ J) (σ : ℝ)
    (hw : InexactRealizations.Prose.RawAdditiveLaw N 𝓕 w μ σ)
    (Γ : Matrix J J ℝ) (hΓ : ∀ s : Fin N, InexactRealizations.Probability.covarianceMatrix (w s.val) μ = Γ) :
    (∫ ω, ‖h.stochasticOutput (InexactRealizations.History.matrixEnd H) initial w ω‖ ^ 2 ∂μ) =
      ‖(aeval (InexactRealizations.History.matrixEnd H) h.terminal) initial‖ ^ 2 +
        ∑ s : Fin N, Matrix.trace
          (aeval H (h.response s) * Γ * (aeval H (h.response s)).transpose) :=
  h.integral_stochasticOutput_common_covariance H initial hw.martingale Γ hΓ
end

section
/-! ## Appendix F, p. 25 (the subtractive-dither law at every input)
The nearest-integer quantizer is the literal h(round(g/h+chi)-chi).
`Dither.law` is uniform on [-1/2,1/2]; its half-open representation differs
on a null endpoint only. The actual error is a scaled measure-preserving
rotation of that law, giving its exact variance h^2/12 for every input. -/
open InexactRealizations.Probability.Dither
theorem text_F_quantizer_error (h g χ : ℝ) (hh : h ≠ 0) :
    h * ((round (g / h + χ) : ℝ) - χ) - g = h * normalizedError (g / h) χ :=
  quantizer_error h g χ hh

theorem text_F_quantizer_uniform_law (h g : ℝ) (hh : h ≠ 0) :
    Measure.map (fun χ ↦ quantizer h g χ - g) law =
      Measure.map (fun v : ℝ ↦ h * v) law := by
  have he : (fun χ ↦ quantizer h g χ - g) = (fun v : ℝ ↦ h * v) ∘ normalizedError (g / h) :=
    funext (fun χ ↦ quantizer_error h g χ hh)
  rw [he, ← Measure.map_map (by fun_prop) (normalizedError_preserving (g / h)).measurable,
    (normalizedError_preserving (g / h)).map_eq]

theorem text_F_quantizer_unbiased (h g : ℝ) (hh : h ≠ 0) :
    (∫ χ, quantizer h g χ - g ∂law) = 0 := quantizer_unbiased h g hh

theorem text_F_quantizer_variance (h g : ℝ) (hh : h ≠ 0) :
    (∫ χ, (quantizer h g χ - g) ^ 2 ∂law) = h ^ 2 / 12 :=
  quantizer_variance h g hh
end

section
/-! ## Appendix F, p. 25 (the actual worker-averaged quantizer covariance)
`quantizedStream` is constructed from one finite independent worker/component
product tape over all actual calls. It is not an assumed covariance stream.
The formula gives the printed four-worker covariance after substituting the
quantizer step. The positive quantizer step is encoded by h nonzero. -/
open InexactRealizations.Probability InexactRealizations.Probability.Dither
variable {N m : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
omit [DecidableEq J] in
theorem text_F_quantized_worker_centered (R : InexactRealizations.History N)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (hh : h ≠ 0) (initial : EuclideanSpace ℝ J) (s : Fin N) :
    (Temporal.law N m)[quantizedStream R H c h initial s.val | Temporal.past N m s.val] =ᵐ[Temporal.law N m]
      (0 : Temporal.Tape N m J → EuclideanSpace ℝ J) :=
  (quantizedStream_martingale R H c h hh initial).centered s.val s.isLt

theorem text_F_quantized_worker_conditional_covariance (R : InexactRealizations.History N) (hm : 0 < m)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (hh : h ≠ 0) (initial : EuclideanSpace ℝ J) (s : Fin N) (j k : J) :
    (Temporal.law N m)[(fun ω ↦ quantizedStream R H c h initial s.val ω j *
      quantizedStream R H c h initial s.val ω k) | Temporal.past N m s.val] =ᵐ[Temporal.law N m]
      fun _ ↦ if j = k then h ^ 2 / (12 * (m : ℝ)) else 0 := by
  simp only [quantizedStream, Temporal.stream_at_fin]
  exact Temporal.error_conditional_cross _ (quantizedGradient_measurable R H c h hh initial) hm h hh s j k

theorem text_F_quantized_worker_covariance (R : InexactRealizations.History N) (hm : 0 < m)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (hh : h ≠ 0) (initial : EuclideanSpace ℝ J) (s : Fin N) :
    covarianceMatrix (quantizedStream R H c h initial s.val) (Temporal.law N m) =
      (h ^ 2 / (12 * (m : ℝ))) • (1 : Matrix J J ℝ) :=
  quantizedStream_covariance R hm H c h hh initial s

theorem text_F_four_worker_covariance (R : InexactRealizations.History N)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)
    (c : Fin 4 → EuclideanSpace ℝ J) (σ : ℝ) (hσ : 0 < σ)
    (initial : EuclideanSpace ℝ J) (s : Fin N) :
    covarianceMatrix (quantizedStream R H c (Real.sqrt 3 / 2 * σ) initial s.val)
      (Temporal.law N 4) = (σ ^ 2 / 64) • (1 : Matrix J J ℝ) := by
  have hh : Real.sqrt 3 / 2 * σ ≠ 0 := by positivity
  rw [quantizedStream_covariance R (by omega : 0 < 4) H c _ hh initial s]
  congr 1
  simp only [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num
  ring

theorem text_F_quantized_worker_mse (R : InexactRealizations.History N) (hm : 0 < m)
    (M : Matrix J J ℝ) (c : Fin m → EuclideanSpace ℝ J) (h : ℝ) (hh : h ≠ 0)
    (initial xstar : EuclideanSpace ℝ J)
    (hc : (m : ℝ)⁻¹ • (∑ i, c i) = InexactRealizations.History.matrixEnd M xstar) :
    (∫ ω, ‖quantizedOutput R (InexactRealizations.History.matrixEnd M) c h initial ω - xstar‖ ^ 2
      ∂Temporal.law N m) =
      ‖(aeval (InexactRealizations.History.matrixEnd M) R.terminal) (initial - xstar)‖ ^ 2 +
        ∑ s : Fin N, Matrix.trace
          (aeval M (R.response s) * ((h ^ 2 / (12 * (m : ℝ))) • (1 : Matrix J J ℝ)) *
            (aeval M (R.response s)).transpose) :=
  integral_quantizedOutput_covariance R hm M c h hh initial xstar hc
end


section StrictGap3

open MeasureTheory Polynomial
open scoped BigOperators ENNReal

section
/-! ## Appendix F, p. 25 (covariance of an actually rounded product)
The scalar primitive channels are ordered first by input component and then by
arithmetic component. Their conditional means vanish given all previous
roundings and the query's past. This implies every distinct-channel cross
moment vanishes; no combined covariance or cross-covariance certificate is an
input. Finiteness of each primitive second moment derives square integrability.
The input and arithmetic variances below are their actual scalar second moments.
-/
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

structure ScalarRoundingLaw (n : ℕ) (𝓕 : Filtration ℕ mΩ) (w : ℕ → Ω → ℝ) : Prop where
  adapted : ∀ s, s < n → StronglyMeasurable[𝓕 (s + 1)] (w s)
  centered : ∀ s, s < n → μ[w s | 𝓕 s] =ᵐ[μ] 0
  finiteSecondMoment : ∀ s, s < n → (∫⁻ ω, ENNReal.ofReal ((w s ω) ^ 2) ∂μ) < ∞

omit [IsProbabilityMeasure μ] in
private theorem auxG3_memLp {n : ℕ} {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → ℝ}
    (hw : ScalarRoundingLaw (μ := μ) n 𝓕 w) (s : ℕ) (hs : s < n) : MemLp (w s) 2 μ := by
  have hm : AEStronglyMeasurable (w s) μ := ((hw.adapted s hs).mono (𝓕.le (s + 1))).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  refine ⟨hm.norm.pow 2, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω ↦ sq_nonneg ‖w s ω‖)).mpr
  simpa only [Real.norm_eq_abs, sq_abs] using hw.finiteSecondMoment s hs

omit [IsProbabilityMeasure μ] in
private theorem auxG3_martingale {n : ℕ} {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → ℝ}
    (hw : ScalarRoundingLaw (μ := μ) n 𝓕 w) :
    InexactRealizations.Probability.MartingaleDifferences n 𝓕 w μ :=
  ⟨hw.adapted, auxG3_memLp hw, hw.centered⟩

def scalarRoundingVariance (w : ℕ → Ω → ℝ) (s : ℕ) : ℝ := ∫ ω, (w s ω) ^ 2 ∂μ

theorem text_F_rounding_primitive_cross {n : ℕ} {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → ℝ}
    (hw : ScalarRoundingLaw (μ := μ) n 𝓕 w) (s t : Fin n) :
    (∫ ω, w s.val ω * w t.val ω ∂μ) =
      if s = t then scalarRoundingVariance (μ := μ) w s.val else 0 := by
  by_cases he : s = t
  · subst t
    simp only [ite_true, scalarRoundingVariance, pow_two]
  · simp only [he, ite_false]
    rcases lt_or_gt_of_ne (show s.val ≠ t.val from fun h ↦ he (Fin.ext h)) with hlt | hgt
    · simpa only [Real.inner_apply, conj_trivial, mul_comm] using
        (auxG3_martingale hw).integral_inner_eq_zero s.val t.val s.isLt t.isLt hlt
    · simpa only [Real.inner_apply, conj_trivial, mul_comm] using
        (auxG3_martingale hw).integral_inner_eq_zero t.val s.val t.isLt s.isLt hgt

private def auxG3_transform {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (w : ℕ → Ω → ℝ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j ↦ ∑ s : Fin n, A j s * w s.val ω)

omit [IsProbabilityMeasure μ] in
private theorem auxG3_transform_memLp {n d : ℕ} {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → ℝ}
    (hw : ScalarRoundingLaw (μ := μ) n 𝓕 w) (A : Matrix (Fin d) (Fin n) ℝ) :
    MemLp (auxG3_transform A w) 2 μ := by
  apply memLp_piLp_iff.mpr
  intro j
  change MemLp (fun ω ↦ ∑ s : Fin n, A j s * w s.val ω) 2 μ
  exact memLp_finsetSum _ (fun s _ ↦ (auxG3_memLp hw s.val s.isLt).const_mul (A j s))

private theorem auxG3_transform_mean {n d : ℕ} {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → ℝ}
    (hw : ScalarRoundingLaw (μ := μ) n 𝓕 w) (A : Matrix (Fin d) (Fin n) ℝ) :
    (∫ ω, auxG3_transform A w ω ∂μ) = 0 := by
  ext j
  rw [eval_integral_piLp (fun i ↦ ((auxG3_transform_memLp hw A).eval_piLp i).integrable (by norm_num))]
  change (∫ ω, ∑ s : Fin n, A j s * w s.val ω ∂μ) = 0
  rw [integral_finsetSum _ (fun s _ ↦ ((auxG3_memLp hw s.val s.isLt).integrable (by norm_num)).const_mul _)]
  simp only [integral_const_mul]
  apply Finset.sum_eq_zero
  intro s _
  rw [(auxG3_martingale hw).integral_eq_zero s.val s.isLt, mul_zero]

private theorem auxG3_transform_covariance {n d : ℕ} {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → ℝ}
    (hw : ScalarRoundingLaw (μ := μ) n 𝓕 w) (A : Matrix (Fin d) (Fin n) ℝ) :
    InexactRealizations.Probability.covarianceMatrix (auxG3_transform A w) μ =
      A * Matrix.diagonal (fun s : Fin n ↦ scalarRoundingVariance (μ := μ) w s.val) * A.transpose := by
  rw [InexactRealizations.Probability.covarianceMatrix_of_mean_zero _ (auxG3_transform_mean hw A)]
  ext i j
  change (∫ ω, (∑ s : Fin n, A i s * w s.val ω) * (∑ t : Fin n, A j t * w t.val ω) ∂μ) = _
  have hprod (s t : Fin n) : Integrable (fun ω ↦ (A i s * A j t) * (w s.val ω * w t.val ω)) μ :=
    ((auxG3_memLp hw s.val s.isLt).integrable_mul (auxG3_memLp hw t.val t.isLt)).const_mul _
  calc
    _ = ∫ ω, ∑ s : Fin n, ∑ t : Fin n, (A i s * A j t) * (w s.val ω * w t.val ω) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ by
        change (∑ s : Fin n, A i s * w s.val ω) * (∑ t : Fin n, A j t * w t.val ω) =
          ∑ s : Fin n, ∑ t : Fin n, (A i s * A j t) * (w s.val ω * w t.val ω)
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro t _
        ring
    _ = ∑ s : Fin n, ∑ t : Fin n, (A i s * A j t) * (∫ ω, w s.val ω * w t.val ω ∂μ) := by
      rw [integral_finsetSum _ (fun s _ ↦ integrable_finsetSum _ (fun t _ ↦ hprod s t))]
      apply Finset.sum_congr rfl
      intro s _
      rw [integral_finsetSum _ (fun t _ ↦ hprod s t)]
      simp only [integral_const_mul]
    _ = ∑ s : Fin n, (A i s * A j s) * scalarRoundingVariance (μ := μ) w s.val := by
      simp [text_F_rounding_primitive_cross hw]
    _ = _ := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
      apply Finset.sum_congr rfl
      intro s _
      ring

variable {d : ℕ}

def roundingInputError (w : ℕ → Ω → ℝ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j ↦ w j.val ω)

def roundingArithmeticError (w : ℕ → Ω → ℝ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j ↦ w (d + j.val) ω)

def roundingProductError (H : Matrix (Fin d) (Fin d) ℝ) (w : ℕ → Ω → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  InexactRealizations.Probability.matrixApply H (roundingInputError w ω) + roundingArithmeticError w ω

def roundingInputVariance (w : ℕ → Ω → ℝ) (j : Fin d) : ℝ :=
  scalarRoundingVariance (μ := μ) w j.val

def roundingArithmeticVariance (w : ℕ → Ω → ℝ) (j : Fin d) : ℝ :=
  scalarRoundingVariance (μ := μ) w (d + j.val)

private def auxG3_matrix (H : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin (d + d)) ℝ :=
  fun i s ↦ Fin.addCases (fun j ↦ H i j) (fun j ↦ if i = j then 1 else 0) s

omit mΩ in
private theorem auxG3_product_eq_transform (H : Matrix (Fin d) (Fin d) ℝ)
    (w : ℕ → Ω → ℝ) : roundingProductError H w = auxG3_transform (auxG3_matrix H) w := by
  funext ω
  ext j
  simp only [roundingProductError, PiLp.add_apply, InexactRealizations.Probability.matrixApply_coordinate,
    roundingInputError, roundingArithmeticError, PiLp.toLp_apply, auxG3_transform,
    auxG3_matrix, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
    Fin.val_castAdd, Fin.val_natAdd, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

omit mΩ in
theorem text_F_rounded_product_error (H : Matrix (Fin d) (Fin d) ℝ)
    (y : EuclideanSpace ℝ (Fin d)) (w : ℕ → Ω → ℝ) (ω : Ω) :
    InexactRealizations.Probability.matrixApply H (y + roundingInputError w ω) + roundingArithmeticError w ω -
      InexactRealizations.Probability.matrixApply H y = roundingProductError H w ω := by
  ext j
  simp only [InexactRealizations.Probability.matrixApply_coordinate, PiLp.add_apply, PiLp.sub_apply,
    roundingProductError, mul_add, Finset.sum_add_distrib]
  ring

theorem text_F_input_arithmetic_rounding_cross {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → ℝ}
    (hw : ScalarRoundingLaw (μ := μ) (d + d) 𝓕 w) (i j : Fin d) :
    (∫ ω, roundingInputError w ω i * roundingArithmeticError w ω j ∂μ) = 0 := by
  let s : Fin (d + d) := ⟨i.val, by omega⟩
  let t : Fin (d + d) := ⟨d + j.val, by omega⟩
  have he : s ≠ t := by intro h; have hh := congrArg Fin.val h; dsimp only [s, t] at hh; omega
  simpa only [roundingInputError, roundingArithmeticError, PiLp.toLp_apply, s, t, he, ite_false]
    using text_F_rounding_primitive_cross hw s t

theorem text_F_rounded_product_covariance {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → ℝ}
    (hw : ScalarRoundingLaw (μ := μ) (d + d) 𝓕 w) (H : Matrix (Fin d) (Fin d) ℝ) :
    InexactRealizations.Probability.covarianceMatrix (roundingProductError H w) μ =
      H * Matrix.diagonal (roundingInputVariance (μ := μ) w) * H.transpose +
        Matrix.diagonal (roundingArithmeticVariance (μ := μ) w) := by
  rw [auxG3_product_eq_transform, auxG3_transform_covariance hw]
  ext i j
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  rw [Fin.sum_univ_add]
  simp only [auxG3_matrix, Fin.addCases_left, Fin.addCases_right,
    Fin.val_castAdd, Fin.val_natAdd, roundingInputVariance]
  congr 1
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal, roundingArithmeticVariance]
  · simp [Matrix.diagonal, roundingArithmeticVariance, hij]

theorem text_F_symmetric_rounded_product_covariance {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → ℝ}
    (hw : ScalarRoundingLaw (μ := μ) (d + d) 𝓕 w) (H : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.IsSymm) :
    InexactRealizations.Probability.covarianceMatrix (roundingProductError H w) μ =
      H * Matrix.diagonal (roundingInputVariance (μ := μ) w) * H +
        Matrix.diagonal (roundingArithmeticVariance (μ := μ) w) := by
  rw [text_F_rounded_product_covariance hw H, hH.eq]

theorem text_F_query_rounding_covariance (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.IsSymm)
    (y : EuclideanSpace ℝ (Fin d)) (ε : EuclideanSpace ℝ (Fin d) → ℕ → Ω → ℝ)
    (𝓕 : Filtration ℕ mΩ) (hε : ScalarRoundingLaw (μ := μ) (d + d) 𝓕 (ε y)) :
    InexactRealizations.Probability.covarianceMatrix
      (fun ω ↦ InexactRealizations.Probability.matrixApply H (y + roundingInputError (ε y) ω) +
        roundingArithmeticError (ε y) ω - InexactRealizations.Probability.matrixApply H y) μ =
      H * Matrix.diagonal (roundingInputVariance (μ := μ) (ε y)) * H +
        Matrix.diagonal (roundingArithmeticVariance (μ := μ) (ε y)) := by
  have he : (fun ω ↦ InexactRealizations.Probability.matrixApply H (y + roundingInputError (ε y) ω) +
      roundingArithmeticError (ε y) ω - InexactRealizations.Probability.matrixApply H y) =
      roundingProductError H (ε y) := funext (text_F_rounded_product_error H y (ε y))
  rw [he]
  exact text_F_symmetric_rounded_product_covariance hε H hH

end
end StrictGap3

section
/-! ## Appendix F, p. 25 (the differentiated channel signal)
`signalMatrix h lam a` has the literal entries a_j Phi_s(lam_j) pi_s(lam_j).
The operator is constructed from that matrix, and the supremum on the unit
sphere is attained. No derivative, eigenbasis or maximizing vector is assumed.
The concrete cycle eigenbasis and its physical transport are stated below. -/
open InexactRealizations.Channel
variable {N : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
omit [Fintype J] [DecidableEq J] in
theorem text_F_signal_entries (h : InexactRealizations.History N) (lam a : J → ℝ) (j : J) (s : Fin N) :
    signalMatrix h lam a j s =
      a j * ((h.response s).eval (lam j) * (h.query s).eval (lam j)) := rfl

theorem text_F_channel_derivative (h : InexactRealizations.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) (e : EuclideanSpace ℝ (Fin N)) :
    HasDerivAt (fun t ↦ h.oracleOutput a
      (InexactRealizations.History.perturbedOracle (InexactRealizations.History.matrixEnd (Matrix.diagonal lam))
        (fun s ↦ e s • (LinearMap.id : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)) t))
      (signalOperator h lam a.ofLp e) 0 :=
  hasDerivAt_signal_output h lam a e

omit [DecidableEq J] in
theorem text_F_channel_sharp_gain (h : InexactRealizations.History N) (hN : 0 < N) (lam a : J → ℝ) :
    (∀ e : EuclideanSpace ℝ (Fin N), ‖e‖ ≤ 1 →
      ‖signalOperator h lam a e‖ ≤ ‖signalOperator h lam a‖) ∧
      ∃ e : EuclideanSpace ℝ (Fin N), ‖e‖ = 1 ∧
        ‖signalOperator h lam a e‖ = ‖signalOperator h lam a‖ :=
  signalOperator_sharp h hN lam a
end

section
/-! ## Appendix F, pp. 25–26 (the full finite-sign expansion and its variance)
The coefficients are the concrete finite insertion coefficients of the actual
oracle output; they are not supplied as an input. The Boolean product law is
one independent fair sign per call. The empty and singleton coefficients are
identified with the nominal output and the columns of the actual signal matrix.
The remainder is an explicit nonnegative finite sum and is O(delta^4) at fixed
horizon. All formulas below use the identity channel in spectral coordinates. -/
open InexactRealizations.Channel
variable {N : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
theorem text_F_full_sign_expansion (h : InexactRealizations.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) (δ : ℝ) (ω : Fin N → Bool) :
    finiteSignOutput h (InexactRealizations.History.matrixEnd (Matrix.diagonal lam))
      (fun _ ↦ LinearMap.id) a δ ω =
      ∑ S ∈ (Finset.range N).powerset, InexactRealizations.Probability.SignProducts.characterNat N S ω •
        (δ ^ S.card • finiteNoiseCoefficient h (InexactRealizations.History.matrixEnd (Matrix.diagonal lam))
          (fun _ ↦ LinearMap.id) a S) :=
  finiteSignOutput_expansion h _ _ a δ ω

theorem text_F_full_sign_empty (h : InexactRealizations.History N) (lam : J → ℝ) (a : EuclideanSpace ℝ J) :
    finiteNoiseCoefficient h (InexactRealizations.History.matrixEnd (Matrix.diagonal lam))
      (fun _ ↦ LinearMap.id) a ∅ =
      (aeval (InexactRealizations.History.matrixEnd (Matrix.diagonal lam)) h.terminal) a :=
  finiteNoiseCoefficient_empty h _ _ a

theorem text_F_full_sign_singleton (h : InexactRealizations.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) (s : Fin N) (j : J) :
    finiteNoiseCoefficient h (InexactRealizations.History.matrixEnd (Matrix.diagonal lam))
      (fun _ ↦ LinearMap.id) a {s.val} j = signalMatrix h lam a.ofLp j s :=
  finiteNoiseCoefficient_signal_column h lam a s j

theorem text_F_sign_products_orthogonal (S T : Finset ℕ)
    (hS : S ⊆ Finset.range N) (hT : T ⊆ Finset.range N) :
    (∫ ω, InexactRealizations.Probability.SignProducts.characterNat N S ω *
      InexactRealizations.Probability.SignProducts.characterNat N T ω ∂InexactRealizations.Probability.Signs.law N) =
      if S = T then 1 else 0 :=
  InexactRealizations.Probability.SignProducts.integral_characterNat_mul S T hS hT

theorem text_F_full_sign_mean (h : InexactRealizations.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) (δ : ℝ) :
    (∫ ω, finiteSignOutput h (InexactRealizations.History.matrixEnd (Matrix.diagonal lam))
      (fun _ ↦ LinearMap.id) a δ ω ∂InexactRealizations.Probability.Signs.law N) =
      (aeval (InexactRealizations.History.matrixEnd (Matrix.diagonal lam)) h.terminal) a :=
  finiteSignOutput_mean h _ _ a δ

theorem text_F_full_sign_variance (h : InexactRealizations.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) (δ : ℝ) :
    (∫ ω, ‖finiteSignOutput h (InexactRealizations.History.matrixEnd (Matrix.diagonal lam))
      (fun _ ↦ LinearMap.id) a δ ω -
      (aeval (InexactRealizations.History.matrixEnd (Matrix.diagonal lam)) h.terminal) a‖ ^ 2
        ∂InexactRealizations.Probability.Signs.law N) =
      ∑ S ∈ (Finset.range N).powerset.erase ∅,
        δ ^ (2 * S.card) * ‖finiteNoiseCoefficient h (InexactRealizations.History.matrixEnd (Matrix.diagonal lam))
          (fun _ ↦ LinearMap.id) a S‖ ^ 2 :=
  finiteSignOutput_variance h _ _ a δ

theorem text_F_full_sign_variance_leading (h : InexactRealizations.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) (δ : ℝ) :
    (∫ ω, ‖finiteSignOutput h (InexactRealizations.History.matrixEnd (Matrix.diagonal lam))
      (fun _ ↦ LinearMap.id) a δ ω -
      (aeval (InexactRealizations.History.matrixEnd (Matrix.diagonal lam)) h.terminal) a‖ ^ 2
        ∂InexactRealizations.Probability.Signs.law N) =
      δ ^ 2 * (∑ j, ∑ s, (signalMatrix h lam a.ofLp j s) ^ 2) +
        finiteNoiseRemainder h (InexactRealizations.History.matrixEnd (Matrix.diagonal lam))
          (fun _ ↦ LinearMap.id) a δ :=
  finiteSignOutput_signal_variance h lam a δ

theorem text_F_full_sign_remainder_nonnegative (h : InexactRealizations.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) (δ : ℝ) :
    0 ≤ finiteNoiseRemainder h (InexactRealizations.History.matrixEnd (Matrix.diagonal lam))
      (fun _ ↦ LinearMap.id) a δ := finiteNoiseRemainder_nonneg h _ _ a δ

theorem text_F_full_sign_remainder_order (h : InexactRealizations.History N) (lam : J → ℝ)
    (a : EuclideanSpace ℝ J) :
    (fun δ ↦ finiteNoiseRemainder h (InexactRealizations.History.matrixEnd (Matrix.diagonal lam))
      (fun _ ↦ LinearMap.id) a δ) =O[𝓝 (0 : ℝ)] (fun δ ↦ δ ^ 4) :=
  (finiteNoiseRemainder_isBigO h _ (fun _ ↦ LinearMap.id) a).isBigO
end

section
/-! ## Appendix F, pp. 25–26 (the actual cycle spectral coordinates)
The real orthonormal eigenbasis is constructed from the actual cycle operator.
The integer m generalizes the article's cycle of size16; NeZero m records its
nonempty dimension. The active spectral values are those of the physical
coupled network, not an assumed diagonalization. -/
open InexactRealizations.Models.Network
variable (m : ℕ) [NeZero m]
theorem text_F_cycle_diagonalization (u : EuclideanSpace ℝ (ZMod m)) (j : Fin m) :
    (realEigenbasis m).repr (cycleOperator m u) j =
      realEigenvalue m j * (realEigenbasis m).repr u j :=
  realEigenbasis_diagonalization m u j

theorem text_F_cycle_cosine_spectrum (j : Fin m) :
    ∃ k : ZMod m, realEigenvalue m j = 2 - 2 * Real.cos (2 * Real.pi * k.val / m) :=
  realEigenvalue_cosine m j

theorem text_F_cycle_active_value (κ : ℝ) (hκ : 1 < κ) (j : Fin m) :
    activeSpectralValue m κ j = (4 + (κ - 1) * realEigenvalue m j) / (4 * κ) := by
  have hk : κ ≠ 0 := by linarith
  have hm : κ - 1 ≠ 0 := by linarith
  have hd : 4 + 2 * (2 / (κ - 1)) = 4 * κ / (κ - 1) := by
    field_simp
    ring
  unfold activeSpectralValue
  rw [hd]
  field_simp
  ring

variable {N : ℕ}
theorem text_F_cycle_physical_transport (h : InexactRealizations.History N) (κ δ : ℝ)
    (ξ : Fin N → ℝ) (initial : EuclideanSpace ℝ (Fin m)) :
    h.oracleOutput (activeEmbedding ((realEigenbasis m).repr.symm initial))
      (ambientOracle (cycleLaplacian m) (2 / (κ - 1)) δ ξ) =
      activeEmbedding ((realEigenbasis m).repr.symm
        (h.oracleOutput initial (InexactRealizations.Channel.Roots.euclideanOracle (activeSpectralValue m κ) δ ξ))) :=
  cycle_network_output_spectral m h κ δ ξ initial

theorem text_F_cycle_physical_derivative (h : InexactRealizations.History N) (κ : ℝ)
    (initial : EuclideanSpace ℝ (Fin m)) (e : EuclideanSpace ℝ (Fin N)) :
    HasDerivAt (fun t ↦ h.oracleOutput
      (activeEmbedding ((realEigenbasis m).repr.symm initial))
      (ambientOracle (cycleLaplacian m) (2 / (κ - 1)) t (fun s ↦ e s)))
      (activeEmbedding ((realEigenbasis m).repr.symm
        (InexactRealizations.Channel.signalOperator h (activeSpectralValue m κ) initial.ofLp e))) 0 :=
  cycle_network_hasDerivAt m h κ initial e

theorem text_F_cycle_derivative_norm (h : InexactRealizations.History N) (κ : ℝ)
    (initial : EuclideanSpace ℝ (Fin m)) (e : EuclideanSpace ℝ (Fin N)) :
    ‖activeEmbedding ((realEigenbasis m).repr.symm
      (InexactRealizations.Channel.signalOperator h (activeSpectralValue m κ) initial.ofLp e))‖ =
      ‖InexactRealizations.Channel.signalOperator h (activeSpectralValue m κ) initial.ofLp e‖ :=
  cycle_network_derivative_norm m h κ initial e
end

end Part3

end
end Article
