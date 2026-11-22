import InexactRealizations.Risk.TwoModeWitness
import InexactRealizations.Risk.RelaxedFlat
import InexactRealizations.Properties.Minimax

/-! Every unrestricted causal linear history has the lower risk in current
Theorem3.2. The proof uses its actual response-sum identity, polynomial
minimax theorem and a single physical two-mode martingale model. 
-/
namespace InexactRealizations.Risk.AllLinear
noncomputable section
open Polynomial Set
open scoped BigOperators
variable {N : ℕ}

theorem response_energy_lower (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (hN : 0 < N) (σ : ℝ) :
    (σ ^ 2 / (I.mu ^ 2 * N)) * (1 - h.terminal.eval I.mu) ^ 2 ≤
      σ ^ 2 * ∑ s, (h.response s).eval I.mu ^ 2 := by
  have ht := congrArg (fun p : ℝ[X] ↦ p.eval I.mu) h.terminal_eq_one_add_X_sum_response
  simp only [eval_add, eval_one, eval_mul, eval_X, eval_finsetSum] at ht
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
    (fun _ ↦ (1 : ℝ)) (fun s ↦ (h.response s).eval I.mu)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hc
  have hid : (1 - h.terminal.eval I.mu) ^ 2 = I.mu ^ 2 * (∑ s, (h.response s).eval I.mu) ^ 2 := by
    rw [ht]
    ring
  rw [div_mul_eq_mul_div, hid]
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos I.mu_pos) (by exact_mod_cast hN : (0 : ℝ) < N))).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hc (mul_nonneg (sq_nonneg σ) (sq_nonneg I.mu))]

theorem allMseBound_lower (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (hN : 2 ≤ N) {r σ C : ℝ} (hr : 0 ≤ r) (hb : InexactRealizations.Risk.MseBound h I r σ C) :
    value (r ^ 2) (σ ^ 2 / (I.mu ^ 2 * N)) (I.epsilon N) ≤ C := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr I.mu_lt_L.le)
    h.terminal.continuous.abs.continuousOn
  have hdegree : h.terminal.degree ≤ (N : WithBot ℕ) :=
    degree_le_natDegree.trans (by exact_mod_cast h.terminal_natDegree_le)
  have he := epsilon_unit I (by omega : 0 < N)
  have heM := InexactRealizations.Properties.terminal_minimax_lower I N h.terminal hdegree h.terminal_eval_zero
    |h.terminal.eval x| (fun y hy ↦ hmax hy)
  have hcM := hmax (show I.mu ∈ Icc I.mu I.L from ⟨le_rfl, I.mu_lt_L.le⟩)
  have hM : max (I.epsilon N) |h.terminal.eval I.mu| ≤ |h.terminal.eval x| := max_le heM hcM
  have hsignal : r ^ 2 * (max (I.epsilon N) |h.terminal.eval I.mu|) ^ 2 ≤ r ^ 2 * h.terminal.eval x ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ ((abs_nonneg _).trans (le_max_right _ _)) (abs_nonneg _)).mpr hM) (sq_nonneg r)
    simpa only [sq_abs] using hh
  have hnoise := response_energy_lower h I (by omega) σ
  have htwo := mseBound_twoMode_lower h I hr hb hx
  have hscalar := clipped_value_lower (sq_nonneg r) (by positivity : 0 ≤ σ ^ 2 / (I.mu ^ 2 * N))
    he.1 he.2 (h.terminal.eval I.mu)
  exact hscalar.trans ((add_le_add hsignal hnoise).trans htwo)

end
end InexactRealizations.Risk.AllLinear
