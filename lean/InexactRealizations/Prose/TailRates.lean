import InexactRealizations.Prose.TailBounds
import InexactRealizations.Prose.GeneralMse

/-! The introduction's 1/N MSE assertion for actual Prefix tail averaging.
The radius is arbitrary nonnegative and the noise level positive; both
bounds are over the literal dimension-uniform stochastic comparison class. 
-/
namespace InexactRealizations.Prose.Tail
noncomputable section
open Polynomial Real Filter Topology
open InexactRealizations.Classical
open scoped BigOperators

theorem mse_finite_upper (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (r σ : ℝ) (hr : 0 ≤ r) : InexactRealizations.Risk.mseRisk (history I N) I r σ ≤
      4 * decay I ^ N * r ^ 2 + 4 * responseConstant I ^ 2 * σ ^ 2 / N := by
  have hq : 0 < decay I := (decay_mem I).1
  have hc := (responseConstant_pos I).le
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hP : InexactRealizations.Risk.ResponseBounds (history I N) I (fun _ ↦ 2 * responseConstant I / N) :=
    ⟨fun _ ↦ by positivity, fun s x hx ↦ response_bound_horizon I N hN s x hx⟩
  have hu := general_mse_upper (history I N) I _ hP (2 * decay I ^ start N) (by positivity)
    (fun x hx ↦ terminal_bound I N hx) r σ hr
  have hb := mul_le_mul_of_nonneg_right (terminal_sq_bound I N) (sq_nonneg r)
  have he : σ ^ 2 * (∑ _ : Fin N, (2 * responseConstant I / (N : ℝ)) ^ 2) =
      4 * responseConstant I ^ 2 * σ ^ 2 / N := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  exact hu.trans (add_le_add hb he.le)

theorem start_tendsto : Tendsto start atTop atTop := by
  apply tendsto_atTop.mpr
  intro m
  apply eventually_atTop.mpr
  refine ⟨2 * m, ?_⟩
  intro N hN
  unfold start
  omega

theorem terminal_eventually_half (I : InexactRealizations.Operators.SpectralInterval) :
    ∀ᶠ N : ℕ in atTop, (history I N).terminal.eval I.mu ≤ 1 / 2 := by
  have ht := ((tendsto_pow_atTop_nhds_zero_of_lt_one (decay_mem I).1.le (decay_mem I).2).comp start_tendsto).const_mul 2
  have hh := ht.eventually (gt_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 2))
  filter_upwards [hh] with N hN
  exact ((le_abs_self _).trans (terminal_bound I N ⟨le_rfl, I.mu_lt_L.le⟩)).trans hN.le

theorem mse_lower_of_terminal_half (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (r σ : ℝ) (hr : 0 ≤ r) (hp : (history I N).terminal.eval I.mu ≤ 1 / 2) :
    (σ ^ 2 / (4 * I.mu ^ 2)) / N ≤ InexactRealizations.Risk.mseRisk (history I N) I r σ := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hh := InexactRealizations.Risk.AllLinear.response_energy_lower (history I N) I hN σ
  have hcoef : (1 / 4 : ℝ) ≤ (1 - (history I N).terminal.eval I.mu) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hcoef (show 0 ≤ σ ^ 2 / (I.mu ^ 2 * N) by positivity)
  have he : (σ ^ 2 / (I.mu ^ 2 * N)) * (1 / 4) = (σ ^ 2 / (4 * I.mu ^ 2)) / N := by ring
  rw [he] at hm
  have hrisk := general_mse_endpoint_lower (history I N) I r σ hr
  exact (hm.trans hh).trans (by nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg ((history I N).terminal.eval I.mu))])

theorem mse_one_over_N (I : InexactRealizations.Operators.SpectralInterval) (r σ : ℝ) (hr : 0 ≤ r) (hσ : 0 < σ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      c / (N : ℝ) ≤ InexactRealizations.Risk.mseRisk (history I N) I r σ ∧
        InexactRealizations.Risk.mseRisk (history I N) I r σ ≤ C / (N : ℝ) := by
  let c := σ ^ 2 / (4 * I.mu ^ 2)
  let C := 4 * r ^ 2 + 4 * responseConstant I ^ 2 * σ ^ 2
  have hmu := I.mu_pos
  have hc : 0 < c := by dsimp only [c]; positivity
  have hC : 0 < C := by
    have hres := responseConstant_pos I
    dsimp only [C]
    positivity
  have ht := tendsto_pow_const_mul_const_pow_of_lt_one 1 (decay_mem I).1.le (decay_mem I).2
  have hh := ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  refine ⟨c, C, hc, hC, ?_⟩
  filter_upwards [terminal_eventually_half I, hh, eventually_ge_atTop (2 : ℕ)] with N hp hprod hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  refine ⟨mse_lower_of_terminal_half I N (by omega) r σ hr hp, ?_⟩
  have hu := mse_finite_upper I N (by omega) r σ hr
  have hdecay : decay I ^ N ≤ 1 / (N : ℝ) := by
    apply (le_div_iff₀ hn).mpr
    simpa only [pow_one, mul_comm] using hprod.le
  have hm := mul_le_mul_of_nonneg_right hdecay (show 0 ≤ 4 * r ^ 2 by positivity)
  apply hu.trans
  dsimp only [C]
  rw [add_div]
  apply add_le_add _ le_rfl
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_mul] using hm

end
end InexactRealizations.Prose.Tail
