import InexactRealizations.Accuracy.Operations.Reference

/-! Reference-operand versions of the compensated average and Prefix
estimates. The correction bound is later supplied by the actual run. 
-/
namespace InexactRealizations.Accuracy
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem CompensatedStep.reference_error {x b c x0 b0 : E} {prepared u phi eps K S Kcorr : ℝ}
    (v : CompensatedStep x b c phi prepared u) (hu : 0 ≤ u) (hu1 : u ≤ 1) (hue : u ≤ eps)
    (hphi : 0 ≤ phi) (hphi1 : phi ≤ 1) (hp : |prepared - phi| ≤ u * phi)
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hKcorr : 0 ≤ Kcorr)
    (hx : ‖x - x0‖ ≤ eps * K) (hb : ‖(b + c) - b0‖ ≤ eps * K)
    (hxs : ‖x‖ ≤ S) (hbs : ‖b‖ ≤ S) (hcs : ‖c‖ ≤ S) (hcorr : ‖c‖ ≤ u * Kcorr) :
    ‖v.total - ((b + c) + phi • (x - (b + c)))‖ ≤
      6 * u * phi * ‖x0 - b0‖ + eps ^ 2 * (12 * K + 800 * S + 200 * Kcorr) := by
  have heps : 0 ≤ eps := hu.trans hue
  have hD := distance_from_distances hx hb
  have hlead : phi * ‖x - (b + c)‖ ≤ phi * ‖x0 - b0‖ + 2 * eps * K := by
    nlinarith [mul_le_mul_of_nonneg_left hD hphi,
      mul_le_mul_of_nonneg_right hphi1 (mul_nonneg heps hK)]
  have hdsize : ‖x - (b + c)‖ ≤ 3 * S :=
    (norm_sub_le _ _).trans (by linarith [norm_add_le b c])
  have hsize : ‖x - (b + c)‖ + Kcorr + ‖b‖ ≤ 4 * S + Kcorr := by linarith
  have hh := v.average_error hu hu1 hphi hphi1 hp hKcorr hcorr
  have hsq : u ^ 2 ≤ eps ^ 2 := (sq_le_sq₀ hu heps).mpr hue
  have hmul : u * eps ≤ eps ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hue) heps]
  nlinarith [mul_le_mul_of_nonneg_left hlead (by positivity : 0 ≤ 6 * u),
    mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ 200 * u ^ 2),
    mul_le_mul_of_nonneg_right hsq (show 0 ≤ 4 * S + Kcorr by positivity),
    mul_le_mul_of_nonneg_right hmul hK]

set_option maxHeartbeats 2000000 in
theorem PrefixStep.reference_error {x b g x0 b0 g0 : E} {alphaHat betaHat u alpha beta eps K J S T : ℝ}
    (v : PrefixStep x b g alphaHat betaHat u)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hue : u ≤ eps) (halpha : 0 ≤ alpha)
    (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (ha : |alphaHat - alpha| ≤ u * alpha) (hb : |betaHat - beta| ≤ u * beta)
    (hK : 0 ≤ K) (hJ : 0 ≤ J) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hx : ‖x - x0‖ ≤ eps * K) (hprev : ‖b - b0‖ ≤ eps * K)
    (hgrad : alpha * ‖g - g0‖ ≤ eps * J) (hxs : ‖x‖ ≤ S) (hbs : ‖b‖ ≤ S)
    (hgs : alpha * ‖g‖ ≤ T) :
    ‖v.result - ((1 + beta) • x - beta • b - alpha • g)‖ ≤
      u * (beta * ‖x0 - b0‖ + 2 * (1 + beta) * ‖x0‖ + beta * ‖b0‖ +
        ‖(1 + beta) • x0 - beta • b0‖ + 2 * alpha * ‖g0‖ +
        ‖(1 + beta) • x0 - beta • b0 - alpha • g0‖) +
      eps ^ 2 * (13 * K + 3 * J + 200 * S + 100 * T) := by
  have heps : 0 ≤ eps := hu.trans hue
  have hX := norm_from_distance hx
  have hB := norm_from_distance hprev
  have hD := distance_from_distances hx hprev
  have hZdiff : ‖((1 + beta) • x - beta • b) - ((1 + beta) • x0 - beta • b0)‖ ≤ 3 * eps * K := by
    have he : ((1 + beta) • x - beta • b) - ((1 + beta) • x0 - beta • b0) =
        (1 + beta) • (x - x0) - beta • (b - b0) := by module
    rw [he]
    have ht := norm_sub_le ((1 + beta) • (x - x0)) (beta • (b - b0))
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hbeta, abs_of_nonneg (by positivity : 0 ≤ 1 + beta)] at ht
    nlinarith [mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 1 + beta),
      mul_le_mul_of_nonneg_left hprev hbeta, mul_le_mul_of_nonneg_right hbeta1 (mul_nonneg heps hK)]
  have hZ := norm_from_distance hZdiff
  have hG : alpha * ‖g‖ ≤ alpha * ‖g0‖ + eps * J := by
    have hh := norm_from_distance (show ‖g - g0‖ ≤ ‖g - g0‖ from le_rfl)
    nlinarith [mul_le_mul_of_nonneg_left hh halpha]
  have hQdiff : ‖((1 + beta) • x - beta • b - alpha • g) -
      ((1 + beta) • x0 - beta • b0 - alpha • g0)‖ ≤ 3 * eps * K + eps * J := by
    have he : ((1 + beta) • x - beta • b - alpha • g) -
        ((1 + beta) • x0 - beta • b0 - alpha • g0) =
      (((1 + beta) • x - beta • b) - ((1 + beta) • x0 - beta • b0)) - alpha • (g - g0) := by module
    rw [he]
    have ht := norm_sub_le (((1 + beta) • x - beta • b) - ((1 + beta) • x0 - beta • b0)) (alpha • (g - g0))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg halpha] at ht
    linarith
  have hQ := norm_from_distance hQdiff
  have hlead : beta * ‖x - b‖ + 2 * (1 + beta) * ‖x‖ + beta * ‖b‖ +
      ‖(1 + beta) • x - beta • b‖ + 2 * alpha * ‖g‖ +
      ‖(1 + beta) • x - beta • b - alpha • g‖ ≤
      beta * ‖x0 - b0‖ + 2 * (1 + beta) * ‖x0‖ + beta * ‖b0‖ +
      ‖(1 + beta) • x0 - beta • b0‖ + 2 * alpha * ‖g0‖ +
      ‖(1 + beta) • x0 - beta • b0 - alpha • g0‖ + 13 * eps * K + 3 * eps * J := by
    nlinarith [mul_le_mul_of_nonneg_left hD hbeta,
      mul_le_mul_of_nonneg_left hX (by positivity : 0 ≤ 2 * (1 + beta)),
      mul_le_mul_of_nonneg_left hB hbeta, mul_le_mul_of_nonneg_right hbeta1 (mul_nonneg heps hK)]
  have hsize : ‖x‖ + ‖b‖ + alpha * ‖g‖ ≤ 2 * S + T := by linarith
  have hh := v.local_error hu hu1 halpha hbeta hbeta1 ha hb
  have hsq : u ^ 2 ≤ eps ^ 2 := (sq_le_sq₀ hu heps).mpr hue
  have hmul : u * eps ≤ eps ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hue) heps]
  nlinarith [mul_le_mul_of_nonneg_left hlead hu,
    mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ 100 * u ^ 2),
    mul_le_mul_of_nonneg_right hsq (show 0 ≤ 2 * S + T by positivity),
    mul_le_mul_of_nonneg_right hmul hK, mul_le_mul_of_nonneg_right hmul hJ]

end
end InexactRealizations.Accuracy
