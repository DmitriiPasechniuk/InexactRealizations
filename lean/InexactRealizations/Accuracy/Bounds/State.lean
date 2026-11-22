import InexactRealizations.Accuracy.Execution.Stage

/-! Weighted component bounds: gradient registers carry one factor L.
This scaling keeps all propagation constants independent of the absolute
scale of the spectral interval, as required. 
-/
namespace InexactRealizations.Accuracy.Execution
noncomputable section
variable {E : Type*} [NormedAddCommGroup E]

def weight (L : ℝ) (i : Fin 8) : ℝ := if i.val < 6 then 1 else L
def Bounded (v : State E) (L S : ℝ) : Prop := ∀ i, ‖v i‖ ≤ weight L i * S
def Close (v w : State E) (L D : ℝ) : Prop := Bounded (fun i ↦ v i - w i) L D

theorem weight_nonneg {L : ℝ} (hL : 0 ≤ L) (i : Fin 8) : 0 ≤ weight L i := by
  unfold weight
  split_ifs <;> positivity

theorem Bounded.scalar {v : State E} {L S : ℝ} (hv : Bounded v L S) (i : Fin 8) (hi : i.val < 6) :
    ‖v i‖ ≤ S := by simpa only [weight, hi, ite_true, one_mul] using hv i

theorem Bounded.gradient {v : State E} {L S : ℝ} (hv : Bounded v L S) (i : Fin 8) (hi : 6 ≤ i.val) :
    ‖v i‖ ≤ L * S := by simpa only [weight, show ¬i.val < 6 by omega, ite_false] using hv i

theorem Bounded.mono {v : State E} {L S T : ℝ} (hv : Bounded v L S) (hL : 0 ≤ L) (hST : S ≤ T) :
    Bounded v L T := fun i ↦ (hv i).trans (mul_le_mul_of_nonneg_left hST (weight_nonneg hL i))

theorem Close.trans {v w z : State E} {L D F : ℝ} (hv : Close v w L D) (hw : Close w z L F) :
    Close v z L (D + F) := by
  intro i
  calc
    _ ≤ ‖v i - w i‖ + ‖w i - z i‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (v i - w i) (w i - z i)
    _ ≤ weight L i * D + weight L i * F := add_le_add (hv i) (hw i)
    _ = _ := by ring

theorem Close.mono {v w : State E} {L D F : ℝ} (hv : Close v w L D) (hL : 0 ≤ L) (hDF : D ≤ F) :
    Close v w L F := Bounded.mono hv hL hDF

variable [NormedSpace ℝ E]

theorem affine_size (theta : ℝ) (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (x b : E) (S : ℝ) (hx : ‖x‖ ≤ S) (hb : ‖b‖ ≤ S) : ‖b + theta • (x - b)‖ ≤ S := by
  have he : b + theta • (x - b) = theta • x + (1 - theta) • b := by module
  rw [he]
  have hh := norm_add_le (theta • x) ((1 - theta) • b)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg htheta, abs_of_nonneg (sub_nonneg.mpr htheta1)] at hh
  nlinarith [mul_le_mul_of_nonneg_left hx htheta,
    mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr htheta1)]

theorem affine_close (theta : ℝ) (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (x b y c : E) (D : ℝ) (hx : ‖x - y‖ ≤ D) (hb : ‖b - c‖ ≤ D) :
    ‖(b + theta • (x - b)) - (c + theta • (y - c))‖ ≤ D := by
  have he : (b + theta • (x - b)) - (c + theta • (y - c)) =
      (b - c) + theta • ((x - y) - (b - c)) := by module
  rw [he]
  exact affine_size theta htheta htheta1 (x - y) (b - c) D hx hb

end
end InexactRealizations.Accuracy.Execution
