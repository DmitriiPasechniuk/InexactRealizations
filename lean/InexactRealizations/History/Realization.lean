import InexactRealizations.History.Execution
import Mathlib.Algebra.Polynomial.AlgebraMap
import InexactRealizations.Operators.Realization.Expansion

namespace InexactRealizations.History

open Polynomial InexactRealizations.Operators
open scoped BigOperators Polynomial Matrix
noncomputable section
variable {N : ℕ}

/-- The coefficient by which one oracle answer changes a prediction slot.
The none slot predicts the output, and some t predicts query t. Use: the rank-one realization embedding. 
-/
def predictionCoefficient (h : InexactRealizations.History N) (i : Option (Fin N)) (s : Fin N) : ℝ :=
  match i with
  | none => h.b s
  | some t => h.a t s

/-- A causal history as a rank-one, one-query-per-stage realization. Use: existing spectral response bounds and sharpness. -/
def realization (h : InexactRealizations.History N) : InexactRealizations.Operators.Realization (Option (Fin N)) where
  b _ := 1
  readout := Pi.single none 1
  P _ := 1
  g k := if hk : k < N then fun i => h.predictionCoefficient i ⟨k,hk⟩ else 0
  q k := if hk : k < N then Pi.single (some ⟨k,hk⟩) 1 else 0

/-- Scalar prediction state after k physical oracle calls, from arbitrary memory. Use: identify the embedded terminal and kernel. -/
def predictionState (h : InexactRealizations.History N) (x : ℝ)
    (v : Option (Fin N) → ℝ) (k : ℕ) : Option (Fin N) → ℝ :=
  (orderedProduct (fun j => h.realization.scalarStep j x) k) *ᵥ v

/-- The initial prediction state is the supplied vector. Use: induction on physical stages. -/
theorem predictionState_zero (h : InexactRealizations.History N) (x : ℝ)
    (v : Option (Fin N) → ℝ) : h.predictionState x v 0 = v := by
  simp [predictionState]

/-- One embedded stage subtracts its actual scalar gradient from all predictions. Use: the causal prediction invariant. -/
theorem predictionState_succ (h : InexactRealizations.History N) (x : ℝ)
    (v : Option (Fin N) → ℝ) (k : ℕ) (hk : k < N) (i : Option (Fin N)) :
    h.predictionState x v (k+1) i = h.predictionState x v k i -
      x * h.predictionCoefficient i ⟨k,hk⟩ *
        h.predictionState x v k (some ⟨k,hk⟩) := by
  change ((orderedProduct (fun j => h.realization.scalarStep j x) (k+1)) *ᵥ v) i = _
  rw [orderedProduct_succ, ← Matrix.mulVec_mulVec]
  change (h.realization.scalarStep k x *ᵥ h.predictionState x v k) i = _
  rw [InexactRealizations.Operators.Realization.scalarStep, Matrix.sub_mulVec, Matrix.smul_mulVec,
    InexactRealizations.Operators.Realization.queryFactor, Matrix.vecMulVec_mulVec]
  simp [realization, hk]
  ring

/-- A query prediction never changes after the call at which it is read. Use: the finite triangular system of all predictions. -/
theorem predictionState_stable (h : InexactRealizations.History N) (x : ℝ)
    (v : Option (Fin N) → ℝ) (s : Fin N) (k : ℕ)
    (hsk : s.val ≤ k) (hk : k ≤ N) :
    h.predictionState x v k (some s) =
      h.predictionState x v s.val (some s) := by
  induction k, hsk using Nat.le_induction with
  | base => rfl
  | succ k hsk ih =>
    rw [h.predictionState_succ x v k (by omega)]
    have ha : h.a s ⟨k,by omega⟩ = 0 := h.triangular s _ hsk
    simpa only [predictionCoefficient, ha, mul_zero, zero_mul, sub_zero] using ih (by omega)

/-- Adding one call to a truncated finite sum adds precisely that call's term. Use: the causal prediction invariant. -/
private theorem sum_before_succ (k : ℕ) (hk : k < N) (f : Fin N → ℝ) :
    (∑ j : Fin N, if j.val < k+1 then f j else 0) =
      (∑ j : Fin N, if j.val < k then f j else 0) + f ⟨k,hk⟩ := by
  have he (j : Fin N) : (if j.val < k+1 then f j else 0) =
      (if j.val < k then f j else 0) + (if j = ⟨k,hk⟩ then f j else 0) := by
    by_cases hj : j.val < k
    · have hne : j ≠ ⟨k,hk⟩ := by
        intro he
        have hj' := hj
        rw [he] at hj'
        exact Nat.lt_irrefl k hj'
      simp [hj, show j.val < k+1 by omega, hne]
    · by_cases he : j = ⟨k,hk⟩
      · subst j; simp
      · have hnot : ¬j.val < k+1 := by
          intro hlt
          have : j.val = k := by omega
          exact he (Fin.ext this)
        simp [hj, he, hnot]
  simp_rw [he, Finset.sum_add_distrib]
  simp

/-- All predictions equal initial predictions minus the answers already observed. Use: actual realization/history correspondence. -/
theorem predictionState_invariant (h : InexactRealizations.History N) (x : ℝ)
    (v : Option (Fin N) → ℝ) (k : ℕ) (hk : k ≤ N) (i : Option (Fin N)) :
    h.predictionState x v k i = v i - x * ∑ j : Fin N,
      if j.val < k then h.predictionCoefficient i j *
        h.predictionState x v j.val (some j) else 0 := by
  induction k with
  | zero => simp [h.predictionState_zero]
  | succ k ih =>
    rw [h.predictionState_succ x v k (by omega), ih (by omega),
      sum_before_succ k (by omega)]
    ring

/-- The final prediction state satisfies the complete physical triangular system. Use: identify nominal terminal and error responses. -/
theorem predictionState_final_system (h : InexactRealizations.History N) (x : ℝ)
    (v : Option (Fin N) → ℝ) (i : Option (Fin N)) :
    h.predictionState x v N i = v i - x * ∑ j,
      h.predictionCoefficient i j * h.predictionState x v N (some j) := by
  rw [h.predictionState_invariant x v N le_rfl]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [j.isLt, ite_true]
  rw [h.predictionState_stable x v j N (by omega) le_rfl]

/-- Final query predictions are the causal inverse applied to their initial values. Use: identify the realization on arbitrary memory. -/
theorem predictionState_final_queries (h : InexactRealizations.History N) (x : ℝ)
    (v : Option (Fin N) → ℝ) :
    (fun s => h.predictionState x v N (some s)) =
      Matrix.of (h.evaluated x) *ᵥ (fun s => v (some s)) := by
  have hs : h.scalarPencil x *ᵥ (fun s => h.predictionState x v N (some s)) =
      (fun s => v (some s)) := by
    rw [scalarPencil, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    funext s
    change h.predictionState x v N (some s) + x *
      ∑ j, h.a s j * h.predictionState x v N (some j) = v (some s)
    exact eq_sub_iff_add_eq.mp (h.predictionState_final_system x v (some s))
  have he := congrArg (fun w => Matrix.of (h.evaluated x) *ᵥ w) hs
  rw [Matrix.mulVec_mulVec, h.evaluated_mul_scalarPencil, Matrix.one_mulVec] at he
  exact he

/-- The final output prediction is controlled by the physical inverse row. Use: exact terminal and physical suffix response. -/
theorem predictionState_final_output (h : InexactRealizations.History N) (x : ℝ)
    (v : Option (Fin N) → ℝ) :
    h.predictionState x v N none = v none + x *
      ∑ j, (h.response j).eval x * v (some j) := by
  have hq (s : Fin N) := congrFun (h.predictionState_final_queries x v) s
  have hs : (∑ s, h.b s * ∑ j, h.evaluated x s j * v (some j)) =
      ∑ j, (∑ s, h.b s * h.evaluated x s j) * v (some j) := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [h.predictionState_final_system x v none]
  simp only [predictionCoefficient]
  simp_rw [hq, Matrix.mulVec_apply, dotProduct]
  change v none - x * (∑ s, h.b s * ∑ j,
    h.evaluated x s j * v (some j)) = _
  rw [hs]
  simp_rw [h.response_eval, neg_mul, Finset.sum_neg_distrib]
  ring

/-- The queried coordinate at each embedded stage is the physical nominal query. Use: identification of the two-variable kernel. -/
theorem predictionState_nominal_query (h : InexactRealizations.History N) (x : ℝ) (s : Fin N) :
    h.predictionState x (fun _ => 1) s.val (some s) = (h.query s).eval x := by
  rw [← h.predictionState_stable x (fun _ => 1) s N (by omega) le_rfl]
  have he := congrFun (h.predictionState_final_queries x (fun _ => 1)) s
  change h.predictionState x (fun _ => 1) N (some s) =
    ∑ j, h.evaluated x s j * 1 at he
  simpa only [mul_one, h.query_eval] using he

/-- The scalar realization readout selects the final prediction slot. Use: identify physical terminal and suffix response. -/
theorem realization_scalarContract (h : InexactRealizations.History N)
    (M : Matrix (Option (Fin N)) (Option (Fin N)) ℝ) :
    h.realization.scalarContract M = (M *ᵥ (fun _ => 1)) none := by
  simp [InexactRealizations.Operators.Realization.scalarContract, realization, Fintype.sum_option,
    Matrix.mulVec, dotProduct]

/-- A future gradient-injection vector is fixed by every stage up to its own call. Use: remove the irrelevant prefix in a physical suffix. -/
theorem predictionState_injection_fixed (h : InexactRealizations.History N) (x : ℝ)
    (s : Fin N) (k : ℕ) (hk : k ≤ s.val+1) :
    h.predictionState x (fun i => h.predictionCoefficient i s) k =
      (fun i => h.predictionCoefficient i s) := by
  induction k with
  | zero => exact h.predictionState_zero x _
  | succ k ih =>
    have hkN : k < N := by omega
    have hi := ih (by omega)
    funext i
    rw [h.predictionState_succ x _ k hkN, congrFun hi i,
      congrFun hi (some ⟨k,hkN⟩)]
    have ha : h.a ⟨k,hkN⟩ s = 0 :=
      h.triangular _ _ (show k ≤ s.val by omega)
    simp [predictionCoefficient, ha]

/-- The evaluated adjoint row equation keeps its exact physical signs. Use: identify the suffix transfer of an oracle error. -/
theorem response_eval_balance (h : InexactRealizations.History N) (x : ℝ) (s : Fin N) :
    (h.response s).eval x + x * ∑ j, h.a j s * (h.response j).eval x = -h.b s := by
  have hp := congrFun h.response_pencil s
  rw [pencil, Matrix.vecMul_add, Matrix.vecMul_one] at hp
  change h.response s + ∑ j, h.response j * h.coefficient j s = _ at hp
  have hv := congrArg (fun p : ℝ[X] => p.eval x) hp
  simp only [eval_add, eval_finsetSum, eval_mul, coefficient, eval_X, eval_C,
    eval_neg] at hv
  have hs : (∑ j, (h.response j).eval x * (x * h.a j s)) =
      x * ∑ j, h.a j s * (h.response j).eval x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rwa [hs] at hv

/-- A physical scalar suffix transports its injection with coefficient -Phi_s. Use: the separated kernel of the embedded realization. -/
theorem realization_suffix_injection (h : InexactRealizations.History N) (x : ℝ) (s : Fin N) :
    ((orderedProduct (fun j => h.realization.scalarStep (s.val+1+j) x)
      (N-(s.val+1))) *ᵥ (fun i => h.predictionCoefficient i s)) none =
      -(h.response s).eval x := by
  let tail := orderedProduct (fun j => h.realization.scalarStep (s.val+1+j) x)
    (N-(s.val+1))
  let v : Option (Fin N) → ℝ := fun i => h.predictionCoefficient i s
  have he : tail *ᵥ v = h.predictionState x v N := by
    calc
      tail *ᵥ v = tail *ᵥ h.predictionState x v (s.val+1) := by
        rw [h.predictionState_injection_fixed x s (s.val+1) le_rfl]
      _ = (tail * orderedProduct (fun j => h.realization.scalarStep j x) (s.val+1)) *ᵥ v := by
        exact Matrix.mulVec_mulVec _ _ _
      _ = h.predictionState x v N := by
        have hp := orderedProduct_add (fun j => h.realization.scalarStep j x)
          (s.val+1) (N-(s.val+1))
        rw [show s.val+1+(N-(s.val+1)) = N by omega] at hp
        dsimp only [tail]
        rw [← hp]
        rfl
  change (tail *ᵥ v) none = _
  rw [he, h.predictionState_final_output]
  simp only [v, predictionCoefficient]
  have hb := h.response_eval_balance x s
  have hs : (∑ j, (h.response j).eval x * h.a j s) =
      ∑ j, h.a j s * (h.response j).eval x := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  linarith

/-- The embedded realization's spectral kernel is the physical response-query product. Use: all imported spectral gain theorems. -/
theorem realization_kernel (h : InexactRealizations.History N) (s : Fin N) (x y : ℝ) :
    h.realization.kernel N s.val x y =
      (h.response s).eval x * (h.query s).eval y := by
  rw [InexactRealizations.Operators.Realization.kernel, h.realization_scalarContract]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    InexactRealizations.Operators.Realization.queryFactor, Matrix.vecMulVec_mulVec]
  have hq : h.realization.q s.val ⬝ᵥ
      ((orderedProduct (fun i => h.realization.scalarStep i y) s.val) *ᵥ (fun _ => 1)) =
      (h.query s).eval y := by
    change h.realization.q s.val ⬝ᵥ h.predictionState y (fun _ => 1) s.val = _
    have hs : h.realization.q s.val = Pi.single (some s) 1 := by
      simp [realization, s.isLt]
    rw [hs, single_dotProduct, one_mul]
    exact h.predictionState_nominal_query y s
  rw [hq]
  have hg : h.realization.g s.val = fun i => h.predictionCoefficient i s := by
    simp [realization, s.isLt]
  rw [hg, op_smul_eq_smul]
  change -(((orderedProduct (fun j => h.realization.scalarStep (s.val+1+j) x)
    (N-(s.val+1))) *ᵥ ((h.query s).eval y • (fun i => h.predictionCoefficient i s))) none) = _
  rw [Matrix.mulVec_smul]
  change -((h.query s).eval y * _) = _
  rw [h.realization_suffix_injection]
  ring

end
end InexactRealizations.History
