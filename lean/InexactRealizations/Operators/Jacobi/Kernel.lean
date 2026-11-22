import InexactRealizations.Operators.Jacobi.Exactness

/-! 2 in continuant coordinates, including both empty boundary blocks.
Use: `InexactRealizations.Operators.JacobiData.kernel_eq` feeds `InexactRealizations.Chains.Jacobi.kernel_endpoint` (At the
spectral endpoint the response kernel is the actual Green diagonal).
-/
namespace InexactRealizations.Operators.JacobiData
noncomputable section
open Polynomial
open scoped Matrix BigOperators
variable (J : JacobiData) (I : SpectralInterval)

/-- The nonempty tail solution; its two coordinates have different lengths.

The precise assertion is `let M`.
-/
theorem tail_column {N : ℕ} (h : J.Admissible I N) (r k : ℕ) (hr : 1 ≤ r)
    (hk : r + (k + 1) ≤ N) (lam : ℝ) :
    let M := orderedProduct (fun i => (J.realization I).scalarStep (r + i) lam) (k + 1)
    M 0 0 = J.den I r / J.den I (r + (k + 1)) * (J.block r (k + 1)).eval (I.z lam) ∧
    M 1 0 = J.den I r / J.den I (r + k) * (J.block r k).eval (I.z lam) := by
  induction k with
  | zero =>
    simp only [orderedProduct, Matrix.mul_one, Nat.add_zero]
    rw [show (J.realization I).scalarStep r lam =
      (J.realization I).scalarStep ((r - 1) + 1) lam by congr 1; omega, scalarStep_succ]
    simp only [show r - 1 + 1 = r by omega, show r - 1 + 2 = r + 1 by omega]
    constructor
    · simp [block]
      ring
    · simp [block, div_self (J.den_ne I h (show r ≤ N by omega))]
  | succ k ih =>
    have hi := ih (by omega)
    dsimp only at hi ⊢
    rw [orderedProduct_succ]
    have ht : r + (k + 1) = (r + k) + 1 := by omega
    rw [ht, scalarStep_succ]
    have hnext : r + k + 2 = r + (k + 1 + 1) := by omega
    simp only [hnext, ← ht]
    constructor
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, hi.1, hi.2]
      have hc : (J.block r (k + 2)).eval (I.z lam) =
          (I.z lam - J.b (r + k + 1)) * (J.block r (k + 1)).eval (I.z lam) -
            J.aSq (r + k + 1) * (J.block r k).eval (I.z lam) := by simp [block]
      field_simp [J.den_ne I h (show r + k ≤ N by omega),
        J.den_ne I h (show r + (k + 1) ≤ N by omega), J.den_ne I h hk]
      rw [hc]
      simp only [Nat.add_assoc]
      ring
    · simpa [Matrix.mul_apply, Fin.sum_univ_two, ht] using hi.1

/-- Exact identity `orderedProduct (fun i => (J.realization I).scalarStep (r + i) lam) (N - r) 0 0
= J.den I r / J.den I N * (J.block r (N - r)).eval (I.z lam)`.
-/
theorem tail_fundamental {N : ℕ} (h : J.Admissible I N) (r : ℕ)
    (hr : 1 ≤ r) (hrN : r ≤ N) (lam : ℝ) :
    orderedProduct (fun i => (J.realization I).scalarStep (r + i) lam) (N - r) 0 0 =
      J.den I r / J.den I N * (J.block r (N - r)).eval (I.z lam) := by
  cases hk : N - r with
  | zero =>
    have he : r = N := by omega
    simp [he, block, div_self (J.den_ne I h le_rfl), orderedProduct]
  | succ k =>
    have he : r + (k + 1) = N := by omega
    simpa only [hk, he] using (J.tail_column I h r k hr (by omega) lam).1

/-- Exact identity `(J.realization I).kernel N s lam nu = -(orderedProduct (fun i => (J.realization
I).scalarStep (s + 1 + i) lam) (N - (s + 1)) 0 0 * (J.method I).gamma s * orderedProduct (fun i
=> (J.realization I).scalarStep i nu) s 0 0)`.
-/
theorem kernel_factorization (N s : ℕ) (lam nu : ℝ) :
    (J.realization I).kernel N s lam nu =
      -(orderedProduct (fun i => (J.realization I).scalarStep (s + 1 + i) lam)
          (N - (s + 1)) 0 0 * (J.method I).gamma s *
        orderedProduct (fun i => (J.realization I).scalarStep i nu) s 0 0) := by simp [Realization.kernel, realization, Matrix.mul_apply, Fin.sum_univ_two]

/-- 2 in continuant coordinates, including both empty boundary blocks.

Exact identity `(J.realization I).kernel N s lam nu = -(2 / (I.delta * J.den I N)) * (J.block
(s + 1) (N - (s + 1))).eval (I.z lam) * (J.leading s).eval (I.z nu)`.
-/
theorem kernel_eq {N : ℕ} (h : J.Admissible I N) (s : ℕ) (hs : s < N) (lam nu : ℝ) :
    (J.realization I).kernel N s lam nu = -(2 / (I.delta * J.den I N)) *
      (J.block (s + 1) (N - (s + 1))).eval (I.z lam) * (J.leading s).eval (I.z nu) := by
  rw [kernel_factorization, J.tail_fundamental I h (s + 1) (by omega) (by omega)]
  have hp : orderedProduct (fun i => (J.realization I).scalarStep i nu) s 0 0 =
      (J.leading s).eval (I.z nu) / J.den I s := by
    simpa [Realization.scalarTransfer, realization] using
      (J.scalar_exact I h s (by omega) nu).trans (J.residual_eval I s nu)
  rw [hp]
  dsimp [method]
  field_simp [J.den_ne I h (show s ≤ N by omega),
    J.den_ne I h (show s + 1 ≤ N by omega), J.den_ne I h le_rfl,
    ne_of_gt I.delta_pos]

end
end InexactRealizations.Operators.JacobiData
