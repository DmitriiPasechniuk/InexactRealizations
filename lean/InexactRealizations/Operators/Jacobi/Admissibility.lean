import InexactRealizations.Operators.Jacobi.Determinant
import InexactRealizations.Operators.Spectral.OperatorNorm
import Mathlib.Analysis.Matrix.PosDef

/-! E.7, with actual principal matrices: every principal continuant is positive above the spectrum.
Use: `InexactRealizations.Operators.JacobiData.admissible_of_spectrum` feeds `InexactRealizations.Chains.Jacobi.admissible`
(Positivity of all principal determinants at z_0).
Proof chain: `InexactRealizations.Operators.SineJacobi.gain_exact` — chebyshev1,; Exact sine gain,
resolvent expression, asymptotics and energy value.
-/
namespace InexactRealizations.Operators.JacobiData
noncomputable section
open Polynomial Matrix Unitary
open scoped Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
variable (J : JacobiData)

/-- The precise assertion is `(Matrix.scalar (Fin N) eta - J.matrix 0 N).PosDef`. -/
theorem shifted_posDef (N : ℕ) (eta : ℝ) (he : 1 < eta)
    (hspec : spectrum ℝ (J.matrix 0 N) ⊆ Set.Icc (-1) 1) :
    (Matrix.scalar (Fin N) eta - J.matrix 0 N).PosDef := by
  let M := J.matrix 0 N
  have hM : M.IsHermitian := J.matrix_isHermitian 0 N
  have hp : (aeval M (C eta-X)).PosDef := by
    rw [hM.spectral_theorem, Polynomial.aeval_algHom_apply]
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def, aeval_diagonal,
      RCLike.ofReal_real_eq_id, id_eq, eval_sub, eval_C, eval_X]
    apply isUnit_coe.posDef_star_right_conjugate_iff.mpr
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    have hi := (hspec (hM.eigenvalues_mem_spectrum_real i)).2
    simpa using sub_pos.mpr (hi.trans_lt he)
  simpa [map_sub, aeval_C, aeval_X, Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def,
    Matrix.scalar, M] using hp

/-- E.7, with actual principal matrices: every principal continuant is positive above the spectrum.

The stated quantitative bound `0 < (J.block a n).eval eta`.
-/
theorem block_eval_pos_of_spectrum {N a n : ℕ} (hsq : ∀ s, 0 ≤ J.aSq s)
    (hn : a+n ≤ N) (eta : ℝ) (he : 1 < eta)
    (hspec : spectrum ℝ (J.matrix 0 N) ⊆ Set.Icc (-1) 1) :
    0 < (J.block a n).eval eta := by
  let e : Fin n → Fin N := fun i => ⟨a+i.val, by omega⟩
  have hinj : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have hh := congrArg Fin.val hij
    dsimp [e] at hh
    omega
  have hp := (J.shifted_posDef N eta he hspec).submatrix hinj
  have hsub : (Matrix.scalar (Fin N) eta - J.matrix 0 N).submatrix e e =
      Matrix.scalar (Fin n) eta - J.matrix a n := by
    change ((Matrix.scalar (Fin N) eta).submatrix e e - (J.matrix 0 N).submatrix e e) = _
    rw [J.matrix_principal_block N a n hn]
    congr 1
    ext i j
    simp [Matrix.scalar, Matrix.diagonal, Matrix.submatrix_apply, hinj.eq_iff]
  rw [hsub] at hp
  rw [J.block_eq_charpoly hsq, Matrix.eval_charpoly]
  exact hp.det_pos

/-- The precise assertion is `J.Admissible I N`. -/
theorem admissible_of_spectrum (I : SpectralInterval) (N : ℕ) (hsq : ∀ s, 0 ≤ J.aSq s)
    (hspec : spectrum ℝ (J.matrix 0 N) ⊆ Set.Icc (-1) 1) : J.Admissible I N := by
  intro n hn
  exact J.block_eval_pos_of_spectrum hsq (by omega : 0+n ≤ N) I.eta I.eta_gt_one hspec

end
end InexactRealizations.Operators.JacobiData
