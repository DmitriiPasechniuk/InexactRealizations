import InexactRealizations.Models.CycleFourier
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import InexactRealizations.Channel.Roots.Actual
import InexactRealizations.Channel.SignalBounds
import InexactRealizations.Comparisons.Classical.Gains
import InexactRealizations.Lower.EndpointGain
import InexactRealizations.Operators.Chebyshev.EndpointDerivatives
import InexactRealizations.Operators.Stepsize.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace InexactRealizations.Models.Network
noncomputable section
open scoped BigOperators
open Polynomial
variable (m : ℕ) [NeZero m]

/-- The actual real Euclidean cycle operator, before any spectral coordinates are chosen. -/
def cycleOperator : EuclideanSpace ℝ (ZMod m) →ₗ[ℝ] EuclideanSpace ℝ (ZMod m) :=
  (WithLp.linearEquiv 2 ℝ (ZMod m → ℝ)).symm.toLinearMap.comp
    ((cycleLaplacian m).comp (WithLp.linearEquiv 2 ℝ (ZMod m → ℝ)).toLinearMap)

omit [NeZero m] in
/-- Literal coordinate action of the actual Euclidean cycle Laplacian. -/
@[simp] theorem cycleOperator_apply (u : EuclideanSpace ℝ (ZMod m)) (i : ZMod m) :
    cycleOperator m u i=2*u i-u (i+1)-u (i-1) := rfl

/-- The two cyclic shifts are exact adjoints under the physical Euclidean inner product. -/
theorem shift_inner (u v : EuclideanSpace ℝ (ZMod m)) :
    (∑ i,u (i+1)*v i)=∑ i,u i*v (i-1) := by
  have h := Equiv.sum_comp (Equiv.addRight (1:ZMod m)) (fun i => u i*v (i-1))
  simpa only [Equiv.coe_addRight,add_sub_cancel_right] using h

/-- The physical real cycle is self-adjoint; the real spectral theorem therefore applies. -/
theorem cycleOperator_symmetric : (cycleOperator m).IsSymmetric := by
  intro u v
  change inner ℝ (cycleOperator m u) v=inner ℝ u (cycleOperator m v)
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,
    cycleOperator_apply,sub_mul,mul_sub,Finset.sum_sub_distrib]
  have h1 := shift_inner m u v
  have h2 := shift_inner m v u
  have h1' : (∑ i,v i*u (i+1))=∑ i,v (i-1)*u i := by
    simpa only [mul_comm] using h1
  have h2' : (∑ i,v i*u (i-1))=∑ i,v (i+1)*u i := h2.symm
  rw [h1',h2']
  have hd : (∑ i,v i*(2*u i))=∑ i,2*v i*u i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hd]
  ring

/-- Complex Fourier coordinates of an actual real Euclidean cycle state. -/
def realFourier (u : EuclideanSpace ℝ (ZMod m)) : ZMod m → ℂ :=
  (cycleSynthesis m).symm (fun i => (u i:ℂ))

/-- Reconstructing the real state's complex Fourier coordinates recovers the state. -/
@[simp] theorem realFourier_reconstruct (u : EuclideanSpace ℝ (ZMod m)) :
    cycleSynthesis m (realFourier m u)=fun i => (u i:ℂ) :=
  (cycleSynthesis m).apply_symm_apply _

/-- Every Fourier coordinate of a real eigenstate obeys the displayed scalar eigenvalue equation. -/
theorem real_eigen_fourier (u : EuclideanSpace ℝ (ZMod m)) (lam : ℝ)
    (hu : cycleOperator m u=lam • u) (j : ZMod m) :
    (cycleEigenvalue m j:ℂ)*realFourier m u j=(lam:ℂ)*realFourier m u j := by
  have hz : complexCycle m (fun i => (u i:ℂ))=(lam:ℂ) • (fun i => (u i:ℂ)) := by
    funext i
    have h := congrArg (fun v : EuclideanSpace ℝ (ZMod m) => (v i:ℂ)) hu
    simpa only [complexCycle,LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,
      cycleOperator_apply,PiLp.smul_apply,smul_eq_mul,Complex.ofReal_sub,
      Complex.ofReal_mul,Complex.ofReal_ofNat] using h
  have hh : cycleSynthesis m (fun j => (cycleEigenvalue m j:ℂ)*realFourier m u j)=
      cycleSynthesis m ((lam:ℂ) • realFourier m u) := by
    rw [← cycle_diagonalization,realFourier_reconstruct,hz,map_smul,realFourier_reconstruct]
  exact congrFun ((cycleSynthesis m).injective hh) j

/-- Every real cycle eigenvalue is one of the explicitly displayed cosine values. -/
theorem real_eigenvalue_eq_cosine (u : EuclideanSpace ℝ (ZMod m)) (hu0 : u≠0) (lam : ℝ)
    (hu : cycleOperator m u=lam • u) : ∃ j : ZMod m,lam=cycleEigenvalue m j := by
  have hc : realFourier m u≠0 := by
    intro h
    apply hu0
    ext i
    have hi := congrFun (realFourier_reconstruct m u) i
    rw [h,map_zero] at hi
    change u i=0
    apply Complex.ofReal_injective
    simpa using hi.symm
  have hex : ∃ j,realFourier m u j≠0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  obtain ⟨j,hj⟩ := hex
  refine ⟨j,?_⟩
  exact Complex.ofReal_injective ((mul_right_cancel₀ hj (real_eigen_fourier m u lam hu j)).symm)

/-- The actual physical real cycle has an orthonormal basis of real eigenvectors. -/
def realEigenbasis : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (ZMod m)) :=
  (cycleOperator_symmetric m).eigenvectorBasis (by simp)

/-- Corresponding actual real cycle eigenvalues, with full multiplicity. -/
def realEigenvalue : Fin m → ℝ :=
  (cycleOperator_symmetric m).eigenvalues (by simp)

/-- Every chosen real orthonormal mode is an eigenvector of the actual cycle. -/
theorem realEigenbasis_eigenvector (j : Fin m) :
    cycleOperator m (realEigenbasis m j)=realEigenvalue m j • realEigenbasis m j :=
  (cycleOperator_symmetric m).apply_eigenvectorBasis _ j

/-- Every chosen real orthonormal mode has one of the actual Fourier cosine eigenvalues. -/
theorem realEigenvalue_cosine (j : Fin m) :
    ∃ k : ZMod m,realEigenvalue m j=cycleEigenvalue m k := by
  exact real_eigenvalue_eq_cosine m _ ((realEigenbasis m).orthonormal.ne_zero j) _
    (realEigenbasis_eigenvector m j)

/-- Genuine real orthonormal spectral coordinates diagonalize the actual cycle operator. -/
theorem realEigenbasis_diagonalization (u : EuclideanSpace ℝ (ZMod m)) (j : Fin m) :
    (realEigenbasis m).repr (cycleOperator m u) j=
      realEigenvalue m j*(realEigenbasis m).repr u j :=
  (cycleOperator_symmetric m).eigenvectorBasis_apply_self_apply _ u j

/-- Every displayed real cycle mode is an actual Euclidean eigenvector. -/
theorem cycleMode_euclidean_eigenvector (j : ZMod m) :
    cycleOperator m (WithLp.toLp 2 (cycleMode m j))=
      cycleEigenvalue m j • WithLp.toLp 2 (cycleMode m j) := by
  ext i
  exact congrFun (cycle_mode_eigenvector m j) i

/-- Every cosine frequency occurs among the genuine real orthonormal spectral values. -/
theorem realEigenvalue_exists (j : ZMod m) :
    ∃ i : Fin m,realEigenvalue m i=cycleEigenvalue m j := by
  apply (cycleOperator_symmetric m).exists_eigenvalues_eq (by simp)
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨?_,?_⟩
  · exact (Module.End.mem_eigenspace_iff).mpr (cycleMode_euclidean_eigenvector m j)
  · intro hz
    apply cycleMode_ne_zero m j
    have h := congrArg WithLp.ofLp hz
    exact h

/-- The unique lower endpoint index in genuine real orthonormal spectral coordinates. -/
def lowerMode : Fin m := (realEigenvalue_exists m 0).choose

/-- The unique upper endpoint index in genuine real orthonormal spectral coordinates. -/
def upperMode : Fin m := (realEigenvalue_exists m ((m/2:ℕ):ZMod m)).choose

/-- The lower chosen coordinate is exactly the constant Laplacian mode. -/
@[simp] theorem lowerMode_value : realEigenvalue m (lowerMode m)=0 := by
  exact (realEigenvalue_exists m 0).choose_spec.trans (cycleEigenvalue_zero m)

/-- At an even horizon the upper chosen coordinate is exactly the alternating mode. -/
theorem upperMode_value (hm : Even m) : realEigenvalue m (upperMode m)=4 := by
  exact (realEigenvalue_exists m ((m/2:ℕ):ZMod m)).choose_spec.trans (cycleEigenvalue_half m hm)

/-- The active spectral value attached to a genuine real orthonormal cycle mode. -/
def activeSpectralValue (κ : ℝ) (j : Fin m) : ℝ :=
  (realEigenvalue m j+2*(2/(κ-1)))/(4+2*(2/(κ-1)))

end
end InexactRealizations.Models.Network
