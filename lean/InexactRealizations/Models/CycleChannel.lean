import InexactRealizations.Models.CycleSpectrum
import InexactRealizations.Models.NetworkExecution
import InexactRealizations.Channel.Roots.Coordinates

namespace InexactRealizations.Models.Network
noncomputable section
open scoped BigOperators
open MeasureTheory
variable (m : ℕ) [NeZero m]

/-- The actual active cycle oracle in genuine real orthonormal spectral coordinates. -/
theorem cycleOracle_spectral {N : ℕ} (κ δ : ℝ) (ξ : Fin N → ℝ) (s : Fin N)
    (u : EuclideanSpace ℝ (Fin m)) :
    (realEigenbasis m).repr
      (activeOracle (cycleLaplacian m) (2/(κ-1)) δ ξ s ((realEigenbasis m).repr.symm u))=
      Channel.Roots.euclideanOracle (activeSpectralValue m κ) δ ξ s u := by
  let v := (realEigenbasis m).repr.symm u
  have he : activeOracle (cycleLaplacian m) (2/(κ-1)) δ ξ s v=
      (4+2*(2/(κ-1)))⁻¹ • cycleOperator m v+
      ((4+2*(2/(κ-1)))⁻¹*(2*(2/(κ-1)))) • v+(δ*ξ s) • v := by
    ext i
    simp only [activeOracle,PiLp.toLp_apply,PiLp.add_apply,PiLp.smul_apply,
      Pi.add_apply,Pi.smul_apply,cycleOperator_apply,smul_eq_mul,cycleLaplacian,
      LinearMap.coe_mk,AddHom.coe_mk]
    ring
  rw [he,map_add,map_add,map_smul,map_smul,map_smul]
  ext j
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,realEigenbasis_diagonalization,
    v,LinearIsometryEquiv.apply_symm_apply]
  change _=(activeSpectralValue m κ j+δ*ξ s)*u j
  unfold activeSpectralValue
  ring

/-- Every actual active-cycle history output equals the transported spectral-coordinate output. -/
theorem cycle_output_spectral {N : ℕ} (h : InexactRealizations.History N) (κ δ : ℝ) (ξ : Fin N → ℝ)
    (initial : EuclideanSpace ℝ (Fin m)) :
    h.oracleOutput ((realEigenbasis m).repr.symm initial)
      (activeOracle (cycleLaplacian m) (2/(κ-1)) δ ξ)=
    (realEigenbasis m).repr.symm
      (h.oracleOutput initial (Channel.Roots.euclideanOracle (activeSpectralValue m κ) δ ξ)) := by
  apply h.oracleOutput_map (realEigenbasis m).repr.symm.toLinearEquiv.toLinearMap
  intro s u
  apply (realEigenbasis m).repr.injective
  change (realEigenbasis m).repr
    (activeOracle (cycleLaplacian m) (2/(κ-1)) δ ξ s ((realEigenbasis m).repr.symm u))=
    (realEigenbasis m).repr ((realEigenbasis m).repr.symm
      (Channel.Roots.euclideanOracle (activeSpectralValue m κ) δ ξ s u))
  rw [cycleOracle_spectral,LinearIsometryEquiv.apply_symm_apply]

/-- The full physical network output is its genuinely isometric spectral-coordinate output. -/
theorem cycle_network_output_spectral {N : ℕ} (h : InexactRealizations.History N) (κ δ : ℝ)
    (ξ : Fin N → ℝ) (initial : EuclideanSpace ℝ (Fin m)) :
    h.oracleOutput (activeEmbedding ((realEigenbasis m).repr.symm initial))
      (ambientOracle (cycleLaplacian m) (2/(κ-1)) δ ξ)=
      activeEmbedding ((realEigenbasis m).repr.symm (h.oracleOutput initial
        (Channel.Roots.euclideanOracle (activeSpectralValue m κ) δ ξ))) := by
  rw [network_output_active,cycle_output_spectral]

omit [NeZero m] in
/-- The literal diagonal channel oracle is the differentiated Hessian-perturbation oracle. -/
theorem spectralOracle_eq_perturbed {N : ℕ} (eig : Fin m → ℝ) (δ : ℝ) (ξ : Fin N → ℝ) :
    Channel.Roots.euclideanOracle eig δ ξ=
      InexactRealizations.History.perturbedOracle (InexactRealizations.History.matrixEnd (Matrix.diagonal eig))
        (fun s => ξ s • (LinearMap.id : Module.End ℝ (EuclideanSpace ℝ (Fin m)))) δ := by
  funext s
  ext u j
  change (eig j+δ*ξ s)*u j=(Matrix.diagonal eig).mulVec u.ofLp j+δ*(ξ s*u j)
  simp only [Matrix.mulVec,Matrix.diagonal,Matrix.of_apply,dotProduct,ite_mul,zero_mul,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true]
  ring

/-- The article's signal matrix differentiates the actual full physical network iteration. -/
theorem cycle_network_hasDerivAt {N : ℕ} (h : InexactRealizations.History N) (κ : ℝ)
    (initial : EuclideanSpace ℝ (Fin m)) (e : EuclideanSpace ℝ (Fin N)) :
    HasDerivAt (fun t => h.oracleOutput
      (activeEmbedding ((realEigenbasis m).repr.symm initial))
      (ambientOracle (cycleLaplacian m) (2/(κ-1)) t (fun s => e s)))
      (activeEmbedding ((realEigenbasis m).repr.symm
        (Channel.signalOperator h (activeSpectralValue m κ) initial.ofLp e))) 0 := by
  let R : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 2×ZMod m) :=
    activeEmbedding.toContinuousLinearMap.comp (realEigenbasis m).repr.symm.toContinuousLinearMap
  have hd := R.hasFDerivAt.comp_hasDerivAt 0
    (Channel.hasDerivAt_signal_output h (activeSpectralValue m κ) initial e)
  convert hd using 1
  · funext t
    rw [cycle_network_output_spectral,spectralOracle_eq_perturbed]
    rfl
  · rfl

/-- The actual ambient network derivative has exactly the signal-matrix output norm. -/
theorem cycle_network_derivative_norm {N : ℕ} (h : InexactRealizations.History N) (κ : ℝ)
    (initial : EuclideanSpace ℝ (Fin m)) (e : EuclideanSpace ℝ (Fin N)) :
    ‖activeEmbedding ((realEigenbasis m).repr.symm
      (Channel.signalOperator h (activeSpectralValue m κ) initial.ofLp e))‖=
      ‖Channel.signalOperator h (activeSpectralValue m κ) initial.ofLp e‖ := by
  rw [LinearIsometry.norm_map,LinearIsometryEquiv.norm_map]

end
end InexactRealizations.Models.Network
