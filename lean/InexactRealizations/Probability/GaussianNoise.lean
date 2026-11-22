import InexactRealizations.Probability.GaussianMean
import Mathlib.Probability.ConditionalExpectation

/-! The actual Gaussian lower-bound instance satisfies noise
conditions even after conditioning on the hidden minimizer. This filtration
is used for noise assumptions; it is not the adaptive method's interface. 
-/
namespace InexactRealizations.Probability.Gaussian
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

theorem coordinates_independent (N : ℕ) :
    iIndepFun (fun i : Option (Fin N) ↦ fun x : Sample N ↦ x i) (stdGaussian (Sample N)) := by
  let L : Sample N →L[ℝ] (Option (Fin N) → ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin N) ↦ ℝ)).toContinuousLinearMap
  have hG := (IsGaussian.hasGaussianLaw_id (μ := stdGaussian (Sample N))).map_fun L
  apply hG.iIndepFun_of_covariance_eq_zero
  intro i j hij
  change cov[fun x : Sample N ↦ x i, fun x : Sample N ↦ x j; stdGaussian (Sample N)] = 0
  have hh := covarianceBilin_apply_eq_cov (μ := stdGaussian (Sample N))
    IsGaussian.memLp_two_id (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simp only [EuclideanSpace.inner_single_left, conj_trivial, one_mul] at hh
  rw [← hh, covarianceBilin_stdGaussian]
  change inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) = 0
  simp [EuclideanSpace.inner_single_left, hij]

def coordinateScale {N : ℕ} (r sigma : ℝ) : Option (Fin N) → ℝ
  | none => r
  | some _ => sigma

def scaledCoordinate {N : ℕ} (r sigma : ℝ) (i : Option (Fin N)) (x : Sample N) : ℝ :=
  coordinateScale r sigma i * x i

theorem scaledCoordinate_linear {N : ℕ} (r sigma : ℝ) (i : Option (Fin N)) :
    scaledCoordinate r sigma i = fun x : Sample N ↦
      inner ℝ (EuclideanSpace.single i (coordinateScale r sigma i)) x := by
  funext x
  simp [scaledCoordinate, EuclideanSpace.inner_single_left]

theorem scaledCoordinate_measurable {N : ℕ} (r sigma : ℝ) (i : Option (Fin N)) :
    Measurable (scaledCoordinate r sigma i) := by
  rw [scaledCoordinate_linear]
  exact (innerSL ℝ _).continuous.measurable

theorem scaled_independent (N : ℕ) (r sigma : ℝ) :
    iIndepFun (scaledCoordinate r sigma) (stdGaussian (Sample N)) :=
  (coordinates_independent N).comp (fun i x ↦ coordinateScale r sigma i * x)
    (fun _ ↦ measurable_const.mul measurable_id)

def earlier {N : ℕ} (n : ℕ) : Option (Fin N) → Prop
  | none => True
  | some s => s.val < n

def past (N : ℕ) (r sigma : ℝ) : Filtration ℕ (inferInstance : MeasurableSpace (Sample N)) where
  seq n := ⨆ i : Option (Fin N), ⨆ (_ : earlier n i),
    MeasurableSpace.comap (scaledCoordinate r sigma i) (inferInstance : MeasurableSpace ℝ)
  mono' n m hnm := iSup_le fun i ↦ iSup_le fun hi ↦ by
    have him : earlier m i := by
      cases i with
      | none => trivial
      | some s => exact hi.trans_le hnm
    exact le_iSup_of_le i (le_iSup_of_le him le_rfl)
  le' _ := iSup_le fun i ↦ iSup_le fun _ ↦ (scaledCoordinate_measurable r sigma i).comap_le

theorem independent_past (N : ℕ) (r sigma : ℝ) (s : Fin N) :
    Indep (MeasurableSpace.comap (scaledCoordinate r sigma (some s))
      (inferInstance : MeasurableSpace ℝ)) (past N r sigma s.val) (stdGaussian (Sample N)) := by
  have hi := indep_iSup_of_disjoint
    (fun i ↦ (scaledCoordinate_measurable r sigma i).comap_le) (scaled_independent N r sigma)
    (S := {some s}) (T := {i | earlier s.val i})
    (by simp [earlier] : Disjoint ({some s} : Set (Option (Fin N))) {i | earlier s.val i})
  simpa only [past, iSup_singleton, Set.mem_ofPred_eq] using hi

def noise (N : ℕ) (sigma : ℝ) (s : ℕ) (x : Sample N) : ℝ :=
  if hs : s < N then sigma * x (some ⟨s, hs⟩) else 0

theorem noise_eq (N : ℕ) (r sigma : ℝ) (s : ℕ) (hs : s < N) :
    noise N sigma s = scaledCoordinate r sigma (some ⟨s, hs⟩) := by
  funext x
  simp [noise, hs, scaledCoordinate, coordinateScale]

theorem coordinate_mean {N : ℕ} (r sigma : ℝ) (i : Option (Fin N)) :
    (∫ x, scaledCoordinate r sigma i x ∂stdGaussian (Sample N)) = 0 := by
  rw [scaledCoordinate_linear]
  exact linear_mean _

theorem coordinate_second {N : ℕ} (r sigma : ℝ) (i : Option (Fin N)) :
    (∫ x, ‖scaledCoordinate r sigma i x‖ ^ 2 ∂stdGaussian (Sample N)) =
      coordinateScale r sigma i ^ 2 := by
  rw [scaledCoordinate_linear]
  simp only [Real.norm_eq_abs, sq_abs]
  simpa only [PiLp.norm_single, Real.norm_eq_abs, sq_abs] using
    linear_second_moment (EuclideanSpace.single i (coordinateScale r sigma i))

theorem noise_martingale (N : ℕ) (r sigma : ℝ) :
    MartingaleDifferences N (past N r sigma) (noise N sigma) (stdGaussian (Sample N)) where
  adapted s hs := by
    rw [noise_eq N r sigma s hs]
    exact (comap_measurable (scaledCoordinate r sigma (some ⟨s, hs⟩))).stronglyMeasurable.mono
      (le_iSup_of_le (some ⟨s, hs⟩) (le_iSup_of_le (Nat.lt_succ_self s) le_rfl))
  squareIntegrable s hs := by
    rw [noise_eq N r sigma s hs, scaledCoordinate_linear]
    exact linear_memLp _
  centered s hs := by
    rw [noise_eq N r sigma s hs]
    have hh := condExp_indep_eq (scaledCoordinate_measurable r sigma (some ⟨s, hs⟩)).comap_le
      ((past N r sigma).le s) (comap_measurable (scaledCoordinate r sigma (some ⟨s, hs⟩))).stronglyMeasurable
      (independent_past N r sigma ⟨s, hs⟩)
    change _ =ᵐ[stdGaussian (Sample N)] (fun _ ↦ 0)
    simpa only [coordinate_mean] using hh

end
end InexactRealizations.Probability.Gaussian
