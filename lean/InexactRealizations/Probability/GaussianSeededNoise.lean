import InexactRealizations.Probability.GaussianNoise
import InexactRealizations.Probability.IndependentSeed
import Mathlib.MeasureTheory.Integral.Prod

/-! The Gaussian lower-bound instance with an independent algorithm seed.
The noise filtration contains the seed and the hidden initial instance;
the adaptive method still receives only its seed and earlier answers. 
-/
namespace InexactRealizations.Probability.Gaussian
noncomputable section
open MeasureTheory ProbabilityTheory Filter
variable {N : ℕ} {U : Type*} [MeasurableSpace U]

abbrev PriorIndex (N n : ℕ) := {i : Option (Fin N) // earlier n i}

def priorVector (N : ℕ) (r sigma : ℝ) (n : ℕ) (x : Sample N) : PriorIndex N n → ℝ :=
  fun i ↦ scaledCoordinate r sigma i.val x

theorem priorVector_measurable (N : ℕ) (r sigma : ℝ) (n : ℕ) :
    @Measurable (Sample N) (PriorIndex N n → ℝ) (past N r sigma n) inferInstance
      (priorVector N r sigma n) := by
  let : MeasurableSpace (Sample N) := past N r sigma n
  apply Measurable.of_eval
  intro i
  exact measurable_iff_comap_le.mpr (le_iSup_of_le i.val (le_iSup_of_le i.property le_rfl))

theorem priorVector_ambient (N : ℕ) (r sigma : ℝ) (n : ℕ) :
    Measurable (priorVector N r sigma n) :=
  (priorVector_measurable N r sigma n).mono ((past N r sigma).le n) le_rfl

def seedView (N : ℕ) (r sigma : ℝ) (n : ℕ) (p : U × Sample N) : U × (PriorIndex N n → ℝ) :=
  (p.1, priorVector N r sigma n p.2)

def seededPast (U : Type*) [MeasurableSpace U] (N : ℕ) (r sigma : ℝ) :
    Filtration ℕ (inferInstance : MeasurableSpace (U × Sample N)) where
  seq n := MeasurableSpace.comap (seedView N r sigma n) inferInstance
  mono' n m hnm := by
    let : MeasurableSpace (U × Sample N) := MeasurableSpace.comap
      (seedView (U := U) N r sigma m) (inferInstance : MeasurableSpace (U × (PriorIndex N m → ℝ)))
    apply measurable_iff_comap_le.mp
    have hm : Measurable (seedView (U := U) N r sigma m) := comap_measurable _
    apply (measurable_fst.comp hm).prodMk
    apply Measurable.of_eval
    intro i
    have him : earlier m i.val := by
      rcases i with ⟨i, hi⟩
      cases i with
      | none => trivial
      | some s => exact hi.trans_le hnm
    exact (measurable_pi_apply (⟨i.val, him⟩ : PriorIndex N m)).comp (measurable_snd.comp hm)
  le' n := (measurable_fst.prodMk ((priorVector_ambient N r sigma n).comp measurable_snd)).comap_le

theorem seed_measurable (N : ℕ) (r sigma : ℝ) (n : ℕ) :
    @Measurable (U × Sample N) U (seededPast U N r sigma n) inferInstance Prod.fst := by
  have hm : @Measurable (U × Sample N) (U × (PriorIndex N n → ℝ))
      (seededPast U N r sigma n) inferInstance (seedView N r sigma n) := comap_measurable _
  have hp : Measurable (fun v : U × (PriorIndex N n → ℝ) ↦ v.1) := measurable_fst
  exact hp.comp hm

theorem seeded_coordinate_measurable (r sigma : ℝ) (n : ℕ) (i : PriorIndex N n) :
    @Measurable (U × Sample N) ℝ (seededPast U N r sigma n) inferInstance
      (fun p ↦ scaledCoordinate r sigma i.val p.2) :=
  (measurable_pi_apply i).comp (measurable_snd.comp (comap_measurable (seedView N r sigma n)))

theorem seeded_hidden_measurable (N : ℕ) (r sigma : ℝ) :
    StronglyMeasurable[seededPast U N r sigma 0] (fun p : U × Sample N ↦ r * p.2 none) :=
  (seeded_coordinate_measurable r sigma 0 ⟨none, True.intro⟩).stronglyMeasurable

theorem seeded_noise_measurable (N : ℕ) (r sigma : ℝ) (s : ℕ) (hs : s < N) :
    StronglyMeasurable[seededPast U N r sigma (s + 1)]
      (fun p : U × Sample N ↦ noise N sigma s p.2) := by
  simp_rw [noise_eq N r sigma s hs]
  exact (seeded_coordinate_measurable r sigma (s + 1) ⟨some ⟨s, hs⟩, Nat.lt_succ_self s⟩).stronglyMeasurable

theorem seeded_independent_past (N : ℕ) (r sigma : ℝ) (s : Fin N)
    (P : Measure U) [IsProbabilityMeasure P] :
    Indep (MeasurableSpace.comap (fun p : U × Sample N ↦ scaledCoordinate r sigma (some s) p.2)
      (inferInstance : MeasurableSpace ℝ)) (seededPast U N r sigma s.val) (P.prod (stdGaussian (Sample N))) := by
  have hi : IndepFun (scaledCoordinate r sigma (some s)) (priorVector N r sigma s.val)
      (stdGaussian (Sample N)) :=
    indep_of_indep_of_le_right (independent_past N r sigma s)
      (priorVector_measurable N r sigma s.val).comap_le
  exact independent_seed_pair (scaledCoordinate_measurable r sigma (some s))
    (priorVector_ambient N r sigma s.val) hi

theorem seeded_noise_martingale (N : ℕ) (r sigma : ℝ) (P : Measure U) [IsProbabilityMeasure P] :
    MartingaleDifferences N (seededPast U N r sigma)
      (fun s p ↦ noise N sigma s p.2) (P.prod (stdGaussian (Sample N))) where
  adapted s hs := seeded_noise_measurable N r sigma s hs
  squareIntegrable s hs :=
    ((noise_martingale N r sigma).squareIntegrable s hs).comp_measurePreserving measurePreserving_snd
  centered s hs := by
    simp_rw [noise_eq N r sigma s hs]
    have hm : Measurable (fun p : U × Sample N ↦ scaledCoordinate r sigma (some ⟨s, hs⟩) p.2) :=
      (scaledCoordinate_measurable r sigma _).comp measurable_snd
    have hh := condExp_indep_eq hm.comap_le ((seededPast U N r sigma).le s)
      (comap_measurable (fun p : U × Sample N ↦ scaledCoordinate r sigma (some ⟨s, hs⟩) p.2)).stronglyMeasurable
      (seeded_independent_past N r sigma ⟨s, hs⟩ P)
    change _ =ᵐ[P.prod (stdGaussian (Sample N))] (fun _ ↦ 0)
    simpa only [integral_fun_snd, coordinate_mean, smul_zero] using hh

theorem seeded_noise_conditional_variance (N : ℕ) (r sigma : ℝ)
    (P : Measure U) [IsProbabilityMeasure P] (s : ℕ) (hs : s < N) :
    (P.prod (stdGaussian (Sample N)))[fun p ↦ ‖noise N sigma s p.2‖ ^ 2 | seededPast U N r sigma s]
      =ᵐ[P.prod (stdGaussian (Sample N))] fun _ ↦ sigma ^ 2 := by
  simp_rw [noise_eq N r sigma s hs]
  have hm : Measurable (fun p : U × Sample N ↦ scaledCoordinate r sigma (some ⟨s, hs⟩) p.2) :=
    (scaledCoordinate_measurable r sigma _).comp measurable_snd
  have hh := condExp_indep_eq hm.comap_le ((seededPast U N r sigma).le s)
    (((comap_measurable (fun p : U × Sample N ↦ scaledCoordinate r sigma (some ⟨s, hs⟩) p.2)).stronglyMeasurable.norm).pow 2)
    (seeded_independent_past N r sigma ⟨s, hs⟩ P)
  change (P.prod (stdGaussian (Sample N)))[fun p ↦ ‖scaledCoordinate r sigma (some ⟨s, hs⟩) p.2‖ ^ 2 |
    seededPast U N r sigma s] =ᵐ[P.prod (stdGaussian (Sample N))]
    (fun _ ↦ ∫ p : U × Sample N, ‖scaledCoordinate r sigma (some ⟨s, hs⟩) p.2‖ ^ 2
      ∂P.prod (stdGaussian (Sample N))) at hh
  have hmoment : (∫ p : U × Sample N, ‖scaledCoordinate r sigma (some ⟨s, hs⟩) p.2‖ ^ 2
      ∂P.prod (stdGaussian (Sample N))) = sigma ^ 2 := by
    calc
      _ = P.real Set.univ • ∫ x, ‖scaledCoordinate r sigma (some ⟨s, hs⟩) x‖ ^ 2
          ∂stdGaussian (Sample N) := integral_fun_snd _
      _ = sigma ^ 2 := by rw [coordinate_second]; simp only [coordinateScale, probReal_univ, one_smul]
  rw [hmoment] at hh
  exact hh

theorem seeded_hidden_mean_budget (N : ℕ) (r : ℝ) (P : Measure U) [IsProbabilityMeasure P] :
    (∫ p : U × Sample N, ‖r * p.2 none‖ ^ 2 ∂P.prod (stdGaussian (Sample N))) = r ^ 2 := by
  calc
    _ = P.real Set.univ • ∫ x : Sample N, ‖r * x none‖ ^ 2 ∂stdGaussian (Sample N) := integral_fun_snd _
    _ = r ^ 2 := by simp only [Real.norm_eq_abs, sq_abs, hidden_mean_budget, probReal_univ, one_smul]

end
end InexactRealizations.Probability.Gaussian
