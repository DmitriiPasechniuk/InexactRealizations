import InexactRealizations.Probability.GaussianAdaptive
import InexactRealizations.Probability.GaussianSeededNoise

/-! Actual adaptive queries are measurable for the seeded Gaussian noise
filtration. The hidden target is used by the oracle, not by the method. 
-/
namespace InexactRealizations.Probability.Gaussian
noncomputable section
open MeasureTheory
variable {N : ℕ} {U : Type*} [MeasurableSpace U]

def gaussianQuery (M : AdaptiveMethod N ℝ U) (mu r sigma : ℝ) (s : Fin N) (p : U × Sample N) : ℝ :=
  M.query s (p.1, fun j ↦ M.answersThrough (physicalOracle mu r sigma p.2) p.1 s.val
    ⟨j.val, j.isLt.trans s.isLt⟩)

theorem measurable_gaussian_answers (M : AdaptiveMethod N ℝ U) (mu r sigma : ℝ) (n : ℕ) :
    @Measurable (U × Sample N) (Fin N → ℝ) (seededPast U N r sigma n) inferInstance
      (fun p ↦ M.answersThrough (physicalOracle mu r sigma p.2) p.1 n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hmon := (seededPast U N r sigma).mono (Nat.le_succ n)
    have hi := ih.mono hmon le_rfl
    by_cases hn : n < N
    · have hq : @Measurable (U × Sample N) ℝ (seededPast U N r sigma n) inferInstance
          (gaussianQuery M mu r sigma ⟨n, hn⟩) := by
        let : MeasurableSpace (U × Sample N) := seededPast U N r sigma n
        apply (M.query_measurable ⟨n, hn⟩).comp
        apply (seed_measurable N r sigma n).prodMk
        exact Measurable.of_eval fun j ↦ (measurable_pi_apply _).comp ih
      let : MeasurableSpace (U × Sample N) := seededPast U N r sigma (n + 1)
      have htarget := ((seeded_hidden_measurable (U := U) N r sigma).mono
        ((seededPast U N r sigma).mono (Nat.zero_le (n + 1)))).measurable
      have hnoise := (seeded_noise_measurable (U := U) N r sigma n hn).measurable
      have ha : @Measurable (U × Sample N) ℝ (seededPast U N r sigma (n + 1)) inferInstance
          (fun p ↦ physicalOracle mu r sigma p.2 ⟨n, hn⟩ (gaussianQuery M mu r sigma ⟨n, hn⟩ p)) := by
        have hc : Measurable (fun _ : U × Sample N ↦ mu) := measurable_const
        have hh := (hc.mul ((hq.mono hmon le_rfl).sub htarget)).add hnoise
        change Measurable (fun p : U × Sample N ↦
          mu * (gaussianQuery M mu r sigma ⟨n, hn⟩ p - r * p.2 none) + noise N sigma n p.2) at hh
        simpa only [physicalOracle, noise, hn, dite_true] using hh
      apply Measurable.of_eval
      intro s
      by_cases hs : s = (⟨n, hn⟩ : Fin N)
      · subst s
        simp only [AdaptiveMethod.answersThrough, hn, dite_true, Function.update_self]
        exact ha
      · simp only [AdaptiveMethod.answersThrough, hn, dite_true, Function.update_of_ne hs]
        exact (measurable_pi_apply s).comp hi
    · simpa only [AdaptiveMethod.answersThrough, hn, dite_false] using hi

theorem gaussianQuery_adapted (M : AdaptiveMethod N ℝ U) (mu r sigma : ℝ) (s : Fin N) :
    StronglyMeasurable[seededPast U N r sigma s.val] (gaussianQuery M mu r sigma s) := by
  let : MeasurableSpace (U × Sample N) := seededPast U N r sigma s.val
  apply Measurable.stronglyMeasurable
  apply (M.query_measurable s).comp
  apply (seed_measurable N r sigma s.val).prodMk
  exact Measurable.of_eval fun j ↦ (measurable_pi_apply _).comp
    (measurable_gaussian_answers M mu r sigma s.val)

end
end InexactRealizations.Probability.Gaussian
