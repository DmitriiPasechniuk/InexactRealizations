import InexactRealizations.Budgets.Support
import InexactRealizations.Budgets.Corners
import InexactRealizations.Gains.Witness

/-! Actual operator first-variation gains for every call exponent.
The original shared budget and symmetric perturbation restriction are
explicit. Symmetric two-mode maps attain every fixed spectral pairing. 
-/
namespace InexactRealizations.Budgets
noncomputable section
open Polynomial InexactRealizations.Gains
open scoped BigOperators ENNReal NNReal
variable {N : ℕ}

inductive OperatorValue (p : ℝ≥0∞) (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (symmetric : Bool) : ℝ → Prop where
  | execution (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (D : Fin N → E →ₗ[ℝ] E)
      (delta : Fin N → ℝ) (hd : Budget p delta) (hD : ∀ s, ‖(D s).toContinuousLinearMap‖ ≤ delta s)
      (hsym : symmetric = true → ∀ s, (D s).IsSymmetric) (initial : E) (hi : ‖initial‖ ≤ 1) :
      OperatorValue p h I symmetric ‖h.firstVariation H D initial‖

def operatorValues (p : ℝ≥0∞) (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (symmetric : Bool) : Set ℝ :=
  {v | OperatorValue p h I symmetric v}
def operatorGain (p : ℝ≥0∞) (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (symmetric : Bool) : ℝ :=
  sSup (operatorValues p h I symmetric)

variable {p q : ℝ≥0∞} [p.HolderConjugate q]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem variation_upper (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (H : E →ₗ[ℝ] E) (hH : InexactRealizations.Analysis.Admissible I H) (D : Fin N → E →ₗ[ℝ] E)
    (delta : Fin N → ℝ) (hd : Budget p delta) (hD : ∀ s, ‖(D s).toContinuousLinearMap‖ ≤ delta s)
    (initial : E) (hi : ‖initial‖ ≤ 1) (P Q : Fin N → ℝ)
    (hP : InexactRealizations.Risk.ResponseBounds h I P) (hQ : ∀ s, 0 ≤ Q s)
    (hq : ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s) :
    ‖h.firstVariation H D initial‖ ≤ callNorm q (fun s ↦ P s * Q s) := by
  have hnom (s : Fin N) : ‖(aeval H (h.query s)) initial‖ ≤ Q s :=
    (InexactRealizations.Analysis.polynomial_action_bound I H hH _ _ (hQ s) (hq s) initial).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hi (hQ s))
  unfold InexactRealizations.History.firstVariation
  have hp (s : Fin N) : ‖(aeval H (h.response s)) (D s ((aeval H (h.query s)) initial))‖ ≤
      delta s * (P s * Q s) := by
    have hDnorm := ((D s).toContinuousLinearMap.le_opNorm ((aeval H (h.query s)) initial)).trans
      (mul_le_mul (hD s) (hnom s) (norm_nonneg _) (hd.1 s))
    have hh := (InexactRealizations.Analysis.polynomial_action_bound I H hH _ _ (hP.1 s) (hP.2 s) _).trans
      (mul_le_mul_of_nonneg_left hDnorm (hP.1 s))
    convert hh using 1
    · rfl
    · ring
  have hh := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun s _ ↦ hp s))
  exact hh.trans (holder_budget (fun s ↦ P s * Q s) delta (fun s ↦ mul_nonneg (hP.1 s) (hQ s)) hd)

include q in
theorem operatorValues_bddAbove (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (symmetric : Bool) :
    BddAbove (operatorValues p h I symmetric) := by
  classical
  choose P hP0 hP using fun s : Fin N ↦ InexactRealizations.Analysis.exists_polynomial_bound I (h.response s)
  choose Q hQ0 hQ using fun s : Fin N ↦ InexactRealizations.Analysis.exists_polynomial_bound I (h.query s)
  refine ⟨callNorm q (fun s ↦ P s * Q s), ?_⟩
  intro v hv
  cases hv with
  | execution E H hH D delta hd hD hsym initial hi =>
    exact variation_upper h I H hH D delta hd hD initial hi P Q ⟨hP0, hP⟩ hQ0 hQ

include q in
theorem operatorValues_nonempty (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (symmetric : Bool) :
    (operatorValues p h I symmetric).Nonempty := by
  let : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  let H := InexactRealizations.History.scalarOperator I.mu
  have hbudget : Budget p (fun _ : Fin N ↦ 0) := by
    refine ⟨fun _ ↦ le_rfl, ?_⟩
    change ‖(0 : PiLp p (fun _ : Fin N ↦ ℝ))‖ ≤ 1
    simp
  refine ⟨‖h.firstVariation H (fun _ ↦ 0) (0 : ℝ)‖, OperatorValue.execution ℝ H
    (InexactRealizations.Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩) (fun _ ↦ 0) (fun _ ↦ 0)
    hbudget (fun _ ↦ by simp) (fun _ _ ↦ LinearMap.IsSymmetric.zero) 0 (by simp)⟩

theorem operatorGain_upper (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval) (symmetric : Bool)
    (P Q : Fin N → ℝ) (hP : InexactRealizations.Risk.ResponseBounds h I P) (hQ : ∀ s, 0 ≤ Q s)
    (hq : ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.query s).eval x| ≤ Q s) :
    operatorGain p h I symmetric ≤ callNorm q (fun s ↦ P s * Q s) := by
  apply csSup_le (operatorValues_nonempty (p := p) (q := q) h I symmetric)
  intro v hv
  cases hv with
  | execution E H hH D delta hd hD hsym initial hi =>
    exact variation_upper h I H hH D delta hd hD initial hi P Q hP hQ hq

set_option maxHeartbeats 1000000 in
theorem operator_kernel_lower [Nonempty (Fin N)] (h : InexactRealizations.History N) (I : InexactRealizations.Operators.SpectralInterval)
    (symmetric : Bool) (x y : ℝ) (hx : x ∈ Set.Icc I.mu I.L) (hy : y ∈ Set.Icc I.mu I.L) :
    callNorm q (fun s : Fin N ↦ InexactRealizations.Lower.physicalKernel h s x y) ≤ operatorGain p h I symmetric := by
  classical
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let K := fun s : Fin N ↦ InexactRealizations.Lower.physicalKernel h s x y
  obtain ⟨delta, hd, hvalue⟩ := exists_holder_budget (p := p) (q := q) (fun s ↦ |K s|) (fun _ ↦ abs_nonneg _)
  let c := fun s : Fin N ↦ if K s < 0 then -delta s else delta s
  have hc (s : Fin N) : |c s| = delta s := by
    dsimp only [c]
    split_ifs <;> simp only [abs_neg, abs_of_nonneg (hd.1 s)]
  have hpair : (∑ s, c s * K s) = callNorm q K := by
    rw [← callNorm_abs K, ← hvalue]
    apply Finset.sum_congr rfl
    intro s _
    dsimp only [c]
    split_ifs with hneg
    · rw [abs_of_neg hneg]; ring
    · rw [abs_of_nonneg (le_of_not_gt hneg)]
  let H := diagonalOperator ![x, y]
  let D := fun s : Fin N ↦ c s • swapOperator
  let initial := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  have hH : InexactRealizations.Analysis.Admissible I H := diagonalOperator_admissible I _ (by
    intro i
    fin_cases i
    · exact hx
    · exact hy)
  have hD : ∀ s, ‖(D s).toContinuousLinearMap‖ ≤ delta s := by
    intro s
    dsimp only [D]
    rw [scaledSwap_norm, hc]
  have hv : ‖h.firstVariation H D initial‖ ∈ operatorValues p h I symmetric :=
    OperatorValue.execution WitnessSpace H hH D delta hd hD
      (fun _ _ ↦ LinearMap.IsSymmetric.smul (by simp) swapOperator_symmetric) initial (by simp [initial])
  have hsup := le_csSup (operatorValues_bddAbove (p := p) (q := q) h I symmetric) hv
  have hcoord := witness_coordinate_le_norm (h.firstVariation H D initial) 0
  change |h.firstVariation (diagonalOperator ![x, y]) (fun s ↦ c s • swapOperator)
    (EuclideanSpace.single 1 1) 0| ≤ _ at hcoord
  rw [firstVariation_swap_coordinate] at hcoord
  change |∑ s, c s * K s| ≤ _ at hcoord
  rw [hpair, abs_of_nonneg (callNorm_nonneg K)] at hcoord
  exact hcoord.trans hsup

theorem operator_corner_lower (p : ℝ≥0∞) (hp : 1 ≤ p) (h : InexactRealizations.History N)
    (I : InexactRealizations.Operators.SpectralInterval) (he : h.ChebyshevExact I) (hN : 0 < N) (symmetric : Bool) :
    (N : ℝ) ^ (-(1 / p).toReal) * InexactRealizations.Lower.derivativeScale I N ≤ operatorGain p h I symmetric := by
  let : p.HolderConjugate (dualExponent p) := holder_dualExponent p hp
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hcorner := relative_endpoint_lower (p := p) (q := dualExponent p) h I he hN
  exact hcorner.trans (operator_kernel_lower (p := p) (q := dualExponent p) h I symmetric I.mu I.mu
    ⟨le_rfl, I.mu_lt_L.le⟩ ⟨le_rfl, I.mu_lt_L.le⟩)

end
end InexactRealizations.Budgets
