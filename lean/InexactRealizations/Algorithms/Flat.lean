import InexactRealizations.Algorithms.FlatRegisters
import InexactRealizations.Algorithms.FlatPreparation

namespace InexactRealizations.Algorithms.Flat
noncomputable section
open Polynomial
open scoped BigOperators

/-- All prepared scalar data of the printed Flat algorithm. -/
def parameters (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : FlatParameters N where
  tau s := InexactRealizations.Flat.tau I N s
  alpha s := InexactRealizations.Flat.alpha I s
  beta s := InexactRealizations.Flat.beta I s
  terminalA := InexactRealizations.Flat.terminalA I N
  terminalB := InexactRealizations.Flat.terminalB I N

/-- as four actual in-place registers V, P, G, A. -/
def program (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : RegisterProgram 4 N :=
  (parameters I N).program

/-- Every recovery denominator is strictly positive. -/
theorem denominator_pos (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : 0 < 1 + (parameters I N).tau s := by
  have ht := InexactRealizations.Flat.tau_nonneg I N (by omega) s.val s.isLt
  change 0 < 1 + InexactRealizations.Flat.tau I N s
  linarith

/-- The actual physical program is translation normalized. -/
theorem normalized (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (program I N).TranslationNormalized :=
  (parameters I N).normalized (fun s => ne_of_gt (denominator_pos I N hN s))

/-- The affine extrapolated physical query polynomial. -/
def physicalQuery (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ[X] :=
  InexactRealizations.Flat.virtualPolynomial I s + C (InexactRealizations.Flat.tau I N s) *
    (InexactRealizations.Flat.virtualPolynomial I s - InexactRealizations.Flat.virtualPolynomial I (s-1))

/-- The symbolic oracle is multiplication by the physical spectral variable. -/
def polynomialOracle (N : ℕ) : Fin N → ℝ[X] → ℝ[X] := fun _ p => X * p

/-- Exact nominal recovery, including the separately initialized zero gradient. -/
theorem nominal_recovery (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) :
    (parameters I N).recoveredGradient s
      (if s.val = 0 then 0 else X * InexactRealizations.Flat.virtualPolynomial I (s.val-1))
      (X * physicalQuery I N s) = X * InexactRealizations.Flat.virtualPolynomial I s := by
  by_cases hs : s.val = 0
  · simp [FlatParameters.recoveredGradient, physicalQuery, parameters, hs,
      InexactRealizations.Flat.tau_zero I N (by omega)]
  · have hr := (parameters I N).recoveredGradient_linear s
      (ne_of_gt (denominator_pos I N hN s)) (LinearMap.mulLeft ℝ (X : ℝ[X]))
      (InexactRealizations.Flat.virtualPolynomial I s.val) (InexactRealizations.Flat.virtualPolynomial I (s.val-1))
    simpa only [hs, ite_false, LinearMap.mulLeft_apply, physicalQuery, parameters,
      Polynomial.smul_eq_C_mul] using hr

/-- The two virtual registers and gradient register throughout every nominal
prefix; the fourth register contains the preceding actual oracle answer. 
-/
theorem nominal_prefix (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (k : ℕ) (hk : k < N) :
    ∃ a : ℝ[X], ((program I N).runPrefix (polynomialOracle N) 1 k).vectors =
      ![InexactRealizations.Flat.virtualPolynomial I k,
        InexactRealizations.Flat.virtualPolynomial I (k-1),
        if k=0 then 0 else X * InexactRealizations.Flat.virtualPolynomial I (k-1), a] := by
  induction k with
  | zero =>
    refine ⟨0, ?_⟩
    simp [RegisterProgram.runPrefix, RegisterProgram.initialState, program,
      FlatParameters.program, InexactRealizations.Flat.virtualPolynomial_zero]
    ext i
    fin_cases i <;> simp
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih (by omega)
    have hstep := (parameters I N).stage_vectors ⟨k,by omega⟩
      (ne_of_gt (denominator_pos I N hN _)) (polynomialOracle N)
      (InexactRealizations.Flat.virtualPolynomial I k) (InexactRealizations.Flat.virtualPolynomial I (k-1))
      (if k=0 then 0 else X * InexactRealizations.Flat.virtualPolynomial I (k-1)) a
      (((program I N).runPrefix (polynomialOracle N) 1 k).calls)
    have hquery : InexactRealizations.Flat.virtualPolynomial I k + (parameters I N).tau ⟨k,by omega⟩ •
        (InexactRealizations.Flat.virtualPolynomial I k - InexactRealizations.Flat.virtualPolynomial I (k-1)) =
        physicalQuery I N k := by simp only [physicalQuery, parameters, Polynomial.smul_eq_C_mul]
    rw [hquery] at hstep
    simp only [polynomialOracle] at hstep
    rw [nominal_recovery I N hN ⟨k,by omega⟩] at hstep
    simp only [show k + 1 < N by omega, ite_true] at hstep
    have hnext :
        (1 + (parameters I N).beta ⟨k,by omega⟩) • InexactRealizations.Flat.virtualPolynomial I k -
        (parameters I N).beta ⟨k,by omega⟩ • InexactRealizations.Flat.virtualPolynomial I (k-1) -
        (parameters I N).alpha ⟨k,by omega⟩ • (X * InexactRealizations.Flat.virtualPolynomial I k) =
          InexactRealizations.Flat.virtualPolynomial I (k+1) := by
      simp only [parameters, Polynomial.smul_eq_C_mul]
      cases k with
      | zero => simp [InexactRealizations.Flat.beta, InexactRealizations.Flat.virtualPolynomial_one]
      | succ k =>
        simpa only [Nat.add_sub_cancel, Nat.add_assoc, mul_assoc] using
          (InexactRealizations.Flat.virtualPolynomial_step I k).symm
    rw [hnext] at hstep
    refine ⟨X * physicalQuery I N k, ?_⟩
    rw [RegisterProgram.runPrefix, dite_eq_left (show k < N by omega)]
    have hstate : (program I N).runPrefix (polynomialOracle N) 1 k =
        ⟨![InexactRealizations.Flat.virtualPolynomial I k, InexactRealizations.Flat.virtualPolynomial I (k-1),
          if k=0 then 0 else X * InexactRealizations.Flat.virtualPolynomial I (k-1),a],
          ((program I N).runPrefix (polynomialOracle N) 1 k).calls⟩ := by
      apply RegisterState.ext
      · exact ha
      · rfl
    rw [hstate]
    simpa only [program, Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ite_false] using hstep

/-- The physical symbolic query is extrapolated normalized U state. -/
theorem nominal_query (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : (program I N).queryAt (polynomialOracle N) 1 s = physicalQuery I N s := by
  obtain ⟨a, ha⟩ := nominal_prefix I N hN s.val s.isLt
  unfold RegisterProgram.queryAt
  rw [ha]
  change executeLinear ((parameters I N).program.before s) _ _ = _
  rw [FlatParameters.before_vectors]
  simp only [program, FlatParameters.program, parameters, physicalQuery,
    Matrix.cons_val_zero, Polynomial.smul_eq_C_mul]

/-- The literal final assignment returns the prescribed Chebyshev residual. -/
theorem nominal_output (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (program I N).output (polynomialOracle N) 1 = I.residual N := by
  let k := N-1
  have hk : k < N := by dsimp [k]; omega
  obtain ⟨a, ha⟩ := nominal_prefix I N hN k hk
  have hstep := (parameters I N).stage_vectors ⟨k,hk⟩
    (ne_of_gt (denominator_pos I N hN _)) (polynomialOracle N)
    (InexactRealizations.Flat.virtualPolynomial I k) (InexactRealizations.Flat.virtualPolynomial I (k-1))
    (if k=0 then 0 else X * InexactRealizations.Flat.virtualPolynomial I (k-1)) a
    (((program I N).runPrefix (polynomialOracle N) 1 k).calls)
  have hquery : InexactRealizations.Flat.virtualPolynomial I k + (parameters I N).tau ⟨k,hk⟩ •
      (InexactRealizations.Flat.virtualPolynomial I k - InexactRealizations.Flat.virtualPolynomial I (k-1)) =
      physicalQuery I N k := by simp only [physicalQuery, parameters, Polynomial.smul_eq_C_mul]
  rw [hquery] at hstep
  simp only [polynomialOracle] at hstep
  rw [nominal_recovery I N hN ⟨k,hk⟩] at hstep
  simp only [show ¬ k+1<N by dsimp [k]; omega, ite_false] at hstep
  have hstate : (program I N).runPrefix (polynomialOracle N) 1 k =
      ⟨![InexactRealizations.Flat.virtualPolynomial I k, InexactRealizations.Flat.virtualPolynomial I (k-1),
        if k=0 then 0 else X * InexactRealizations.Flat.virtualPolynomial I (k-1),a],
        ((program I N).runPrefix (polynomialOracle N) 1 k).calls⟩ := by
    apply RegisterState.ext
    · exact ha
    · rfl
  have hout : (program I N).output (polynomialOracle N) 1 =
      (1 + InexactRealizations.Flat.terminalA I N) • InexactRealizations.Flat.virtualPolynomial I k -
      InexactRealizations.Flat.terminalA I N • InexactRealizations.Flat.virtualPolynomial I (k-1) -
      InexactRealizations.Flat.terminalB I N • (X * InexactRealizations.Flat.virtualPolynomial I k) := by
    unfold RegisterProgram.output RegisterProgram.run
    have hn : (program I N).runPrefix (polynomialOracle N) 1 N =
        (program I N).runPrefix (polynomialOracle N) 1 (k+1) := by
      congr 1
      dsimp [k]
      omega
    rw [hn, RegisterProgram.runPrefix, dite_eq_left hk, hstate]
    exact congrFun hstep 1
  rw [hout]
  simp only [Polynomial.smul_eq_C_mul, k, show N-1-1=N-2 by omega]
  simpa only [mul_assoc] using (InexactRealizations.Flat.virtualPolynomial_terminal I N hN).symm

/-- Physical-to-chart substitution recovers exactly the displayed Flat query. -/
theorem physicalQuery_comp_chart (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) :
    (physicalQuery I N s).comp (InexactRealizations.GradedFamily.chart I) =
      InexactRealizations.Flat.queryPolynomial I N s := by
  have hv (k : ℕ) : (InexactRealizations.Flat.virtualPolynomial I k).comp
      (InexactRealizations.GradedFamily.chart I) = InexactRealizations.Flat.normalizedU I k := by
    rw [InexactRealizations.Flat.virtualPolynomial, comp_assoc,
      InexactRealizations.GradedFamily.coordinate_comp_chart, comp_X]
  simp only [physicalQuery, add_comp, mul_comp, sub_comp, C_comp, hv,
    InexactRealizations.Flat.queryPolynomial, map_add, map_one]
  ring

/-- The literal four-vector program has exactly the synthesized Flat history.
Use: this identifies every physical response, not only the noiseless terminal. 
-/
theorem history_eq (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (program I N).history (normalized I N hN) = InexactRealizations.Flat.history I N hN := by
  apply (InexactRealizations.Flat.queries I N (by omega)).realize_unique I
    (fun s => InexactRealizations.Flat.queryPolynomial_eta I N s)
  · change ((program I N).history (normalized I N hN)).terminal = I.residual N
    rw [← RegisterProgram.polynomial_output, ← nominal_output I N hN]
    rfl
  · intro s
    unfold InexactRealizations.History.chartQuery
    rw [← RegisterProgram.polynomial_query]
    change ((program I N).queryAt (polynomialOracle N) 1 s).comp _ = _
    rw [nominal_query I N hN s]
    exact physicalQuery_comp_chart I N s

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Every actual query equals the Flat causal history query, for
an arbitrary time-dependent oracle and any actual sequence of returned errors. 
-/
theorem query_eq_history (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) (s : Fin N) :
    (program I N).queryAt oracle initial s =
      (InexactRealizations.Flat.history I N hN).oracleQuery initial oracle s := by
  rw [RegisterProgram.query_eq_history _ (normalized I N hN), history_eq]

/-- The actual physical output equals the Flat history output for
every oracle stream. Use: all proved physical gains and risks apply to this code. 
-/
theorem output_eq_history (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) :
    (program I N).output oracle initial =
      (InexactRealizations.Flat.history I N hN).oracleOutput initial oracle := by
  rw [RegisterProgram.output_eq_history _ (normalized I N hN), history_eq]

/-- Exact additive response of the physical four-vector algorithm for arbitrary
linear Hessians and actual error streams, with no stochastic restrictions. 
-/
theorem physical_response (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (H : E →ₗ[ℝ] E) (initial : E) (noise : Fin N → E) :
    (program I N).output (fun s y => H y+noise s) initial =
      (Polynomial.aeval H (I.residual N)) initial +
      ∑ s, (Polynomial.aeval H ((InexactRealizations.Flat.history I N hN).response s)) (noise s) := by
  have he := InexactRealizations.Flat.history_exact I N hN
  change (InexactRealizations.Flat.history I N hN).terminal = I.residual N at he
  rw [output_eq_history, InexactRealizations.History.oracleOutput_linear,
    InexactRealizations.History.physical_response, he]

end
end InexactRealizations.Algorithms.Flat
