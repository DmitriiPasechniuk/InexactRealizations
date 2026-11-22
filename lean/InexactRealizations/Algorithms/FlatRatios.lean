import InexactRealizations.Algorithms.Flat

/-! Current Algorithm1: compute normalized ratios, never the exponentially
large exterior U values. Every scalar is identified with the original
physical four-register Flat program. 
-/
namespace InexactRealizations.Algorithms.Flat
noncomputable section
open InexactRealizations.Flat

def ratioU (I : InexactRealizations.Operators.SpectralInterval) : ℕ → ℝ
  | 0 => 1 / (2 * I.eta)
  | j + 1 => 1 / (2 * I.eta - ratioU I j)

theorem ratioU_eq (I : InexactRealizations.Operators.SpectralInterval) (j : ℕ) :
    ratioU I j = u I j / u I (j + 1) := by
  induction j with
  | zero => simp [ratioU]
  | succ j ih =>
    rw [ratioU, ih, show j + 1 + 1 = j + 2 by omega, u_add_two]
    have hp := (u_pos I (j + 1)).ne'
    have hd : 2 * I.eta * u I (j + 1) - u I j ≠ 0 := by rw [← u_add_two]; exact (u_pos I (j + 2)).ne'
    field_simp

theorem ratioU_unit (I : InexactRealizations.Operators.SpectralInterval) (j : ℕ) :
    0 < ratioU I j ∧ ratioU I j < 1 := by
  rw [ratioU_eq]
  exact ⟨div_pos (u_pos I j) (u_pos I (j + 1)), (div_lt_one (u_pos I (j + 1))).mpr (u_growth I j).2⟩

theorem ratioU_denominator_pos (I : InexactRealizations.Operators.SpectralInterval) (j : ℕ) :
    0 < 2 * I.eta - ratioU I j := by linarith only [I.eta_gt_one, (ratioU_unit I j).2]

def scaledU (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => scaledU I N m * ratioU I (N - 2 - m)

theorem scaledU_eq (I : InexactRealizations.Operators.SpectralInterval) {N m : ℕ} (hm : m < N) :
    scaledU I N m = u I (N - 1 - m) / u I (N - 1) := by
  induction m with
  | zero => simp only [scaledU, Nat.sub_zero, div_self (u_pos I _).ne']
  | succ m ih =>
    rw [scaledU, ih (by omega), ratioU_eq]
    have hi : N - 2 - m + 1 = N - 1 - m := by omega
    have hj : N - 1 - (m + 1) = N - 2 - m := by omega
    rw [hi, hj]
    field_simp [(u_pos I (N - 1)).ne', (u_pos I (N - 1 - m)).ne']

def ratioPrefix (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : ℕ → ℝ
  | 0 => 1 / 2
  | m + 1 => ratioPrefix I N m + scaledU I N (m + 1)

theorem ratioPrefix_eq (I : InexactRealizations.Operators.SpectralInterval) {N m : ℕ} (hm : m < N) :
    ratioPrefix I N m = prefixMass I N m / u I (N - 1) := by
  induction m with
  | zero =>
    rw [ratioPrefix]
    have hp : prefixMass I N 0 = u I (N - 1) / 2 := by simp [prefixMass, mass]
    rw [hp]
    field_simp [(u_pos I (N - 1)).ne']
  | succ m ih =>
    rw [ratioPrefix, ih (by omega), scaledU_eq I hm, prefixMass_succ]
    have hne : m + 1 ≠ 0 := by omega
    simp only [mass, ite_eq_right hne]
    ring

def ratioMass (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : ℝ := ratioPrefix I N (N - 1) / N

theorem ratioMass_eq (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 0 < N) :
    ratioMass I N = unitMass I N / u I (N - 1) := by
  rw [ratioMass, ratioPrefix_eq I (by omega : N - 1 < N)]
  unfold unitMass totalMass
  ring

theorem ratioMass_pos (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 0 < N) :
    0 < ratioMass I N := by
  rw [ratioMass_eq I hN]
  exact div_pos (unitMass_pos I N hN) (u_pos I (N - 1))

def ratioTau (I : InexactRealizations.Operators.SpectralInterval) (N s : ℕ) : ℝ :=
  ratioPrefix I N (N - 1 - s) / ratioMass I N - (N - 1 - s : ℕ) - 1

theorem ratioTau_eq (I : InexactRealizations.Operators.SpectralInterval) {N : ℕ} (hN : 0 < N)
    {s : ℕ} (hs : s < N) : ratioTau I N s = InexactRealizations.Flat.tau I N s := by
  rw [ratioTau, ratioPrefix_eq I (by omega : N - 1 - s < N), ratioMass_eq I hN]
  unfold InexactRealizations.Flat.tau reservoir
  field_simp [(u_pos I (N - 1)).ne', (unitMass_pos I N hN).ne']

def ratioParameters (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : FlatParameters N where
  tau s := ratioTau I N s
  alpha s := if s.val = 0 then 2 / (I.L + I.mu) else 4 * ratioU I s / I.delta
  beta s := if s.val = 0 then 0 else ratioU I (s.val - 1) * ratioU I s
  terminalA := ratioU I (N - 2) / (I.eta - ratioU I (N - 2))
  terminalB := 2 / (I.delta * (I.eta - ratioU I (N - 2)))

theorem ratio_terminal_denominator_pos (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) :
    0 < I.eta - ratioU I (N - 2) := by linarith only [I.eta_gt_one, (ratioU_unit I (N - 2)).2]

theorem ratioParameters_eq (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    ratioParameters I N = parameters I N := by
  have hu := fun j ↦ (u_pos I j).ne'
  have hd := I.delta_pos.ne'
  have hC : I.eta * u I (N - 1) - u I (N - 2) = I.den N := by
    have hh := preparedDen_eq I N hN
    simpa only [preparedDen, preparedU_eq] using hh
  have hnm : N - 2 + 1 = N - 1 := by omega
  have hraw : I.eta * u I (N - 1) - u I (N - 2) ≠ 0 := by rw [hC]; exact I.den_ne N
  dsimp only [ratioParameters, parameters]
  congr 1
  · funext s
    exact ratioTau_eq I (by omega) s.isLt
  · funext s
    dsimp only [InexactRealizations.Flat.alpha]
    split_ifs
    · rfl
    · rw [ratioU_eq]
      field_simp [hu, hd]
  · funext s
    dsimp only [InexactRealizations.Flat.beta]
    split_ifs with hs
    · rfl
    · rw [ratioU_eq, ratioU_eq, show s.val - 1 + 1 = s.val by omega]
      field_simp [hu]
  · dsimp only [terminalA]
    rw [ratioU_eq, hnm, ← hC]
    field_simp [hu, hraw]
  · dsimp only [terminalB]
    rw [ratioU_eq, hnm, ← hC]
    field_simp [hu, hraw, hd]

def ratioProgram (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) : RegisterProgram 4 N :=
  (ratioParameters I N).program

theorem ratioProgram_eq (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    ratioProgram I N = program I N := by rw [ratioProgram, ratioParameters_eq I N hN]; rfl

theorem ratioProgram_query {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) (s : Fin N) :
    (ratioProgram I N).queryAt oracle initial s = (InexactRealizations.Flat.history I N hN).oracleQuery initial oracle s := by
  rw [ratioProgram_eq I N hN]
  exact query_eq_history I N hN oracle initial s

theorem ratioProgram_output {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : InexactRealizations.Operators.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (oracle : Fin N → E → E) (initial : E) :
    (ratioProgram I N).output oracle initial = (InexactRealizations.Flat.history I N hN).oracleOutput initial oracle := by
  rw [ratioProgram_eq I N hN]
  exact output_eq_history I N hN oracle initial

end
end InexactRealizations.Algorithms.Flat
