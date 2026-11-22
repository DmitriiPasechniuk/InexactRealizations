import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-! Observable information for the adaptive-method clause.
A method receives its own seed and the earlier oracle answers. The hidden
minimizer and the proof's enlarged noise filtration are not inputs. 
-/
namespace InexactRealizations.Probability
noncomputable section
open MeasureTheory

structure AdaptiveMethod (N : ℕ) (E U : Type*) [MeasurableSpace E] [MeasurableSpace U] where
  query : (s : Fin N) → U × (Fin s.val → E) → E
  query_measurable : ∀ s, Measurable (query s)
  output : U × (Fin N → E) → E
  output_measurable : Measurable output

namespace AdaptiveMethod
variable {N : ℕ} {E U : Type*} [MeasurableSpace E] [MeasurableSpace U]

def answersThrough [Zero E] (M : AdaptiveMethod N E U) (O : Fin N → E → E) (u : U) : ℕ → (Fin N → E)
  | 0 => 0
  | n + 1 =>
    if hn : n < N then
      Function.update (answersThrough M O u n) ⟨n, hn⟩
        (O ⟨n, hn⟩ (M.query ⟨n, hn⟩
          (u, fun j ↦ answersThrough M O u n ⟨j.val, j.isLt.trans hn⟩)))
    else answersThrough M O u n

def oracleOutput [Zero E] (M : AdaptiveMethod N E U) (O : Fin N → E → E) (u : U) : E :=
  M.output (u, answersThrough M O u N)

def observableOutput (M : AdaptiveMethod N ℝ U) (mu : ℝ) (p : U × (Fin N → ℝ)) : ℝ :=
  M.oracleOutput (fun s q ↦ mu * q - p.2 s) p.1

theorem measurable_answersThrough (M : AdaptiveMethod N ℝ U) (mu : ℝ) (n : ℕ) :
    Measurable (fun p : U × (Fin N → ℝ) ↦ M.answersThrough (fun s q ↦ mu * q - p.2 s) p.1 n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    by_cases hn : n < N
    · apply Measurable.of_eval
      intro s
      by_cases hs : s = (⟨n, hn⟩ : Fin N)
      · subst s
        simp only [answersThrough, hn, dite_true, Function.update_self]
        have hq : Measurable (fun p : U × (Fin N → ℝ) ↦
            M.query ⟨n, hn⟩ (p.1, fun j ↦
              M.answersThrough (fun s q ↦ mu * q - p.2 s) p.1 n ⟨j.val, j.isLt.trans hn⟩)) := by
          apply (M.query_measurable ⟨n, hn⟩).comp
          apply measurable_fst.prodMk
          exact Measurable.of_eval fun j ↦ (measurable_pi_apply _).comp ih
        exact (measurable_const.mul hq).sub ((measurable_pi_apply _).comp measurable_snd)
      · simp only [answersThrough, hn, dite_true, Function.update_of_ne hs]
        exact (measurable_pi_apply s).comp ih
    · simpa only [answersThrough, hn, dite_false] using ih

theorem measurable_observableOutput (M : AdaptiveMethod N ℝ U) (mu : ℝ) :
    Measurable (M.observableOutput mu) :=
  M.output_measurable.comp (measurable_fst.prodMk (M.measurable_answersThrough mu N))

end AdaptiveMethod
end
end InexactRealizations.Probability
