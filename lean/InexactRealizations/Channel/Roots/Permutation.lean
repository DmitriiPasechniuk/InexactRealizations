import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

namespace InexactRealizations.Channel.Roots
noncomputable section

/-- Root position after one literal LF interlacing/reflection step. -/
def reflectedHalf (m : ℕ) (e : Equiv.Perm (Fin m)) (p : Fin m × Fin 2) : Fin (m*2) :=
  ⟨if p.2.val=0 then (e p.1).val else m*2-1-(e p.1).val, by
    have h := (e p.1).isLt
    split_ifs <;> omega⟩

/-- The reflected halves are a bijection of all doubled root positions. -/
theorem reflectedHalf_bijective (m : ℕ) (e : Equiv.Perm (Fin m)) :
    Function.Bijective (reflectedHalf m e) := by
  constructor
  · rintro ⟨i,b⟩ ⟨j,c⟩ he
    have hv : (if b.val=0 then (e i).val else m*2-1-(e i).val) =
        (if c.val=0 then (e j).val else m*2-1-(e j).val) := congrArg Fin.val he
    have hi := (e i).isLt
    have hj := (e j).isLt
    fin_cases b <;> fin_cases c
    all_goals norm_num at hv
    · have heij : e i=e j := Fin.ext hv
      have hij := e.injective heij
      subst j
      rfl
    · omega
    · omega
    · have heij : e i=e j := Fin.ext (by omega)
      have hij := e.injective heij
      subst j
      rfl
  · intro j
    by_cases hj : j.val<m
    · refine ⟨(e.symm ⟨j.val,hj⟩, 0), ?_⟩
      apply Fin.ext
      simp [reflectedHalf]
    · have hr : m*2-1-j.val<m := by have := j.isLt; omega
      refine ⟨(e.symm ⟨m*2-1-j.val,hr⟩, 1), ?_⟩
      apply Fin.ext
      simp only [reflectedHalf, Equiv.apply_symm_apply]
      have := j.isLt
      norm_num
      omega

/-- One exact LF doubling: previous positions are interlaced with their reflection. -/
def doublePermutation (m : ℕ) (e : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m*2)) :=
  finProdFinEquiv.symm.trans (Equiv.ofBijective (reflectedHalf m e) (reflectedHalf_bijective m e))

/-- Literal recursive LF/fractal permutation at horizon 2^k. -/
def dyadicPermutation : (k : ℕ) → Equiv.Perm (Fin (2^k))
  | 0 => Equiv.refl _
  | k+1 => (finCongr (pow_succ 2 k)).trans
      ((doublePermutation (2^k) (dyadicPermutation k)).trans (finCongr (pow_succ 2 k).symm))

/-- The first dyadic root schedule starts with its sole root. -/
@[simp] theorem dyadicPermutation_zero : dyadicPermutation 0 = Equiv.refl _ := rfl

/-- The recursive configuration is an actual permutation, hence neither repeats nor loses a root. -/
theorem dyadicPermutation_bijective (k : ℕ) : Function.Bijective (dyadicPermutation k) :=
  (dyadicPermutation k).bijective

end
end InexactRealizations.Channel.Roots
