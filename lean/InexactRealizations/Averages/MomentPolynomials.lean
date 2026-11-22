import InexactRealizations.Averages.Prefix

/-! The single polynomial product identity needed to integrate the printed
Prefix moments: U_n^2-U_(n-1)^2=U_(2n). 
-/
namespace InexactRealizations.Averages
noncomputable section
open Polynomial Polynomial.Chebyshev

theorem secondKind_addition (n m : ℕ) :
    U ℝ ((n : ℤ) + m) = U ℝ (n : ℤ) * U ℝ (m : ℤ) - U ℝ ((n : ℤ) - 1) * U ℝ ((m : ℤ) - 1) := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one =>
    simp only [Nat.cast_one, sub_self, U_one, U_zero, mul_one]
    rw [U_add_one]
    ring
  | more m ih0 ih1 =>
    have hrec := U_add_two ℝ ((n : ℤ) + m)
    have hm := U_add_one ℝ (m : ℤ)
    have hh : ((n : ℤ) + m + 1) = (n : ℤ) + ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hh, ih1, ih0] at hrec
    push_cast at *
    simp only [add_sub_cancel_right] at hrec
    rw [show (n : ℤ) + (m + 2) = (n : ℤ) + m + 2 by ring, hrec,
      show (m : ℤ) + 2 - 1 = (m : ℤ) + 1 by ring, U_add_two ℝ (m : ℤ)]
    linear_combination (U ℝ ((n : ℤ) - 1)) * hm

theorem secondKind_square_difference (n : ℕ) :
    U ℝ (n : ℤ) ^ 2 - U ℝ ((n : ℤ) - 1) ^ 2 = U ℝ (2 * (n : ℤ)) := by
  rw [show 2 * (n : ℤ) = (n : ℤ) + n by ring, secondKind_addition]
  ring

end
end InexactRealizations.Averages
