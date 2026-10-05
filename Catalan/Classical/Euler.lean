module

public import Catalan.Classical.Euler.Bridge
public import Catalan.Classical.Euler.QuarticThree
public import Catalan.Classical.Euler.SquareIndex

/-!
# `Catalan.Classical.Euler`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Catalan.Euler

lemma pell_x_square_index_zero (n a : ℕ) (h : pellX n = a ^ 2) : n = 0 := by
  have hp := pell_identity n
  rw [h, Nat.cast_pow] at hp
  have hquartic : (a : ℤ) ^ 4 - 3 * (pellY n : ℤ) ^ 2 = 1 := by
    nlinarith only [hp]
  obtain ⟨ha, _⟩ := quartic_pell_three (a : ℤ) (pellY n : ℤ) hquartic
  have ha1 : a = 1 := by
    rcases ha with ha | ha <;> omega
  apply (pell_x_eq_one_iff n).mp
  simpa only [ha1, one_pow] using h

lemma pell_y_plus_one_twice_square (n a : ℕ)
    (h : pellY n + 1 = 2 * a ^ 2) : n = 1 :=
  pell_y_plus_one_twice_square_of_x_square_trivial pell_x_square_index_zero n a h

end Catalan.Euler

namespace Catalan

theorem euler_square_cube (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 2 = y ^ 3 + 1) :
    (x = 3 ∨ x = -3) ∧ y = 2 := by
  obtain ⟨a, n, hya, hn⟩ := Euler.euler_solution_pell x y hx hy h
  have hn1 := Euler.pell_y_plus_one_twice_square n a hn
  have hY1 : Euler.pellY 1 = 1 := by norm_num [Euler.pellY, Pell.yn_succ]
  rw [hn1, hY1] at hn
  have ha : a ^ 2 = 1 := by omega
  have haZ : (a : ℤ) ^ 2 = 1 := by exact_mod_cast ha
  have hy2 : y = 2 := by rw [haZ] at hya; omega
  refine ⟨?_, hy2⟩
  have hx9 : x ^ 2 = (3 : ℤ) ^ 2 := by norm_num [hy2] at h ⊢; exact h
  exact eq_or_eq_neg_of_sq_eq_sq x 3 hx9

end Catalan
