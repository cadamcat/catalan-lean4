module

public import Catalan.Classical.Euler.Defs
public import Mathlib

/-!
# `Catalan.Classical.Euler.Sequence`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan.Euler

private lemma pell_x_step (n : ℕ) : pellX (n + 1) = pellX n * 2 + 3 * pellY n := by
  exact Pell.xn_succ (by decide : 1 < 2) n

private lemma pell_y_step (n : ℕ) : pellY (n + 1) = pellX n + pellY n * 2 := by
  exact Pell.yn_succ (by decide : 1 < 2) n

lemma pell_identity (n : ℕ) :
    (pellX n : ℤ) ^ 2 - 3 * (pellY n : ℤ) ^ 2 = 1 := by
  have h := Pell.pell_eqz (by decide : 1 < 2) n
  change (pellX n : ℤ) * pellX n - 3 * pellY n * pellY n = 1 at h
  nlinarith only [h]

lemma pell_complete (x y : ℕ) (h : (x : ℤ) ^ 2 - 3 * (y : ℤ) ^ 2 = 1) :
    ∃ n : ℕ, x = pellX n ∧ y = pellY n := by
  have hnat : x * x = 3 * y * y + 1 := by
    have he : (x : ℤ) * x = 3 * y * y + 1 := by nlinarith only [h]
    exact_mod_cast he
  apply Pell.eq_pell (by decide : 1 < 2)
  change x * x - 3 * y * y = 1
  omega

lemma pell_x_double (n : ℕ) : pellX (2 * n) + 1 = 2 * pellX n ^ 2 := by
  have hadd := Pell.xn_add (by decide : 1 < 2) n n
  change pellX (n + n) = pellX n * pellX n + 3 * pellY n * pellY n at hadd
  have hnat : pellX n ^ 2 = 3 * pellY n ^ 2 + 1 := by
    have he : (pellX n : ℤ) ^ 2 = 3 * (pellY n : ℤ) ^ 2 + 1 := by
      nlinarith only [pell_identity n]
    exact_mod_cast he
  rw [← two_mul] at hadd
  nlinarith only [hadd, hnat]

lemma pell_y_double (n : ℕ) : pellY (2 * n) = 2 * pellX n * pellY n := by
  have hadd := Pell.yn_add (by decide : 1 < 2) n n
  change pellY (n + n) = pellX n * pellY n + pellY n * pellX n at hadd
  rw [← two_mul] at hadd
  nlinarith only [hadd]

lemma pell_x_odd (n : ℕ) : pellX (2 * n + 1) = (pellY n + pellY (n + 1)) ^ 2 + 1 := by
  have hnat : pellX n ^ 2 = 3 * pellY n ^ 2 + 1 := by
    have he : (pellX n : ℤ) ^ 2 = 3 * (pellY n : ℤ) ^ 2 + 1 := by
      nlinarith only [pell_identity n]
    exact_mod_cast he
  rw [pell_x_step, pell_y_step, pell_y_double]
  nlinarith only [pell_x_double n, hnat]

lemma pell_y_odd (n : ℕ) : pellY (2 * n + 1) + 1 = 2 * pellX n * pellY (n + 1) := by
  rw [pell_y_step (2 * n), pell_y_step n, pell_y_double]
  nlinarith only [pell_x_double n]

lemma pell_x_odd_iff (n : ℕ) : Odd (pellX n) ↔ Even n := by
  cases n with
  | zero => simp [pellX]
  | succ n =>
      have hy := Pell.yn_modEq_two (by decide : 1 < 2) n
      change pellY n % 2 = n % 2 at hy
      have hx := pell_x_step n
      simp only [Nat.odd_iff, Nat.even_iff]
      omega

lemma pell_y_odd_iff (n : ℕ) : Odd (pellY n) ↔ Odd n := by
  have h := Pell.yn_modEq_two (by decide : 1 < 2) n
  change pellY n % 2 = n % 2 at h
  simp only [Nat.odd_iff, h]

lemma pell_x_eq_one_iff (n : ℕ) : pellX n = 1 ↔ n = 0 := by
  change Pell.xn (by decide : 1 < 2) n = Pell.xn (by decide : 1 < 2) 0 ↔ n = 0
  exact (Pell.strictMono_x (by decide : 1 < 2)).injective.eq_iff

lemma pell_y_pos (n : ℕ) (hn : 0 < n) : 0 < pellY n := by
  exact Pell.strictMono_y (by decide : 1 < 2) hn

lemma pell_xy_coprime (n : ℕ) : Nat.Coprime (pellX n) (pellY n) := by
  exact Pell.xy_coprime (by decide : 1 < 2) n

end Catalan.Euler

