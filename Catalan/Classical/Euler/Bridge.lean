module

public import Catalan.Classical.Euler.Sequence
public import Catalan.Classical.Euler.Arithmetic

/-!
# `Catalan.Classical.Euler.Bridge`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Catalan.Euler

lemma pell_complete_int (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ^ 2 - 3 * y ^ 2 = 1) :
    ∃ n : ℕ, x = (pellX n : ℤ) ∧ y = (pellY n : ℤ) := by
  have hn : (x.natAbs : ℤ) ^ 2 - 3 * (y.natAbs : ℤ) ^ 2 = 1 := by
    simpa only [Int.natCast_natAbs, sq_abs] using h
  obtain ⟨n, hxn, hyn⟩ := pell_complete x.natAbs y.natAbs hn
  refine ⟨n, ?_, ?_⟩
  · simpa only [Int.natCast_natAbs, abs_of_nonneg hx] using
      congrArg (fun a : ℕ => (a : ℤ)) hxn
  · simpa only [Int.natCast_natAbs, abs_of_nonneg hy] using
      congrArg (fun a : ℕ => (a : ℤ)) hyn

lemma euler_solution_pell
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ 2 = y ^ 3 + 1) :
    ∃ a n : ℕ, y + 1 = 3 * (a : ℤ) ^ 2 ∧ pellY n + 1 = 2 * a ^ 2 := by
  obtain ⟨a, b, ha, hb, hya, hquad⟩ := euler_three_square_factors x y hx hy h
    (euler_three_dvd_y_add_one x y hx hy h)
  have hy' : y = 3 * a ^ 2 - 1 := by linarith
  have hb' : b ^ 2 = 3 * a ^ 4 - 3 * a ^ 2 + 1 := by
    rw [hy'] at hquad
    nlinarith only [hquad]
  have hPell : (2 * b) ^ 2 - 3 * (2 * a ^ 2 - 1) ^ 2 = 1 := by
    nlinarith only [hb']
  have hYpos : 0 ≤ 2 * a ^ 2 - 1 := by
    have h1 : 1 ≤ a := ha
    nlinarith
  obtain ⟨n, hXn, hYn⟩ := pell_complete_int (2 * b) (2 * a ^ 2 - 1)
    (by positivity) hYpos hPell
  refine ⟨a.natAbs, n, ?_, ?_⟩
  · simpa only [Int.natCast_natAbs, sq_abs] using hya
  · have he : (pellY n : ℤ) + 1 = 2 * (a.natAbs : ℤ) ^ 2 := by
      rw [Int.natCast_natAbs, sq_abs]
      linarith only [hYn]
    exact_mod_cast he

end Catalan.Euler
