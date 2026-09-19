import Catalan.Counting.Defs

set_option autoImplicit false
open scoped BigOperators
namespace Catalan.LatticeCount

private lemma cast_choose_three (r : ℕ) :
    (r.choose 3 : ℚ) = (r : ℚ) * (r - 1) * (r - 2) / 6 := by
  rcases r with _ | _ | r
  · norm_num [Nat.choose]
  · norm_num [Nat.choose]
  · have h := congrArg (fun k : ℕ => (k : ℚ))
      (Nat.descFactorial_eq_factorial_mul_choose (r + 2) 3)
    norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.cast_mul,
      Nat.cast_add] at h ⊢
    nlinarith only [h]

lemma countPolynomial_two (r : ℕ) :
    countPolynomial 2 r = 2 * r ^ 2 + 2 * r + 1 := by
  have he : (countPolynomial 2 r : ℚ) = 2 * (r : ℚ) ^ 2 + 2 * r + 1 := by
    norm_num [countPolynomial, Finset.sum_range_succ, Nat.cast_choose_two]
    ring
  exact_mod_cast he

lemma countPolynomial_three (r : ℕ) :
    3 * countPolynomial 3 r = 4 * r ^ 3 + 6 * r ^ 2 + 8 * r + 3 := by
  have he : (3 : ℚ) * (countPolynomial 3 r : ℚ) =
      4 * (r : ℚ) ^ 3 + 6 * r ^ 2 + 8 * r + 3 := by
    norm_num [countPolynomial, Finset.sum_range_succ, Nat.cast_choose_two, cast_choose_three]
    ring
  exact_mod_cast he

lemma countPolynomial_gt_two (r : ℕ) (hr : 9 ≤ r) :
    4 * 2 ^ 2 * (r + 1) < countPolynomial 2 r := by
  rw [countPolynomial_two]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hr
  nlinarith [sq_nonneg (t : ℤ)]

lemma countPolynomial_gt_three (r : ℕ) (hr : 5 ≤ r) :
    4 * 3 ^ 2 * (r + 1) < countPolynomial 3 r := by
  have he := countPolynomial_three r
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hr
  nlinarith only [he, Nat.zero_le (t ^ 3), Nat.zero_le (t ^ 2), Nat.zero_le t]

end Catalan.LatticeCount
