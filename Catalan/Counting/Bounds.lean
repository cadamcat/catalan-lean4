import Catalan.Counting.Defs

namespace Catalan.LatticeCount

open scoped BigOperators

private lemma choose_three_cast (n : ℕ) (hn : 2 ≤ n) :
    (n.choose 3 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) / 6 := by
  have hnat : (n - 2) * ((n - 1) * n) = 6 * n.choose 3 := by
    simpa [Nat.descFactorial_succ, Nat.factorial] using Nat.descFactorial_eq_factorial_mul_choose n 3
  have h := congrArg (fun k : ℕ => (k : ℚ)) hnat
  simp only [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_ofNat, Nat.cast_one] at h
  nlinarith only [h]

private lemma count_two_terms (n r : ℕ) (hn : 3 ≤ n) (hr : 3 ≤ r) :
    (n : ℚ) * ((n : ℚ) - 1) * r * ((r : ℚ) - 1) +
      (2 / 9 : ℚ) * ((n : ℚ) * ((n : ℚ) - 1) * r * ((r : ℚ) - 1)) *
        ((n : ℚ) - 2) * ((r : ℚ) - 2) ≤ (countPolynomial n r : ℚ) := by
  have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have hs : 4 * n.choose 2 * r.choose 2 + 8 * n.choose 3 * r.choose 3 ≤ countPolynomial n r := by
    have h := Finset.sum_le_sum_of_subset (f := fun k => 2 ^ k * n.choose k * r.choose k) hsub
    simpa [countPolynomial] using h
  have hq : (4 : ℚ) * (n.choose 2 : ℚ) * (r.choose 2 : ℚ) +
      8 * (n.choose 3 : ℚ) * (r.choose 3 : ℚ) ≤ (countPolynomial n r : ℚ) := by
    exact_mod_cast hs
  rw [Nat.cast_choose_two, Nat.cast_choose_two, choose_three_cast n (by omega),
    choose_three_cast r (by omega)] at hq
  convert hq using 1
  ring

lemma countPolynomial_gt (n r : ℕ) (hn : 11 ≤ n) (hr : 3 ≤ r) :
    4 * n ^ 2 * (r + 1) < countPolynomial n r
 := by
  have hnQ : (11 : ℚ) ≤ n := by exact_mod_cast hn
  have hrQ : (3 : ℚ) ≤ r := by exact_mod_cast hr
  have hn0 : (0 : ℚ) < n := by linarith
  have hr0 : (0 : ℚ) < (r : ℚ) + 1 := by linarith
  have hn1 : (0 : ℚ) ≤ (n : ℚ) - 1 := by linarith
  have hr1 : (0 : ℚ) ≤ (r : ℚ) - 1 := by linarith
  have hn2 : (0 : ℚ) ≤ (n : ℚ) - 2 := by linarith
  have hr2 : (0 : ℚ) ≤ (r : ℚ) - 2 := by linarith
  let T : ℚ := (n : ℚ) * ((n : ℚ) - 1) * r * ((r : ℚ) - 1)
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hT : (15 / 11 : ℚ) * n ^ 2 * ((r : ℚ) + 1) ≤ T := by
    calc
      (15 / 11 : ℚ) * n ^ 2 * ((r : ℚ) + 1) =
          (n : ℚ) * ((10 / 11 : ℚ) * n) * ((3 / 4 : ℚ) * ((r : ℚ) + 1)) * 2 := by ring
      _ ≤ T := by
        dsimp only [T]
        gcongr <;> linarith
  have hT3 : 2 * T ≤ (2 / 9 : ℚ) * T * ((n : ℚ) - 2) * ((r : ℚ) - 2) := by
    calc
      2 * T = (2 / 9 : ℚ) * T * 9 * 1 := by ring
      _ ≤ _ := by gcongr <;> first | positivity | linarith
  have hpos : (0 : ℚ) < (n : ℚ) ^ 2 * ((r : ℚ) + 1) := by positivity
  have hlow := count_two_terms n r (by omega) hr
  change T + (2 / 9 : ℚ) * T * ((n : ℚ) - 2) * ((r : ℚ) - 2) ≤ _ at hlow
  have hfinal : (4 : ℚ) * n ^ 2 * ((r : ℚ) + 1) < (countPolynomial n r : ℚ) := by
    nlinarith only [hT, hT3, hpos, hlow]
  exact_mod_cast hfinal

lemma countPolynomial_gt' (n r : ℕ) (hn : 5 ≤ n) (hr : 4 ≤ r) :
    4 * n ^ 2 * (r + 1) < countPolynomial n r
 := by
  have hnQ : (5 : ℚ) ≤ n := by exact_mod_cast hn
  have hrQ : (4 : ℚ) ≤ r := by exact_mod_cast hr
  have hn0 : (0 : ℚ) < n := by linarith
  have hr0 : (0 : ℚ) < (r : ℚ) + 1 := by linarith
  have hn1 : (0 : ℚ) ≤ (n : ℚ) - 1 := by linarith
  have hr1 : (0 : ℚ) ≤ (r : ℚ) - 1 := by linarith
  have hn2 : (0 : ℚ) ≤ (n : ℚ) - 2 := by linarith
  have hr2 : (0 : ℚ) ≤ (r : ℚ) - 2 := by linarith
  let T : ℚ := (n : ℚ) * ((n : ℚ) - 1) * r * ((r : ℚ) - 1)
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hT : (48 / 25 : ℚ) * n ^ 2 * ((r : ℚ) + 1) ≤ T := by
    calc
      (48 / 25 : ℚ) * n ^ 2 * ((r : ℚ) + 1) =
          (n : ℚ) * ((4 / 5 : ℚ) * n) * ((4 / 5 : ℚ) * ((r : ℚ) + 1)) * 3 := by ring
      _ ≤ T := by
        dsimp only [T]
        gcongr <;> linarith
  have hT3 : (4 / 3 : ℚ) * T ≤ (2 / 9 : ℚ) * T * ((n : ℚ) - 2) * ((r : ℚ) - 2) := by
    calc
      (4 / 3 : ℚ) * T = (2 / 9 : ℚ) * T * 3 * 2 := by ring
      _ ≤ _ := by gcongr <;> first | positivity | linarith
  have hpos : (0 : ℚ) < (n : ℚ) ^ 2 * ((r : ℚ) + 1) := by positivity
  have hlow := count_two_terms n r (by omega) (by omega)
  change T + (2 / 9 : ℚ) * T * ((n : ℚ) - 2) * ((r : ℚ) - 2) ≤ _ at hlow
  have hfinal : (4 : ℚ) * n ^ 2 * ((r : ℚ) + 1) < (countPolynomial n r : ℚ) := by
    nlinarith only [hT, hT3, hpos, hlow]
  exact_mod_cast hfinal

end Catalan.LatticeCount
