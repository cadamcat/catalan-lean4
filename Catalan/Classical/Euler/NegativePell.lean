module

public import Mathlib

/-!
# `Catalan.Classical.Euler.NegativePell`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan.Euler

lemma negative_pell_two_param (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : 2 * x ^ 2 - y ^ 2 = 1) :
    ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧ a ^ 2 - 2 * b ^ 2 = 1 ∧
      (x = 2 * a ^ 2 - 1 + 2 * a * b ∨
       x = 2 * a ^ 2 - 1 - 2 * a * b) := by
  have hxpos : 0 < x := by nlinarith [sq_nonneg y]
  have hyodd : Odd y := by
    apply Int.odd_iff.mpr
    have hmod := congrArg (fun z : ℤ => z % 2) h
    have hcases : y % 2 = 0 ∨ y % 2 = 1 := by omega
    rcases hcases with heven | hodd
    · norm_num [pow_two, Int.sub_emod, Int.mul_emod, heven] at hmod
    · exact hodd
  obtain ⟨t, ht⟩ := hyodd
  have ht0 : 0 ≤ t := by omega
  have htriple : PythagoreanTriple t (t + 1) x := by
    change t * t + (t + 1) * (t + 1) = x * x
    rw [ht] at h
    nlinarith
  have hcop : Int.gcd t (t + 1) = 1 := by
    apply Int.isCoprime_iff_gcd_eq_one.mp
    exact ⟨-1, 1, by ring⟩
  obtain ⟨m, n, hlegs, hsum, _, _⟩ :=
    PythagoreanTriple.coprime_classification.mp ⟨htriple, hcop⟩
  have hsum' : x = m ^ 2 + n ^ 2 := by
    rcases hsum with hsum | hsum
    · exact hsum
    · nlinarith [sq_nonneg m, sq_nonneg n]
  have hprod0 : 0 ≤ 2 * m * n := by
    rcases hlegs with hlegs | hlegs <;> omega
  have hprod : 2 * |m| * |n| = 2 * m * n := by
    calc
      2 * |m| * |n| = |2 * m * n| := by simp only [abs_mul]; norm_num
      _ = 2 * m * n := abs_of_nonneg hprod0
  have hsq : n ^ 2 ≤ m ^ 2 := by
    rcases hlegs with hlegs | hlegs <;> omega
  have habs : |n| ≤ |m| := sq_le_sq.mp hsq
  have hsumAbs : x = |m| ^ 2 + |n| ^ 2 := by simpa only [sq_abs] using hsum'
  rcases hlegs with hlegs | hlegs
  · have hdiff : 2 * |m| * |n| - (|m| ^ 2 - |n| ^ 2) = 1 := by
      rw [hprod, sq_abs, sq_abs]
      omega
    refine ⟨|m| + |n|, |m|, by positivity, abs_nonneg _, ?_, Or.inr ?_⟩
    · nlinarith
    · nlinarith
  · have hdiff : (|m| ^ 2 - |n| ^ 2) - 2 * |m| * |n| = 1 := by
      rw [hprod, sq_abs, sq_abs]
      omega
    refine ⟨|m| - |n|, |n|, sub_nonneg.mpr habs, abs_nonneg _, ?_, Or.inl ?_⟩
    · nlinarith
    · nlinarith

end Catalan.Euler

