import Catalan.Classical.Euler.Sequence
import Catalan.Classical.Euler.NegativePell
import Catalan.Classical.Euler.QuarticTwo
import Catalan.Classical.Euler.Arithmetic

namespace Catalan.Euler

lemma quartic_pell_three (x y : ℤ) (h : x ^ 4 - 3 * y ^ 2 = 1) :
    (x = 1 ∨ x = -1) ∧ y = 0
 := by
  have hxcast : ((x.natAbs ^ 2 : ℕ) : ℤ) = x ^ 2 := by
    simp only [Nat.cast_pow, Int.natCast_natAbs, sq_abs]
  have hycast : (y.natAbs : ℤ) ^ 2 = y ^ 2 := by
    simp only [Int.natCast_natAbs, sq_abs]
  have hcomplete : (((x.natAbs ^ 2 : ℕ) : ℤ)) ^ 2 - 3 * (y.natAbs : ℤ) ^ 2 = 1 := by
    rw [hxcast, hycast]
    nlinarith only [h]
  obtain ⟨n, hnX, _⟩ := pell_complete (x.natAbs ^ 2) y.natAbs hcomplete
  have hX : (pellX n : ℤ) = x ^ 2 := by rw [← hnX, hxcast]
  have hnEven : Even n := by
    rcases Nat.even_or_odd n with he | ho
    · exact he
    · obtain ⟨j, hj⟩ := ho
      have hh := hX
      rw [hj, pell_x_odd, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at hh
      have hs := sq_sub_sq_eq_one x ((pellY j + pellY (j + 1) : ℕ) : ℤ)
        (by nlinarith only [hh])
      have hzero : pellY j + pellY (j + 1) = 0 := by exact_mod_cast hs.2
      have hpos := pell_y_pos (j + 1) (by omega)
      omega
  obtain ⟨k, hk⟩ := hnEven
  have hn2 : n = 2 * k := by omega
  have hdouble : (pellX (2 * k) : ℤ) + 1 = 2 * (pellX k : ℤ) ^ 2 := by
    exact_mod_cast pell_x_double k
  have hX2 : (pellX (2 * k) : ℤ) = x ^ 2 := by simpa only [hn2] using hX
  have hnegative : 2 * (pellX k : ℤ) ^ 2 - x ^ 2 = 1 := by
    nlinarith only [hdouble, hX2]
  have hkOdd : Odd (pellX k) := by
    have hmod : (2 : ZMod 4) * (pellX k : ZMod 4) ^ 2 - (x : ZMod 4) ^ 2 = 1 := by
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast, Int.cast_one]
        using congrArg (fun z : ℤ => (z : ZMod 4)) hnegative
    have hfinite : ∀ a b : ZMod 4, 2 * a ^ 2 - b ^ 2 = 1 → a.val % 2 = 1 := by decide
    have hv := hfinite (pellX k : ZMod 4) (x : ZMod 4) hmod
    rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4)] at hv
    exact Nat.odd_iff.mpr hv
  obtain ⟨m, hm⟩ := (pell_x_odd_iff k).mp hkOdd
  have hk2 : k = 2 * m := by omega
  have hdoublem : (pellX k : ℤ) + 1 = 2 * (pellX m : ℤ) ^ 2 := by
    rw [hk2]
    exact_mod_cast pell_x_double m
  obtain ⟨a, b, ha, _, hab, hforms⟩ :=
    negative_pell_two_param (pellX k : ℤ) |x| (Int.natCast_nonneg _) (abs_nonneg _)
      (by simpa only [sq_abs] using hnegative)
  have hasq : ∃ A : ℤ, 0 ≤ A ∧ a = A ^ 2 := by
    rcases hforms with hplus | hminus
    · have hcop : IsCoprime a (a + b) := by
        refine ⟨a + 2 * b, -2 * b, ?_⟩
        nlinarith only [hab]
      have hprod : a * (a + b) = (pellX m : ℤ) ^ 2 := by
        nlinarith only [hplus, hdoublem]
      exact sq_of_nonneg_coprime_product a (a + b) (pellX m : ℤ) ha hcop hprod
    · have hcop : IsCoprime a (a - b) := by
        refine ⟨a - 2 * b, 2 * b, ?_⟩
        nlinarith only [hab]
      have hprod : a * (a - b) = (pellX m : ℤ) ^ 2 := by
        nlinarith only [hminus, hdoublem]
      exact sq_of_nonneg_coprime_product a (a - b) (pellX m : ℤ) ha hcop hprod
  obtain ⟨A, _, haA⟩ := hasq
  have hquartic : A ^ 4 - 2 * b ^ 2 = 1 := by
    rw [haA] at hab
    nlinarith only [hab]
  obtain ⟨hA, hb0⟩ := quartic_pell_two A b hquartic
  have ha1 : a = 1 := by
    rcases hA with hA | hA <;> simp only [hA] at haA <;> norm_num at haA ⊢ <;> exact haA
  have hXk : (pellX k : ℤ) = 1 := by
    rcases hforms with hplus | hminus
    · simpa [ha1, hb0] using hplus
    · simpa [ha1, hb0] using hminus
  have hx2 : x ^ 2 = 1 := by nlinarith only [hnegative, hXk]
  have hxpm := (sq_sub_sq_eq_one x 0 (by simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using hx2)).1
  refine ⟨hxpm, ?_⟩
  nlinarith only [h, hx2, sq_nonneg y]

end Catalan.Euler
