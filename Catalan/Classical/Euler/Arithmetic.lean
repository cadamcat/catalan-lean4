module

public import Mathlib

/-!
# `Catalan.Classical.Euler.Arithmetic`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Catalan.Euler

lemma sq_of_nonneg_coprime_product (a b c : ℤ) (ha : 0 ≤ a)
    (hab : IsCoprime a b) (h : a * b = c ^ 2) :
    ∃ r : ℤ, 0 ≤ r ∧ a = r ^ 2 := by
  obtain ⟨r, hr | hr⟩ := Int.sq_of_isCoprime hab h
  · exact ⟨|r|, abs_nonneg r, by simpa only [sq_abs] using hr⟩
  · exact ⟨0, le_rfl, by nlinarith [sq_nonneg r]⟩

lemma sq_sub_sq_eq_one (a b : ℤ) (h : a ^ 2 - b ^ 2 = 1) :
    (a = 1 ∨ a = -1) ∧ b = 0 := by
  have hm : (a - b) * (a + b) = 1 := by nlinarith
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨Or.inl (by omega), by omega⟩
  · exact ⟨Or.inr (by omega), by omega⟩

lemma euler_factors (x y : ℤ) (h : x ^ 2 = y ^ 3 + 1) :
    (y + 1) * (y ^ 2 - y + 1) = x ^ 2 := by
  nlinarith

lemma euler_y_pos (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 2 = y ^ 3 + 1) : 0 < y := by
  have hpoly : 0 < y ^ 2 - y + 1 := by nlinarith [sq_nonneg (2 * y - 1)]
  have hf := euler_factors x y h
  have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hyp : 0 < y + 1 := (mul_pos_iff_of_pos_right hpoly).mp (hf ▸ hx2)
  omega

lemma sq_eq_quadratic (y a : ℤ) (hy : 0 ≤ y) (ha : 0 ≤ a)
    (h : y ^ 2 - y + 1 = a ^ 2) : y = 0 ∨ y = 1 := by
  by_contra! hn
  have hy2 : 2 ≤ y := by omega
  have hlow : (y - 1) ^ 2 < a ^ 2 := by nlinarith
  have hhigh : a ^ 2 < y ^ 2 := by nlinarith
  have haLower : y - 1 < a := by nlinarith
  have haUpper : a < y := by nlinarith
  omega

lemma euler_three_square_factors
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ 2 = y ^ 3 + 1) (h3 : (3 : ℤ) ∣ y + 1) :
    ∃ a b : ℤ, 0 < a ∧ 0 ≤ b ∧ y + 1 = 3 * a ^ 2 ∧ y ^ 2 - y + 1 = 3 * b ^ 2 := by
  have hypos := euler_y_pos x y hx hy h
  obtain ⟨t, ht⟩ := h3
  have htpos : 0 < t := by omega
  have hquad : y ^ 2 - y + 1 = 3 * (3 * t ^ 2 - 3 * t + 1) := by
    have hy' : y = 3 * t - 1 := by omega
    rw [hy']
    ring
  have hf := euler_factors x y h
  rw [ht, hquad] at hf
  have h3x : (3 : ℤ) ∣ x := by
    apply (Int.prime_three.dvd_of_dvd_pow)
    exact ⟨t * (3 * (3 * t ^ 2 - 3 * t + 1)), by simpa only [mul_assoc] using hf.symm⟩
  obtain ⟨u, hu⟩ := h3x
  have hprod : t * (3 * t ^ 2 - 3 * t + 1) = u ^ 2 := by
    rw [hu] at hf
    nlinarith
  have hcop : IsCoprime t (3 * t ^ 2 - 3 * t + 1) :=
    ⟨3 - 3 * t, 1, by ring⟩
  have hB : 0 ≤ 3 * t ^ 2 - 3 * t + 1 := by nlinarith [sq_nonneg (2 * t - 1)]
  obtain ⟨a, ha, hta⟩ := sq_of_nonneg_coprime_product t _ u htpos.le hcop hprod
  obtain ⟨b, hb, hbb⟩ := sq_of_nonneg_coprime_product _ t u hB hcop.symm (by rwa [mul_comm])
  refine ⟨a, b, ?_, hb, ?_, ?_⟩
  · nlinarith [hta]
  · rw [ht, hta]
  · rw [hquad, hbb]

lemma int_sq_ne_two (x : ℤ) : x ^ 2 ≠ 2 := by
  intro h
  have h4 : (x : ZMod 4) ^ 2 = 2 := by
    simpa only [Int.cast_pow, Int.cast_ofNat] using congrArg (fun z : ℤ => (z : ZMod 4)) h
  exact (by decide : ∀ z : ZMod 4, z ^ 2 ≠ 2) (x : ZMod 4) h4

lemma euler_three_dvd_y_add_one
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ 2 = y ^ 3 + 1) :
    (3 : ℤ) ∣ y + 1 := by
  by_contra h3
  have hcop0 : IsCoprime (y + 1) (3 : ℤ) :=
    ((Int.prime_three.coprime_iff_not_dvd).mpr h3).symm
  obtain ⟨a, b, hab⟩ := hcop0
  have hcop : IsCoprime (y + 1) (y ^ 2 - y + 1) := by
    refine ⟨a - b * (y - 2), b, ?_⟩
    linear_combination hab
  have hpoly : 0 ≤ y ^ 2 - y + 1 := by nlinarith [sq_nonneg (2 * y - 1)]
  obtain ⟨r, hr, hsq⟩ := sq_of_nonneg_coprime_product _ _ x hpoly hcop.symm
    (by simpa only [mul_comm] using euler_factors x y h)
  rcases sq_eq_quadratic y r (euler_y_pos x y hx hy h).le hr hsq with h0 | h1
  · exact hy h0
  · apply int_sq_ne_two x
    simpa only [h1, one_pow, one_add_one_eq_two] using h

end Catalan.Euler
