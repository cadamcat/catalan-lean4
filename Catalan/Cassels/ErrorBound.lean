module

public import Catalan.Cassels.Remainder

/-!
# `Catalan.Cassels.ErrorBound`

Part of the Catalan formalization.
-/

@[expose] public section

open scoped BigOperators

namespace Catalan

lemma cassels_index_mul_gt (p q : ℕ) (hq : 0 < q) :
    p < casselsIndex p q * q := by
  have hmod := Nat.mod_lt p hq
  have hdecomp := Nat.mod_add_div p q
  unfold casselsIndex
  nlinarith

lemma cassels_scaled_power (a : ℝ) (ha : a ≠ 0) (q m k : ℕ) (hk : k ≤ m) :
    a ^ (m * q) * (1 / a ^ q) ^ k = a ^ (q * (m - k)) := by
  have he : q * (m - k) + q * k = m * q := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hk, Nat.mul_comm]
  rw [one_div, inv_pow, ← pow_mul, ← he, pow_add]
  exact mul_inv_cancel_right₀ (pow_ne_zero _ ha) _

lemma cassels_error_real_identity (p q : ℕ) (a y : ℤ)
    (ha : (a : ℝ) ≠ 0) (hmq : p ≤ casselsIndex p q * q)
    (hF : casselsF p q (1 / (a : ℝ) ^ q) = (y : ℝ) / (a : ℝ) ^ p) :
    (casselsError p q a y : ℝ) =
      (a : ℝ) ^ (casselsIndex p q * q) *
        (casselsF p q (1 / (a : ℝ) ^ q) -
          casselsTaylor p q (casselsIndex p q) (1 / (a : ℝ) ^ q)) := by
  unfold casselsError casselsTaylor
  push_cast
  rw [hF, mul_sub, Finset.mul_sum]
  congr 1
  · have he := Nat.sub_add_cancel hmq
    conv_rhs => rw [← he, pow_add]
    field_simp
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ casselsIndex p q := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [← mul_assoc, mul_comm ((a : ℝ) ^ _) (casselsCoeff p q k : ℝ), mul_assoc,
      cassels_scaled_power (a : ℝ) ha q (casselsIndex p q) k hk']

lemma cassels_root_identification (p q : ℕ) (hpodd : Odd p) (hqodd : Odd q)
    (hq0 : q ≠ 0) (x y a : ℝ) (ha : a ≠ 0)
    (hxa : x - 1 = a ^ q) (h : x ^ p = y ^ q + 1)
    (ht : |1 / a ^ q| ≤ (1 : ℝ) / 2) :
    casselsF p q (1 / a ^ q) = y / a ^ p := by
  have hx : 1 + 1 / a ^ q = x / a ^ q := by
    apply (eq_div_iff (pow_ne_zero _ ha)).mpr
    field_simp
    linarith
  have he : (y / a ^ p) ^ q = (1 + 1 / a ^ q) ^ p - (1 / a ^ q) ^ p := by
    rw [hx]
    simp only [div_pow, one_pow, ← pow_mul, Nat.mul_comm p q]
    rw [← sub_div]
    congr 1
    linarith
  obtain ⟨hL, _, hB⟩ := cassels_root_inputs_lower p hpodd (1 / a ^ q) ht
  have hy : 0 < y / a ^ p := hqodd.pow_pos_iff.mp (he ▸ hL.trans_le hB)
  unfold casselsF
  rw [← he, one_div]
  exact Real.pow_rpow_inv_natCast hy.le hq0

lemma cassels_abs_power_lower (a : ℝ) (q : ℕ) (ha : 2 ≤ |a|) (hq : 3 ≤ q) :
    8 ≤ |a| ^ q := by
  have h1 : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ q := pow_le_pow_right₀ (by norm_num) hq
  have h2 : (2 : ℝ) ^ q ≤ |a| ^ q := pow_le_pow_left₀ (by norm_num) ha q
  norm_num at h1
  exact h1.trans h2

lemma cassels_abs_x_bounds (a x : ℝ) (q : ℕ) (hx : x - 1 = a ^ q) :
    |a| ^ q - 1 ≤ |x| ∧ |x| ≤ |a| ^ q + 1 := by
  have h1 := abs_sub x 1
  have h2 := abs_add_le (x - 1) 1
  rw [hx, abs_pow, abs_one] at h1
  rw [sub_add_cancel, hx, abs_pow, abs_one] at h2
  exact ⟨by linarith, h2⟩

lemma cassels_geometric_scaled_bound (A : ℝ) (m : ℕ) (hA : 8 ≤ A) :
    A ^ m * ((1 / A) ^ (m + 1) / (1 - 1 / A) ^ 2) = A / (A - 1) ^ 2 := by
  have hA0 : A ≠ 0 := by linarith
  have hA1 : A - 1 ≠ 0 := by linarith
  rw [pow_succ, mul_div_assoc, ← mul_assoc]
  have hc : A ^ m * (1 / A) ^ m = 1 := by
    rw [← mul_pow, mul_one_div_cancel hA0, one_pow]
  rw [hc, one_mul]
  field_simp

lemma cassels_geometric_comparison (A X : ℝ) (hA : 8 ≤ A)
    (hXlo : A - 1 ≤ X) (hXhi : X ≤ A + 1) :
    A / (A - 1) ^ 2 ≤ 1 / (X - 3) := by
  have hA1 : 0 < A - 1 := by linarith
  have hA2 : 0 < A - 2 := by linarith
  have hX3 : 0 < X - 3 := by linarith
  calc
    A / (A - 1) ^ 2 ≤ 1 / (A - 2) := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hA1) hA2).mpr
      nlinarith
    _ ≤ 1 / (X - 3) := by
      exact one_div_le_one_div_of_le hX3 (by linarith)

lemma cassels_error_bound (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q < p)
    (x y a : ℤ) (ha : 2 ≤ |a|) (hxa : x - 1 = a ^ q)
    (h : x ^ p = y ^ q + 1) :
    |casselsError p q a y| ≤ 1 / (((|x| : ℤ) : ℚ) - 3) := by
  have haR : (2 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast ha
  have ha0 : (a : ℝ) ≠ 0 := by
    intro he
    rw [he, abs_zero] at haR
    norm_num at haR
  have hxaR : (x : ℝ) - 1 = (a : ℝ) ^ q := by exact_mod_cast hxa
  have hR : (x : ℝ) ^ p = (y : ℝ) ^ q + 1 := by exact_mod_cast h
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  let A : ℝ := |(a : ℝ)| ^ q
  have hA : 8 ≤ A := cassels_abs_power_lower (a : ℝ) q haR hq3
  have hA0 : 0 < A := by linarith
  have htA : |1 / (a : ℝ) ^ q| = 1 / A := by
    simp only [abs_div, abs_one, abs_pow, A]
  have ht : |1 / (a : ℝ) ^ q| ≤ (1 : ℝ) / 2 := by
    rw [htA]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hF := cassels_root_identification p q (hp.odd_of_ne_two hp2)
    (hq.odd_of_ne_two hq2) hq.ne_zero (x : ℝ) (y : ℝ) (a : ℝ) ha0 hxaR hR ht
  have hE := cassels_error_real_identity p q a y ha0
    (cassels_index_mul_gt p q hq.pos).le hF
  have hrem := cassels_remainder_bound p q hp hq hp2 hq2 hqp
    (1 / (a : ℝ) ^ q) ht
  have hscale : |(a : ℝ) ^ (casselsIndex p q * q)| = A ^ casselsIndex p q := by
    rw [abs_pow, Nat.mul_comm, pow_mul]
  have hbound : |(casselsError p q a y : ℝ)| ≤
      A / (A - 1) ^ 2 := by
    rw [hE, abs_mul, hscale]
    calc
      _ ≤ A ^ casselsIndex p q *
          (|1 / (a : ℝ) ^ q| ^ (casselsIndex p q + 1) /
            (1 - |1 / (a : ℝ) ^ q|) ^ 2) :=
        mul_le_mul_of_nonneg_left hrem (pow_nonneg hA0.le _)
      _ = A / (A - 1) ^ 2 := by
        rw [htA]
        exact cassels_geometric_scaled_bound A (casselsIndex p q) hA
  obtain ⟨hXlo, hXhi⟩ := cassels_abs_x_bounds (a : ℝ) (x : ℝ) q hxaR
  have hfinal := hbound.trans (cassels_geometric_comparison A |(x : ℝ)| hA hXlo hXhi)
  exact_mod_cast hfinal

#print axioms cassels_error_bound
#print axioms cassels_abs_power_lower
#print axioms cassels_abs_x_bounds
#print axioms cassels_geometric_scaled_bound
#print axioms cassels_geometric_comparison
#print axioms cassels_index_mul_gt
#print axioms cassels_scaled_power
#print axioms cassels_error_real_identity
#print axioms cassels_root_identification

end Catalan
