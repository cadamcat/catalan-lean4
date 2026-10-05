module

public import Catalan.Cassels.Elementary

/-!
# `Catalan.Classical.KoChao.Factors`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan.KoChao

lemma square_base_oriented_factors
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (hxodd : Odd x)
    (h : x ^ 2 = y ^ q + 1) :
    ∃ z a b : ℤ, (z = x ∨ z = -x) ∧ a ≠ 0 ∧ b ≠ 0 ∧ Odd b ∧
      z - 1 = 2 ^ (q - 1) * a ^ q ∧ z + 1 = 2 * b ^ q ∧
      IsCoprime (b ^ 2) (2 * a)
 := by
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have horient : ∃ z k : ℤ, (z = x ∨ z = -x) ∧ z = 4 * k + 1 := by
    obtain ⟨t, ht⟩ := hxodd
    rcases Int.even_or_odd t with he | ho
    · obtain ⟨s, hs⟩ := he
      exact ⟨x, s, Or.inl rfl, by omega⟩
    · obtain ⟨s, hs⟩ := ho
      exact ⟨-x, -s - 1, Or.inr rfl, by omega⟩
  obtain ⟨z, k, hzx, hzk⟩ := horient
  have hzs : z ^ 2 = y ^ q + 1 := by
    rcases hzx with hz | hz <;> simpa only [hz, neg_sq] using h
  let B : ℤ := 2 * k + 1
  have hBodd : Odd B := ⟨k, rfl⟩
  have hcop2 : IsCoprime (2 : ℤ) B := Int.isCoprime_two_left.mpr hBodd
  have hcopHalf : IsCoprime (z - 1) B := by
    obtain ⟨r, s, hrs⟩ := hcop2
    refine ⟨-r, 2 * r + s, ?_⟩
    dsimp only [B] at hrs ⊢
    rw [hzk]
    nlinarith only [hrs]
  have hcop : IsCoprime (2 * (z - 1)) B := hcop2.mul_left hcopHalf
  have hprod : (2 * (z - 1)) * B = y ^ q := by
    dsimp only [B]
    rw [hzk] at hzs ⊢
    nlinarith only [hzs]
  have hprod0 : (2 * (z - 1)) * B ≠ 0 := by
    rw [hprod]
    exact pow_ne_zero q hy
  have hA0 : 2 * (z - 1) ≠ 0 := left_ne_zero_of_mul hprod0
  have hB0 : B ≠ 0 := right_ne_zero_of_mul hprod0
  obtain ⟨c, b, hc, hb⟩ := cassels_coprime_power_factors q hqodd
    (2 * (z - 1)) B y hA0 hB0 (Int.isCoprime_iff_gcd_eq_one.mp hcop) hprod
  have hc0 : c ≠ 0 := by
    intro he
    rw [he, zero_pow hq.ne_zero] at hc
    exact hA0 hc
  have hb0 : b ≠ 0 := by
    intro he
    rw [he, zero_pow hq.ne_zero] at hb
    exact hB0 hb
  have hbodd : Odd b := by
    apply (Int.odd_pow' hq.ne_zero).mp
    rw [← hb]
    exact hBodd
  have hc2 : (2 : ℤ) ∣ c := by
    apply Int.prime_two.dvd_of_dvd_pow
    rw [← hc]
    exact dvd_mul_right 2 (z - 1)
  obtain ⟨a, hca⟩ := hc2
  have ha0 : a ≠ 0 := by
    intro he
    exact hc0 (by simpa only [he, mul_zero] using hca)
  have hpow2 : (2 : ℤ) ^ q = 2 * (2 : ℤ) ^ (q - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hq.one_le, pow_succ']
  have hzminus : z - 1 = 2 ^ (q - 1) * a ^ q := by
    have hh := hc
    rw [hca, mul_pow, hpow2] at hh
    nlinarith only [hh]
  have hzplus : z + 1 = 2 * b ^ q := by
    rw [← hb]
    dsimp only [B]
    omega
  have hcb : IsCoprime c b := by
    apply (IsCoprime.pow_iff hq.pos hq.pos).mp
    rw [← hc, ← hb]
    exact hcop
  have hb2a : IsCoprime b (2 * a) := by
    rw [← hca]
    exact hcb.symm
  exact ⟨z, a, b, hzx, ha0, hb0, hbodd, hzminus, hzplus, hb2a.pow_left⟩

end Catalan.KoChao
