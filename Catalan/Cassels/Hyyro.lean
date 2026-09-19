import Catalan.Cassels.Factorization

namespace Catalan

/-- The factor relation and divisibility give a ≡ -1 mod r by Fermat. -/
lemma hyyro_factor_congruence (r : ℕ) (hr : r.Prime) (s z a : ℤ)
    (hz : (r : ℤ) ∣ z) (h : z - 1 = s ^ (r - 1) * a ^ r) :
    (r : ℤ) ∣ a + 1 := by
  let : Fact r.Prime := ⟨hr⟩
  have hz0 : (z : ZMod r) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z r).mpr hz
  have he : -(1 : ZMod r) = (s : ZMod r) ^ (r - 1) * (a : ZMod r) ^ r := by
    have hh := congrArg (fun t : ℤ => (t : ZMod r)) h
    simpa only [Int.cast_sub, Int.cast_one, Int.cast_mul, Int.cast_pow, hz0, zero_sub] using hh
  have hs0 : (s : ZMod r) ≠ 0 := by
    intro hs
    rw [hs, zero_pow (by have := hr.one_lt; omega), zero_mul] at he
    exact one_ne_zero (neg_eq_zero.mp he)
  rw [ZMod.pow_card_sub_one_eq_one hs0, one_mul, ZMod.pow_card] at he
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a + 1) r).mp
  rw [Int.cast_add, Int.cast_one, ← he, neg_add_cancel]

/-- An integer-power estimate used in the negative case. -/
lemma hyyro_two_pow_le_three (n : ℕ) (hn : 3 ≤ n) :
    (2 : ℤ) ^ n ≤ 3 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    calc
      (2 : ℤ) ^ (n + 1) = 2 ^ n * 2 := pow_succ _ _
      _ ≤ 3 ^ (n - 1) * 3 := by nlinarith [pow_pos (by norm_num : (0 : ℤ) < 3) (n - 1)]
      _ = 3 ^ (n + 1 - 1) := by rw [← pow_succ]; congr 1; omega

/-- Exclude a = -1 in the negative case without taking real roots. -/
lemma hyyro_small_negative_impossible (p q : ℕ) (hp3 : 3 ≤ p) (hq3 : 3 ≤ q)
    (hop : Odd p) (hoq : Odd q) (x y b : ℤ)
    (hx : x < 0) (hy : y < 0) (hb : b < 0)
    (h : x ^ p = y ^ q + 1)
    (hx1 : 1 - x = (p : ℤ) ^ (q - 1))
    (hyb : y + 1 = (q : ℤ) ^ (p - 1) * b ^ p)
    (hbd : (p : ℤ) ∣ b - 1) : False := by
  have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have hqZ : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  have hbp : (p : ℤ) - 1 ≤ -b := by
    have hd : (p : ℤ) ∣ 1 - b := by simpa only [neg_sub] using dvd_neg.mpr hbd
    have hh := Int.le_of_dvd (by omega : 0 < 1 - b) hd
    omega
  have hlow : (p : ℤ) ^ p ≤ (q : ℤ) ^ (p - 1) * (-b) ^ p := by
    calc
      (p : ℤ) ^ p ≤ (2 * ((p : ℤ) - 1)) ^ p :=
        pow_le_pow_left₀ (by omega) (by omega) _
      _ = (2 : ℤ) ^ p * ((p : ℤ) - 1) ^ p := mul_pow _ _ _
      _ ≤ (3 : ℤ) ^ (p - 1) * ((p : ℤ) - 1) ^ p := by
        exact mul_le_mul_of_nonneg_right (hyyro_two_pow_le_three p hp3)
          (pow_nonneg (by omega) _)
      _ ≤ (q : ℤ) ^ (p - 1) * (-b) ^ p := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ (by norm_num) hqZ _
        · exact pow_le_pow_left₀ (by omega) hbp _
        · exact pow_nonneg (by omega) _
        · positivity
  have hylarge : (p : ℤ) ^ p < -y := by
    rw [hop.neg_pow] at hlow
    have hprod : (q : ℤ) ^ (p - 1) * -(b ^ p) = -(y + 1) := by nlinarith [hyb]
    rw [hprod] at hlow
    omega
  have hpow : (-y) ^ q = (-x) ^ p + 1 := by
    rw [hoq.neg_pow, hop.neg_pow]
    omega
  have hyupper : (-y) ^ q < ((p : ℤ) ^ p) ^ q := by
    calc
      (-y) ^ q = (-x) ^ p + 1 := hpow
      _ ≤ (-x + 1) ^ p := by
        simpa only [one_pow] using pow_add_pow_le (by omega : 0 ≤ -x) (by norm_num : (0 : ℤ) ≤ 1) (by omega : p ≠ 0)
      _ = ((p : ℤ) ^ (q - 1)) ^ p := by congr 1; omega
      _ < ((p : ℤ) ^ p) ^ q := by
        rw [← pow_mul, ← pow_mul]
        apply pow_lt_pow_right₀ (by omega : (1 : ℤ) < p)
        have he : (q - 1) * p + p = p * q := by
          calc
            (q - 1) * p + p = ((q - 1) + 1) * p := by ring
            _ = p * q := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q), Nat.mul_comm]
        omega
  have hyupper' : -y < (p : ℤ) ^ p :=
    (pow_lt_pow_iff_left₀ (by omega) (by positivity) (by omega : q ≠ 0)).mp hyupper
  omega

/-- Hyyrö's bound, including the negative-integer case (Bilu 2005, Prop. 5.3). -/
theorem hyyro_bound (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) :
    (p : ℤ) ^ (q - 1) * ((q : ℤ) - 1) ^ q + 1 ≤ |x| := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have hqZ : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  have hop : Odd p := hp.odd_of_ne_two hp2
  have hoq : Odd q := hq.odd_of_ne_two hq2
  have hpPow : 0 < (p : ℤ) ^ (q - 1) := pow_pos (by omega) _
  obtain ⟨a, b, u, v, ha, hb, hu, hv, hxa, hya, _, hyb, hxb, _⟩ :=
    cassels_factorization p q hp hq hp2 hq2 x y hx hy h
  have had : (q : ℤ) ∣ a + 1 := hyyro_factor_congruence q hq p x a
    (cassels_q_dvd_x p q hp hq hp2 hq2 x y hx hy h) hxa
  have hbd : (p : ℤ) ∣ b - 1 := by
    have hf : -y - 1 = (q : ℤ) ^ (p - 1) * (-b) ^ p := by
      rw [hop.neg_pow]
      linear_combination -hyb
    have hd := hyyro_factor_congruence p hp q (-y) (-b)
      (dvd_neg.mpr (cassels_p_dvd_y p q hp hq hp2 hq2 x y hx hy h)) hf
    have he : -(-b + 1) = b - 1 := by ring
    simpa only [he] using dvd_neg.mpr hd
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have haneg : a < 0 := by
      apply hoq.pow_neg_iff.mp
      nlinarith
    have hyneg : y < 0 := by
      apply hoq.pow_neg_iff.mp
      have hxp : x ^ p < 0 := hop.pow_neg_iff.mpr hxneg
      omega
    have hbneg : b < 0 := by
      have hqv : 0 < (q : ℤ) * v := mul_pos (by omega) hv
      have he : x = ((q : ℤ) * v) * b := by nlinarith [hxb]
      nlinarith
    have hane : a ≠ -1 := by
      intro he
      have hx1 : 1 - x = (p : ℤ) ^ (q - 1) := by
        rw [he, hoq.neg_one_pow, mul_neg_one] at hxa
        omega
      exact hyyro_small_negative_impossible p q hp3 hq3 hop hoq x y b
        hxneg hyneg hbneg h hx1 hyb hbd
    have haq : (q : ℤ) + 1 ≤ -a := by
      have hd : (q : ℤ) ∣ -(a + 1) := dvd_neg.mpr had
      have hh := Int.le_of_dvd (by omega : 0 < -(a + 1)) hd
      omega
    have hgap : ((q : ℤ) - 1) ^ q + 1 ≤ (-a) ^ q := by
      have hh := pow_lt_pow_left₀ (by omega : (q : ℤ) - 1 < -a)
        (by omega : 0 ≤ (q : ℤ) - 1) hq.ne_zero
      omega
    have hpp : (2 : ℤ) ≤ (p : ℤ) ^ (q - 1) := by
      have hh := pow_le_pow_right₀ (by omega : (1 : ℤ) ≤ p)
        (by omega : 1 ≤ q - 1)
      simp only [pow_one] at hh
      omega
    have hxa' : 1 - x = (p : ℤ) ^ (q - 1) * (-a) ^ q := by
      rw [hoq.neg_pow]
      linear_combination -hxa
    rw [abs_of_neg hxneg]
    nlinarith [mul_le_mul_of_nonneg_left hgap hpPow.le]
  · have hapos : 0 < a := by
      have hpow : 0 ≤ a ^ q := by nlinarith
      have ha0 : 0 ≤ a := by
        by_contra hn
        have hh := hoq.pow_neg_iff.mpr (show a < 0 by omega)
        omega
      omega
    have haq : (q : ℤ) - 1 ≤ a := by
      have hh := Int.le_of_dvd (by omega : 0 < a + 1) had
      omega
    have hpow := pow_le_pow_left₀ (by omega : 0 ≤ (q : ℤ) - 1) haq q
    rw [abs_of_pos hxpos]
    nlinarith [mul_le_mul_of_nonneg_left hpow hpPow.le]

end Catalan
