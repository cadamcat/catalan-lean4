import Catalan.Cassels.Elementary

namespace Catalan

private lemma pow_lt_pow_rev {p q : ℕ} (hqp : q < p) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) : a ^ p < a ^ q := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hqp)
  have hr0 : r ≠ 0 := by omega
  have hrr : a ^ r < 1 := pow_lt_one₀ (le_of_lt ha0) ha1 hr0
  have hmul := mul_lt_mul_of_pos_left hrr (pow_pos ha0 q)
  rw [hr, pow_add]
  simpa only [mul_one] using hmul

private lemma real_pos_between {p q : ℕ} (hqp : q < p) (hq0 : 0 < q)
    {B : ℝ} (hB : 1 < B) :
    (B ^ q - 1) ^ p < (B ^ p - 1) ^ q := by
  let t : ℝ := B⁻¹
  have hB0 : 0 < B := by linarith
  have ht0 : 0 < t := by
    dsimp [t]
    exact inv_pos.mpr hB0
  have ht1 : t < 1 := by
    dsimp [t]
    exact inv_lt_one_of_one_lt₀ hB
  have htp : t ^ p < t ^ q := pow_lt_pow_rev hqp ht0 ht1
  have h1q : 0 < 1 - t ^ q := by
    have hq1 : t ^ q < 1 :=
      pow_lt_one₀ (le_of_lt ht0) ht1 (Nat.ne_of_gt hq0)
    linarith
  have hbase : 1 - t ^ q < 1 - t ^ p := by linarith [htp]
  have hpow1 : (1 - t ^ q) ^ p < (1 - t ^ q) ^ q := by
    have hbase1 : 1 - t ^ q < 1 := sub_lt_self 1 (pow_pos ht0 q)
    exact pow_lt_pow_rev hqp h1q hbase1
  have hpow2 : (1 - t ^ q) ^ q < (1 - t ^ p) ^ q := by
    exact pow_lt_pow_left₀ hbase (le_of_lt h1q) (Nat.ne_of_gt hq0)
  have hnorm : (1 - t ^ q) ^ p < (1 - t ^ p) ^ q := lt_trans hpow1 hpow2
  have hscale : 0 < B ^ (p * q) := pow_pos hB0 _
  have hleft : (B ^ q - 1) ^ p / B ^ (p * q) = (1 - t ^ q) ^ p := by
    dsimp [t]
    rw [inv_pow]
    field_simp [ne_of_gt hB0]
    rw [div_pow, ← pow_mul, Nat.mul_comm]
    field_simp [ne_of_gt hB0]
  have hright : (B ^ p - 1) ^ q / B ^ (p * q) = (1 - t ^ p) ^ q := by
    dsimp [t]
    rw [inv_pow]
    field_simp [ne_of_gt hB0]
    rw [div_pow, ← pow_mul, Nat.mul_comm]
    field_simp [ne_of_gt hB0]
  have hnorm' : (B ^ q - 1) ^ p / B ^ (p * q) <
      (B ^ p - 1) ^ q / B ^ (p * q) := by
    rw [hleft, hright]
    exact hnorm
  exact (div_lt_div_iff_of_pos_right hscale).mp hnorm'

private lemma real_neg_between {p q : ℕ} (hqp : q < p)
    {C : ℝ} (hC : 1 ≤ C) :
    (C ^ p + 1) ^ q < (C ^ q + 1) ^ p := by
  let t : ℝ := C⁻¹
  have hC0 : 0 < C := by linarith
  have ht0 : 0 < t := by
    dsimp [t]
    exact inv_pos.mpr hC0
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (inv_le_one₀ hC0).mpr hC
  have htp : t ^ p ≤ t ^ q :=
    pow_le_pow_of_le_one (le_of_lt ht0) ht1 (Nat.le_of_lt hqp)
  have hbase : 1 + t ^ p ≤ 1 + t ^ q := by linarith
  have hpowle : (1 + t ^ p) ^ q ≤ (1 + t ^ q) ^ q :=
    pow_le_pow_left₀ (by positivity) hbase q
  have hbasepos : 1 < 1 + t ^ q := by
    have : 0 < t ^ q := pow_pos ht0 q
    linarith
  have hpowlt : (1 + t ^ q) ^ q < (1 + t ^ q) ^ p :=
    pow_lt_pow_right₀ hbasepos hqp
  have hnorm : (1 + t ^ p) ^ q < (1 + t ^ q) ^ p :=
    lt_of_le_of_lt hpowle hpowlt
  have hscale : 0 < C ^ (p * q) := pow_pos hC0 _
  have hleft : (C ^ p + 1) ^ q / C ^ (p * q) = (1 + t ^ p) ^ q := by
    dsimp [t]
    rw [inv_pow]
    field_simp [ne_of_gt hC0]
    rw [div_pow, ← pow_mul, Nat.mul_comm]
    field_simp [ne_of_gt hC0]
  have hright : (C ^ q + 1) ^ p / C ^ (p * q) = (1 + t ^ q) ^ p := by
    dsimp [t]
    rw [inv_pow]
    field_simp [ne_of_gt hC0]
    rw [div_pow, ← pow_mul, Nat.mul_comm]
    field_simp [ne_of_gt hC0]
  have hnorm' : (C ^ p + 1) ^ q / C ^ (p * q) <
      (C ^ q + 1) ^ p / C ^ (p * q) := by
    rw [hleft, hright]
    exact hnorm
  exact (div_lt_div_iff_of_pos_right hscale).mp hnorm'

lemma cassels_between_powers (p q : ℕ) (hp : Odd p) (hq : Odd q)
    (hq3 : 3 ≤ q) (hqp : q < p) (b : ℤ) (hb0 : b ≠ 0) (hb1 : b ≠ 1) :
    (b ^ q - 1) ^ p < (b ^ p - 1) ^ q + 1 ∧
      (b ^ p - 1) ^ q + 1 < (b ^ q) ^ p := by
  have hq0 : 0 < q := by omega
  have hq3Z : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  by_cases hbpos : 2 ≤ b
  · have hB : (1 : ℝ) < (b : ℝ) := by
      exact_mod_cast (show (1 : ℤ) < b by omega)
    have hreal := real_pos_between hqp hq0 hB
    have hmid : (b ^ q - 1) ^ p < (b ^ p - 1) ^ q := by
      exact_mod_cast hreal
    have hp0 : 0 < p := by omega
    have hpow : (2 : ℤ) ≤ b ^ p := by
      calc
        (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ b ^ p := pow_le_pow_left₀ (by norm_num) hbpos p
    have hz : 1 ≤ b ^ p - 1 := by omega
    have hgap := cassels_consecutive_gap q (b ^ p - 1) hz
    have hgap' : (q : ℤ) ≤ (b ^ p) ^ q - (b ^ p - 1) ^ q := by
      simpa only [sub_add_cancel] using hgap
    have hupper : (b ^ p - 1) ^ q + 1 < (b ^ p) ^ q := by
      linarith
    constructor
    · linarith
    · have heq : (b ^ p) ^ q = (b ^ q) ^ p := by
        calc
          (b ^ p) ^ q = b ^ (p * q) := (pow_mul b p q).symm
          _ = b ^ (q * p) := by rw [Nat.mul_comm]
          _ = (b ^ q) ^ p := pow_mul b q p
      rw [heq] at hupper
      exact hupper
  · have hbneg : b ≤ -1 := by omega
    let c : ℤ := -b
    have hc : 1 ≤ c := by
      dsimp [c]
      omega
    have hC : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    have hreal := real_neg_between hqp hC
    have hmid : (c ^ p + 1) ^ q < (c ^ q + 1) ^ p := by
      exact_mod_cast hreal
    have hcp : 1 ≤ c ^ p := one_le_pow₀ hc
    have hgap := cassels_consecutive_gap q (c ^ p) hcp
    have hgap' : (q : ℤ) ≤ (c ^ p + 1) ^ q - (c ^ p) ^ q := by
      simpa only [add_comm] using hgap
    have hupperc : (c ^ p) ^ q + 1 < (c ^ p + 1) ^ q := by
      linarith
    have hbq : b ^ q = - c ^ q := by
      dsimp [c]
      rw [hq.neg_pow]
      simp
    have hbp : b ^ p = - c ^ p := by
      dsimp [c]
      rw [hp.neg_pow]
      simp
    have hleft : (b ^ q - 1) ^ p = - (c ^ q + 1) ^ p := by
      rw [hbq]
      have he : -c ^ q - 1 = -(c ^ q + 1) := by ring
      rw [he, hp.neg_pow]
    have hmiddle : (b ^ p - 1) ^ q + 1 = -(c ^ p + 1) ^ q + 1 := by
      rw [hbp]
      have he : -c ^ p - 1 = -(c ^ p + 1) := by ring
      rw [he, hq.neg_pow]
    have hright : (b ^ q) ^ p = -(c ^ q) ^ p := by
      rw [hbq, hp.neg_pow]
    constructor
    · rw [hleft, hmiddle]
      linarith
    · rw [hmiddle, hright]
      have hpoweq : (c ^ q) ^ p = (c ^ p) ^ q := by
        calc
          (c ^ q) ^ p = c ^ (q * p) := (pow_mul c q p).symm
          _ = c ^ (p * q) := by rw [Nat.mul_comm]
          _ = (c ^ p) ^ q := pow_mul c p q
      rw [hpoweq]
      linarith

#print axioms cassels_between_powers

end Catalan
