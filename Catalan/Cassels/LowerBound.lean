import Catalan.Cassels.Modular

namespace Catalan

lemma cassels_lower_bound_from_relations (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q < p) (x y b u : ℤ)
    (hb : b ≠ 0) (hu : 0 < u)
    (hyb : y + 1 = (q : ℤ) ^ (p - 1) * b ^ p)
    (hsu : casselsCyclo q (-y) = (q : ℤ) * u ^ p)
    (hxu : x = (q : ℤ) * b * u) :
    (q : ℤ) ^ (p - 1) + q ≤ |x| := by
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hp4 : 4 ≤ p := by omega
  have hq3Z : (3 : ℤ) ≤ q := by exact_mod_cast hq3
  have hqpos : 0 < (q : ℤ) := by exact_mod_cast hq.pos
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hbabs : (1 : ℤ) ≤ |b| := Int.one_le_abs hb
  have hbpow : (1 : ℤ) ≤ |b| ^ p := one_le_pow₀ hbabs
  have hyabs : |y + 1| = (q : ℤ) ^ (p - 1) * |b| ^ p := by
    rw [hyb, abs_mul, abs_pow, abs_pow, abs_of_pos hqpos]
  have hqpow : (q : ℤ) ^ (p - 1) ≤ |y + 1| := by
    rw [hyabs]
    nlinarith [pow_pos hqpos (p - 1)]
  have hqsq : (q : ℤ) ^ 2 ≤ |y + 1| :=
    (pow_le_pow_right₀ (by omega : (1 : ℤ) ≤ q) (by omega : 2 ≤ p - 1)).trans hqpow
  have hyadd : |y + 1| ≤ |y| + 1 := by simpa only [abs_one] using abs_add_le y 1
  have hY : (q : ℤ) + 2 ≤ |y| := by
    nlinarith [sq_nonneg ((q : ℤ) - 2)]
  have hnegA : -y - 1 = -(y + 1) := by ring
  have hu1 : 1 < u := by
    by_contra hle
    have hueq : u = 1 := by omega
    have hf := int_pow_sub_one_factor q (-y)
    rw [hsu, hueq, one_pow, mul_one] at hf
    have heq : (-y) ^ q = (-y - 1) * (q : ℤ) + 1 := by linarith
    have hupper : |y| ^ q ≤ (q : ℤ) * (|y| + 1) + 1 := by
      calc
        |y| ^ q = |(-y) ^ q| := by rw [abs_pow, abs_neg]
        _ = |(-y - 1) * (q : ℤ) + 1| := congrArg abs heq
        _ ≤ |(-y - 1) * (q : ℤ)| + |1| := abs_add_le _ _
        _ = (q : ℤ) * |y + 1| + 1 := by
          rw [abs_mul, hnegA, abs_neg, abs_of_pos hqpos, abs_one]
          ring
        _ ≤ (q : ℤ) * (|y| + 1) + 1 := by gcongr
    have hlower : |y| ^ 2 ≤ |y| ^ q :=
      pow_le_pow_right₀ (by omega : (1 : ℤ) ≤ |y|) hq.two_le
    nlinarith [mul_nonneg (abs_nonneg y) (show 0 ≤ |y| - (q : ℤ) - 2 by omega)]
  have hqpowA : (q : ℤ) ^ (p - 1) ∣ -y - 1 := by
    rw [hnegA, dvd_neg, hyb]
    exact dvd_mul_right _ _
  have hd : (q : ℤ) ^ (p - 1) ∣ (q : ℤ) * (u ^ p - 1) := by
    have he : casselsCyclo q (-y) - (q : ℤ) = (q : ℤ) * (u ^ p - 1) := by
      rw [hsu]
      ring
    simpa only [he] using dvd_trans hqpowA (cassels_cyclo_sub_dvd q (-y))
  have hpstep : p - 1 = (p - 2) + 1 := by omega
  have hqpowstep : (q : ℤ) ^ (p - 1) = (q : ℤ) * (q : ℤ) ^ (p - 2) := by
    rw [hpstep, pow_succ']
  have hd' : (q : ℤ) ^ (p - 2) ∣ u ^ p - 1 := by
    rwa [hqpowstep, mul_dvd_mul_iff_left hqZ.ne_zero] at hd
  have hqup : (q : ℤ) ∣ u ^ p - 1 :=
    dvd_trans (dvd_pow_self (q : ℤ) (by omega : p - 2 ≠ 0)) hd'
  have hqu : (q : ℤ) ∣ u - 1 := cassels_prime_root_mod p q hp hq hqp u hqup
  have hnqS : ¬ (q : ℤ) ∣ casselsCyclo p u := by
    intro hqS
    have hqdiff : (q : ℤ) ∣ casselsCyclo p u - (p : ℤ) :=
      dvd_trans hqu (cassels_cyclo_sub_dvd p u)
    have hqpdvd : (q : ℤ) ∣ (p : ℤ) := by
      have he : casselsCyclo p u - (casselsCyclo p u - (p : ℤ)) = p := by ring
      simpa only [he] using dvd_sub hqS hqdiff
    have hqpdvdN : q ∣ p := by exact_mod_cast hqpdvd
    rcases (Nat.dvd_prime hp).mp hqpdvdN with he | he
    · exact hq.ne_one he
    · omega
  have hdU : (q : ℤ) ^ (p - 2) ∣ u - 1 := by
    apply hqZ.pow_dvd_of_dvd_mul_right (p - 2) hnqS
    rw [← int_pow_sub_one_factor p u]
    exact hd'
  have hlu : (q : ℤ) ^ (p - 2) + 1 ≤ u := by
    have := Int.le_of_dvd (by omega : 0 < u - 1) hdU
    omega
  have hxabs : |x| = (q : ℤ) * |b| * u := by
    rw [hxu, abs_mul, abs_mul, abs_of_pos hqpos, abs_of_pos hu]
  calc
    (q : ℤ) ^ (p - 1) + q = (q : ℤ) * ((q : ℤ) ^ (p - 2) + 1) := by
      rw [hqpowstep]
      ring
    _ ≤ (q : ℤ) * u := mul_le_mul_of_nonneg_left hlu hqpos.le
    _ = (q : ℤ) * 1 * u := by ring
    _ ≤ (q : ℤ) * |b| * u := by gcongr
    _ = |x| := hxabs.symm

#print axioms cassels_lower_bound_from_relations

end Catalan
