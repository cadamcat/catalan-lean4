import Catalan.Wieferich.Core
import Catalan.Cassels.Divisibility

namespace Catalan.A1e

lemma solution_primes_ne (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) : p ≠ q := by
  intro hpq
  subst q
  let pPrime : Fact p.Prime := ⟨hp⟩
  have hpx := cassels_q_dvd_x p p hp hp hp2 hq2 x y hx hy h
  have hpy := cassels_p_dvd_y p p hp hp hp2 hq2 x y hx hy h
  have hx0 : (x : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mpr hpx
  have hy0 : (y : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd y p).mpr hpy
  have hm := congrArg (fun z : ℤ => (z : ZMod p)) h
  simp only [Int.cast_pow, Int.cast_add, Int.cast_one, hx0, hy0,
    zero_pow hp.ne_zero, zero_add] at hm
  exact zero_ne_one hm

lemma lift_minus_one (q : ℕ) (hq : Odd q) (a : ℤ)
    (ha : a ≡ -1 [ZMOD (q : ℤ)]) :
    a ^ q ≡ -1 [ZMOD (q : ℤ) ^ 2] := by
  have hd : (q : ℤ) ∣ -a - 1 := by
    simpa only [sub_eq_add_neg, add_comm] using Int.modEq_iff_dvd.mp ha
  obtain ⟨t, ht⟩ := hd
  have ht' : -a = 1 + (q : ℤ) * t := by linarith
  have hl := one_add_mul_pow_dvd q t
  rw [← ht', hq.neg_pow] at hl
  apply Int.modEq_iff_dvd.mpr
  simpa only [sub_eq_add_neg, add_comm] using hl

lemma wieferich_of_factorization
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hpq : p ≠ q) (x a : ℤ)
    (hx : (q : ℤ) ^ 2 ∣ x)
    (hfac : x - 1 = (p : ℤ) ^ (q - 1) * a ^ q) :
    p ^ (q - 1) ≡ 1 [MOD q ^ 2] := by
  let qPrime : Fact q.Prime := ⟨hq⟩
  have hp0 : (p : ZMod q) ≠ 0 := by
    intro hz
    have hd : q ∣ p := (ZMod.natCast_eq_zero_iff p q).mp hz
    rcases (Nat.dvd_prime hp).mp hd with hq1 | hqp
    · exact hq.ne_one hq1
    · exact hpq hqp.symm
  have hF : (p : ℤ) ^ (q - 1) ≡ 1 [ZMOD (q : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff ((p : ℤ) ^ (q - 1)) 1 q).mp
    simpa only [Int.cast_pow, Int.cast_natCast, Int.cast_one] using
      (ZMod.pow_card_sub_one_eq_one hp0)
  have hqx : (q : ℤ) ∣ x := by
    apply dvd_trans (show (q : ℤ) ∣ (q : ℤ) ^ 2 from ⟨(q : ℤ), by ring⟩) hx
  have hA : (p : ℤ) ^ (q - 1) * a ^ q ≡ -1 [ZMOD (q : ℤ)] := by
    rw [← hfac]
    simpa only [zero_sub] using
      (Int.modEq_zero_iff_dvd.mpr hqx).sub (Int.ModEq.refl (1 : ℤ))
  have hPa : (p : ℤ) ^ (q - 1) * a ^ q ≡ a [ZMOD (q : ℤ)] := by
    simpa only [one_mul] using hF.mul (Int.ModEq.pow_prime_eq_self hq a)
  have ha : a ≡ -1 [ZMOD (q : ℤ)] := hPa.symm.trans hA
  have ha2 := lift_minus_one q (hq.odd_of_ne_two hq2) a ha
  have hA2 : (p : ℤ) ^ (q - 1) * a ^ q ≡ -1 [ZMOD (q : ℤ) ^ 2] := by
    rw [← hfac]
    simpa only [zero_sub] using
      (Int.modEq_zero_iff_dvd.mpr hx).sub (Int.ModEq.refl (1 : ℤ))
  have hPa2 : (p : ℤ) ^ (q - 1) * a ^ q ≡
      -((p : ℤ) ^ (q - 1)) [ZMOD (q : ℤ) ^ 2] := by
    simpa only [mul_neg, mul_one] using
      (Int.ModEq.refl ((p : ℤ) ^ (q - 1))).mul ha2
  have hn := (hPa2.symm.trans hA2).neg
  have hfinal : (p : ℤ) ^ (q - 1) ≡ 1 [ZMOD (q : ℤ) ^ 2] := by
    simpa only [neg_neg] using hn
  apply Int.natCast_modEq_iff.mp
  simpa only [Nat.cast_pow, Nat.cast_one] using hfinal

end Catalan.A1e

