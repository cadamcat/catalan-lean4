import Catalan.Classical.KoChao.Homogeneous
import Catalan.Classical.KoChao.Inequalities
import Catalan.Classical.Euler.Arithmetic

set_option autoImplicit false
open scoped BigOperators
namespace Catalan.KoChao

lemma prime_dvd_or_square_of_pow_sub_pow_eq_sq
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (A B C : ℤ)
    (hcop : IsCoprime A B) (h : A ^ q - B ^ q = C ^ 2) :
    (q : ℤ) ∣ C ∨ ∃ r : ℤ, A - B = r ^ 2 := by
  let S : ℤ := ∑ i ∈ Finset.range q, A ^ i * B ^ (q - 1 - i)
  have hprod : (A - B) * S = C ^ 2 := by
    rw [mul_comm]
    exact (geom_sum₂_mul A B q).trans h
  rcases gcd_sub_homogeneous_sum q hq A B hcop with hg | hg
  · right
    have hnonneg : 0 ≤ A - B := by
      have hle : B ^ q ≤ A ^ q := by nlinarith only [h, sq_nonneg C]
      exact sub_nonneg.mpr ((hq.odd_of_ne_two hq2).pow_le_pow.mp hle)
    obtain ⟨r, _, hr⟩ := Euler.sq_of_nonneg_coprime_product (A - B) S C hnonneg
      (Int.isCoprime_iff_gcd_eq_one.mpr hg) hprod
    exact ⟨r, hr⟩
  · left
    have hqd : (q : ℤ) ∣ A - B := by
      have hd := Int.gcd_dvd_left (A - B) S
      change Int.gcd (A - B) S = q at hg
      rwa [hg] at hd
    apply (Nat.prime_iff_prime_int.mp hq).dvd_of_dvd_pow
    rw [← hprod]
    exact dvd_mul_of_dvd_left hqd S

lemma oriented_second_congruence
    (q : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q) (z a b : ℤ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hminus : z - 1 = 2 ^ (q - 1) * a ^ q)
    (hplus : z + 1 = 2 * b ^ q) (hcop : IsCoprime (b ^ 2) (2 * a)) :
    (q : ℤ) ∣ z - 3 := by
  have halt := prime_dvd_or_square_of_pow_sub_pow_eq_sq q hq (by omega)
    (b ^ 2) (2 * a) (b ^ q - 2) hcop (oriented_square_identity q hq.pos z a b hminus hplus)
  rcases halt with hdvd | hsq
  · have he : z - 3 = 2 * (b ^ q - 2) := by linarith only [hplus]
    rw [he]
    exact dvd_mul_of_dvd_right hdvd 2
  · exact False.elim (oriented_difference_not_square q hq5 z a b ha hb hminus hplus hsq)

lemma prime_eq_three_of_two_congruences
    (q : ℕ) (hq : q.Prime) (z : ℤ) (hz : (q : ℤ) ∣ z)
    (hz3 : (q : ℤ) ∣ z - 3) : q = 3 := by
  have h3 : (q : ℤ) ∣ 3 := by
    have hd := dvd_sub hz hz3
    have he : z - (z - 3) = 3 := by ring
    rwa [he] at hd
  have hn : q ∣ 3 := by exact_mod_cast h3
  exact ((Nat.dvd_prime Nat.prime_three).mp hn).resolve_left hq.ne_one

end Catalan.KoChao
