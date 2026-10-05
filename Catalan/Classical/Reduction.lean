module

public import Mathlib

/-!
# `Catalan.Classical.Reduction`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan

theorem five_pow_hundred : ¬ (5 ^ 100 ≡ 1 [MOD 101 ^ 2]) := by
  norm_num

theorem reduce_to_primes : (∀ p q : ℕ, p.Prime → q.Prime → ∀ x y : ℤ, 1 < x → 1 < y →
    x ^ p = y ^ q + 1 → p = 2 ∧ q = 3 ∧ x = 3 ∧ y = 2) →
    ∀ (x y : ℤ) (a b : ℕ), 1 < a → 1 < b → 1 < x → 1 < y → x ^ a = y ^ b + 1 →
    a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2 := by
  intro hclass x y a b ha hb hx hy hxy
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (by omega : a ≠ 1)
  obtain ⟨q, hq, hqb⟩ := Nat.exists_prime_and_dvd (by omega : b ≠ 1)
  obtain ⟨a', ha'⟩ := exists_eq_mul_right_of_dvd hpa
  obtain ⟨b', hb'⟩ := exists_eq_mul_right_of_dvd hqb
  have ha'pos : 0 < a' := by
    by_contra hzero
    have hzero' : a' = 0 := Nat.eq_zero_of_not_pos hzero
    rw [hzero', mul_zero] at ha'
    omega
  have hb'pos : 0 < b' := by
    by_contra hzero
    have hzero' : b' = 0 := Nat.eq_zero_of_not_pos hzero
    rw [hzero', mul_zero] at hb'
    omega
  have hx' : 1 < x ^ a' := one_lt_pow₀ hx ha'pos.ne'
  have hy' : 1 < y ^ b' := one_lt_pow₀ hy hb'pos.ne'
  have hxpow : (x ^ a') ^ p = x ^ a := by
    rw [← pow_mul, ha', Nat.mul_comm]
  have hypow : (y ^ b') ^ q = y ^ b := by
    rw [← pow_mul, hb', Nat.mul_comm]
  have hinner : (x ^ a') ^ p = (y ^ b') ^ q + 1 := by
    rw [hxpow, hypow]
    exact hxy
  obtain ⟨hp2, hq3, hx3, hy2⟩ := hclass p q hp hq (x ^ a') (y ^ b') hx' hy' hinner
  have hxpowNat : x.natAbs ^ a' = 3 := by
    simpa [Int.natAbs_pow] using congrArg Int.natAbs hx3
  have hypowNat : y.natAbs ^ b' = 2 := by
    simpa [Int.natAbs_pow] using congrArg Int.natAbs hy2
  have hxa' : x.natAbs = 3 ∧ a' = 1 := (Nat.prime_three.pow_eq_iff).mp hxpowNat
  have hyb' : y.natAbs = 2 ∧ b' = 1 := (Nat.prime_two.pow_eq_iff).mp hypowNat
  have hxeq : x = 3 := by
    have hxnonneg : 0 ≤ x := by omega
    calc
      x = |x| := (abs_of_nonneg hxnonneg).symm
      _ = (x.natAbs : ℤ) := (Int.natCast_natAbs x).symm
      _ = 3 := by exact_mod_cast hxa'.1
  have hyeq : y = 2 := by
    have hynonneg : 0 ≤ y := by omega
    calc
      y = |y| := (abs_of_nonneg hynonneg).symm
      _ = (y.natAbs : ℤ) := (Int.natCast_natAbs y).symm
      _ = 2 := by exact_mod_cast hyb'.1
  have haeq : a = 2 := by
    rw [ha', hxa'.2, mul_one]
    exact hp2
  have hbeq : b = 3 := by
    rw [hb', hyb'.2, mul_one]
    exact hq3
  exact ⟨haeq, hbeq, hxeq, hyeq⟩

end Catalan
