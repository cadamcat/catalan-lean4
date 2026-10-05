module

public import Mathlib

/-!
# `Catalan.CaseTwo.Mignotte`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan

lemma mignotte_lower_bound (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp5 : 5 ≤ p) (h1 : q ≡ 1 [MOD p ^ 2]) : 4 * p ^ 2 + 1 ≤ q
 := by
  obtain ⟨k, hk⟩ := h1.symm.dvd'
  have hqrep : q = p ^ 2 * k + 1 := by have := hq.one_le; omega
  have hkpos : 0 < k := by
    by_contra hk0
    have hkz : k = 0 := by omega
    rw [hkz, mul_zero, zero_add] at hqrep
    exact hq.ne_one hqrep
  have hpSq : 25 ≤ p ^ 2 := by
    simpa using Nat.pow_le_pow_left hp5 2
  have hqLB : p ^ 2 + 1 ≤ q := by
    have hm := Nat.mul_le_mul_left (p ^ 2) (show 1 ≤ k by omega)
    nlinarith only [hm, hqrep]
  have hpmod : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hqmod : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
  have hkmod : k % 2 = 0 := by
    have he := congrArg (fun t : ℕ => t % 2) hqrep
    norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hpmod, hqmod] at he
    omega
  have hk4 : 4 ≤ k := by
    by_contra hklt
    have hk2 : k = 2 := by omega
    have hp3 : ¬ 3 ∣ p := by
      intro hd
      have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
      omega
    have hpmod3 : p % 3 = 1 ∨ p % 3 = 2 := by
      have hnz : p % 3 ≠ 0 := fun he => hp3 (Nat.dvd_of_mod_eq_zero he)
      omega
    have hpsq3 : p ^ 2 % 3 = 1 := by
      rcases hpmod3 with he | he <;> norm_num [Nat.pow_mod, he]
    have hq3 : 3 ∣ q := by
      apply Nat.dvd_of_mod_eq_zero
      rw [hqrep, hk2]
      norm_num [Nat.add_mod, Nat.mul_mod, hpsq3]
    have hqeq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp hq3
    omega
  have hm := Nat.mul_le_mul_left (p ^ 2) hk4
  nlinarith only [hm, hqrep]

end Catalan
