import Mathlib

set_option autoImplicit false
namespace Catalan

lemma wieferich_lift_congruence (p q : ℕ) (hp : p.Prime)
    (h1 : q ≡ 1 [MOD p]) (hw : q ^ (p - 1) ≡ 1 [MOD p ^ 2]) :
    q ≡ 1 [MOD p ^ 2] := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hxy : (p : ℤ) ∣ (q : ℤ) - 1 := by simpa using h1.symm.dvd
  have hx : ¬ (p : ℤ) ∣ (q : ℤ) := by
    intro hd
    have hunit : (p : ℤ) ∣ 1 := by
      have hd' := dvd_sub hd hxy
      have he : (q : ℤ) - ((q : ℤ) - 1) = 1 := by ring
      rwa [he] at hd'
    have hn : p ∣ 1 := by exact_mod_cast hunit
    have := Nat.le_of_dvd (by decide : 0 < 1) hn
    have := hp.two_le
    omega
  have hn : ¬ (p : ℤ) ∣ ((p - 1 : ℕ) : ℤ) := by
    intro hd
    have hdN : p ∣ p - 1 := by exact_mod_cast hd
    have hp2 := hp.two_le
    have := Nat.le_of_dvd (by omega : 0 < p - 1) hdN
    omega
  have he : emultiplicity (p : ℤ) ((q : ℤ) ^ (p - 1) - 1) =
      emultiplicity (p : ℤ) ((q : ℤ) - 1) := by
    simpa only [one_pow] using emultiplicity_pow_sub_pow_of_prime hpZ hxy hx hn
  have hd : (p : ℤ) ^ 2 ∣ (q : ℤ) ^ (p - 1) - 1 := by
    simpa only [Nat.cast_pow, Nat.cast_one] using hw.symm.dvd
  have hqd : (p : ℤ) ^ 2 ∣ (q : ℤ) - 1 := by
    rw [pow_dvd_iff_le_emultiplicity] at hd ⊢
    rwa [he] at hd
  apply Nat.modEq_of_dvd
  simpa only [Nat.cast_pow, Nat.cast_one, neg_sub] using hqd.neg_right

end Catalan
