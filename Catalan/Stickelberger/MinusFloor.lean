import Mathlib

namespace Catalan.MinusGenerators

lemma floor_step_zero_or_one (p a k : ℕ) (ha : a < p) :
    ((a * (k + 1) / p : ℕ) : ℤ) - ((a * k / p : ℕ) : ℤ) = 0 ∨
    ((a * (k + 1) / p : ℕ) : ℤ) - ((a * k / p : ℕ) : ℤ) = 1 := by
  have hp : 0 < p := by omega
  rw [show a * (k + 1) = a * k + a by ring, Nat.add_div hp]
  rw [Nat.div_eq_of_lt ha]
  by_cases hrem : p ≤ a * k % p + a % p
  · simp [hrem]
  · simp [hrem]

lemma complementary_floor_sum (p a t : ℕ) (hp : p.Prime)
    (ha0 : 0 < a) (hap : a < p) (ht0 : 0 < t) (htp : t < p) :
    a * t / p + (p - a) * t / p = t - 1 := by
  have hpa : a + (p - a) = p := Nat.add_sub_of_le hap.le
  have hsum : a * t + (p - a) * t = p * t := by
    rw [← Nat.add_mul, hpa]
  have hnot : ¬p ∣ a * t := by
    intro hdiv
    rcases (hp.dvd_mul.mp hdiv) with ha_div | ht_div
    · exact (Nat.not_dvd_of_pos_of_lt ha0 hap) ha_div
    · exact (Nat.not_dvd_of_pos_of_lt ht0 htp) ht_div
  have hrem : p ≤ (a * t) % p + ((p - a) * t) % p := by
    apply Nat.le_mod_add_mod_of_dvd_add_of_not_dvd
    · rw [hsum]
      exact ⟨t, by omega⟩
    · exact hnot
  have hdiv := Nat.add_div_eq_of_le_mod_add_mod hrem hp.pos
  rw [hsum, Nat.mul_div_right t hp.pos] at hdiv
  omega

end Catalan.MinusGenerators
