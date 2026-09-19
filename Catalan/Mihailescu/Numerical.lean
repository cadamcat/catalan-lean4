import Mathlib

namespace Catalan

lemma even_degree_power_bound (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ((p - 1 : ℝ) ^ 2) ≤ 2 ^ (p - 1) := by
  have heven : Even (p - 1) := (Fact.out : p.Prime).even_sub_one hp2
  obtain ⟨n, hn⟩ := heven
  have hbound : (2 * n) ^ 2 ≤ 2 ^ (2 * n) := by
    calc
      (2 * n) ^ 2 ≤ (2 ^ n) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_pow (by decide : 2 ≠ 1) n) 2
      _ = 2 ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm]
  have hpone : 1 ≤ p := (Fact.out : p.Prime).one_le
  have hsub : (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := by
    norm_num [Nat.cast_sub hpone]
  calc
    ((p - 1 : ℝ) ^ 2) = (((2 * n : ℕ) : ℝ) ^ 2) := by
      rw [hsub, hn]
      simp [two_mul]
    _ = (((2 * n) ^ 2 : ℕ) : ℝ) := by rw [Nat.cast_pow]
    _ ≤ (((2 ^ (2 * n) : ℕ) : ℝ)) := by exact_mod_cast hbound
    _ = (2 : ℝ) ^ (2 * n) := by norm_num [Nat.cast_pow]
    _ = (2 : ℝ) ^ (p - 1) := by rw [hn]; simp [two_mul]

lemma small_ratio_le (d n X ε s : ℝ) (hd : 2 ≤ d) (hn : 0 < n)
    (hX : 36 ≤ X) (hε : 0 < ε) (hs0 : 0 ≤ s)
    (hs : s ≤ 2 * ((2 - ε) * n / d)) :
    s / (n * (X - 1)) ≤ 2 / 35 := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hX1pos : 0 < X - 1 := by linarith
  have hdenpos : 0 < n * (X - 1) := mul_pos hn hX1pos
  have hratio_nonneg : 0 ≤ s / (n * (X - 1)) := div_nonneg hs0 hdenpos.le
  have hnum : (2 - ε) * n / d ≤ n := by
    apply (div_le_iff₀ hdpos).2
    calc
      (2 - ε) * n ≤ 2 * n := by
        exact mul_le_mul_of_nonneg_right (by linarith) hn.le
      _ ≤ d * n := by
        exact mul_le_mul_of_nonneg_right hd hn.le
      _ = n * d := by ring
  have hs2n : s ≤ 2 * n := hs.trans (mul_le_mul_of_nonneg_left hnum (by norm_num))
  have hX1 : 35 ≤ X - 1 := by linarith
  have hden : 35 * n ≤ n * (X - 1) := by
    calc
      35 * n = n * 35 := by ring
      _ ≤ n * (X - 1) := mul_le_mul_of_nonneg_left hX1 hn.le
  apply (div_le_iff₀ hdenpos).2
  calc
    s ≤ 2 * n := hs2n
    _ = (2 / 35) * (35 * n) := by ring
    _ ≤ (2 / 35) * (n * (X - 1)) := by
      exact mul_le_mul_of_nonneg_left hden (by norm_num)

end Catalan
