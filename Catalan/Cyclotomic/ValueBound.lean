import Mathlib

open scoped BigOperators

noncomputable section
namespace Catalan

variable (p : ℕ) [hp : Fact p.Prime]

lemma cyclotomic_pow_growth (n : ℕ) (hn : 5 ≤ n) :
    (n : ℤ) < (2 : ℤ) ^ (n - 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hsub : n + 1 - 2 = (n - 2) + 1 := by omega
      rw [hsub, pow_succ, Nat.cast_succ]
      have hpow : 0 ≤ (2 : ℤ) ^ (n - 2) := pow_nonneg (by norm_num) _
      nlinarith

lemma cyclotomic_neg_sum_bound (t : ℤ) (ht : 2 ≤ t) (m : ℕ) :
    t ^ (3 + 2 * m) ≤
      ∑ i ∈ Finset.range (5 + 2 * m), (-t) ^ i := by
  have ht0 : 0 ≤ t := by omega
  have hbase : t ^ 3 ≤ ∑ i ∈ Finset.range 5, (-t) ^ i := by
    norm_num [Finset.sum_range_succ]
    nlinarith [sq_nonneg (t - 1), sq_nonneg (t * (t - 1))]
  induction m with
  | zero => simpa using hbase
  | succ m ih =>
      let n : ℕ := 5 + 2 * m
      have hnodd : Odd n := by
        dsimp [n]
        exact ⟨2 + m, by omega⟩
      have hrec :
          (∑ i ∈ Finset.range (n + 2), (-t) ^ i) =
            (∑ i ∈ Finset.range n, (-t) ^ i) + (-t) ^ n + (-t) ^ (n + 1) := by
        rw [show n + 2 = (n + 1) + 1 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ]
      have hpair : (-t) ^ n + (-t) ^ (n + 1) = t ^ n * (t - 1) := by
        rw [hnodd.neg_pow, pow_succ, hnodd.neg_pow]
        ring
      have htn : 0 ≤ t ^ n := pow_nonneg ht0 _
      have hpairge : t ^ n ≤ (-t) ^ n + (-t) ^ (n + 1) := by
        rw [hpair]
        have htminus : (1 : ℤ) ≤ t - 1 := by omega
        nlinarith
      have hstep : t ^ n ≤ ∑ i ∈ Finset.range (n + 2), (-t) ^ i := by
        rw [hrec]
        have hi : t ^ (3 + 2 * m) ≤
            ∑ i ∈ Finset.range n, (-t) ^ i := by
          simpa [n] using ih
        have hpowold : 0 ≤ t ^ (3 + 2 * m) := pow_nonneg ht0 _
        have hsum : 0 ≤ ∑ i ∈ Finset.range n, (-t) ^ i := by
          nlinarith
        nlinarith [hpairge, hsum]
      dsimp [n] at hstep ⊢
      convert hstep using 1 <;> ring_nf

theorem cyclotomic_value_large (hp2 : p ≠ 2) (x : ℤ)
    (hx : 2 ≤ |x|) (hexc : p = 3 → x ≠ -2) :
    (p : ℤ) < |∑ i ∈ Finset.range p, x ^ i| := by
  have hp3_or_hp5 : p = 3 ∨ 5 ≤ p := by
    have hpprime : p.Prime := hp.out
    by_cases hp3 : p = 3
    · exact Or.inl hp3
    · right
      by_contra hnot
      have hple : p ≤ 4 := by omega
      have hpge : 2 ≤ p := hp.out.two_le
      interval_cases p
      · exact (hp2 rfl).elim
      · exact (hp3 rfl).elim
      · norm_num at hpprime
  rcases hp3_or_hp5 with rfl | hp5
  · have hxne : x ≠ -2 := hexc rfl
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one]
    by_cases hx0 : 0 ≤ x
    · rw [abs_of_nonneg hx0] at hx
      have hpoly : 0 ≤ 1 + x + x ^ 2 := by nlinarith [sq_nonneg (x + 1)]
      rw [abs_of_nonneg hpoly]
      have hstrict : (3 : ℤ) < 1 + x + x ^ 2 := by
        nlinarith [sq_nonneg (x - 2)]
      exact hstrict
    · have hxneg : x < 0 := by omega
      rw [abs_of_neg hxneg] at hx
      have hxle : x ≤ -2 := by omega
      have hxle3 : x ≤ -3 := by
        by_contra h
        have : x = -2 := by omega
        exact hxne this
      have hpoly : 0 ≤ 1 + x + x ^ 2 := by
        nlinarith [sq_nonneg (x + 1)]
      rw [abs_of_nonneg hpoly]
      have hstrict : (3 : ℤ) < 1 + x + x ^ 2 := by
        nlinarith [sq_nonneg (x + 3)]
      exact hstrict
  · by_cases hx0 : 0 ≤ x
    · rw [abs_of_nonneg hx0] at hx
      have hsum : 0 ≤ ∑ i ∈ Finset.range p, x ^ i := by
        exact Finset.sum_nonneg (fun i hi => pow_nonneg hx0 _)
      have hlast : x ^ (p - 1) ≤ ∑ i ∈ Finset.range p, x ^ i := by
        apply Finset.single_le_sum
        · intro i hi
          exact pow_nonneg hx0 _
        · exact Finset.mem_range.mpr (by omega)
      have hgrowth := cyclotomic_pow_growth p hp5
      have hpow : (2 : ℤ) ^ (p - 2) ≤ x ^ (p - 1) := by
        calc
          (2 : ℤ) ^ (p - 2) ≤ x ^ (p - 2) :=
            pow_le_pow_left₀ (by norm_num) hx (p - 2)
          _ ≤ x ^ (p - 1) := by
            apply pow_le_pow_right₀
            · omega
            · omega
      rw [abs_of_nonneg hsum]
      exact lt_of_lt_of_le hgrowth (hpow.trans hlast)
    · have hxneg : x < 0 := by omega
      have ht : 2 ≤ -x := by
        rw [abs_of_neg hxneg] at hx
        exact hx
      have hpodd : Odd p := hp.out.odd_of_ne_two hp2
      obtain ⟨k, hpk⟩ := hpodd
      have hk2 : 2 ≤ k := by omega
      obtain ⟨m, hkm⟩ := Nat.exists_eq_add_of_le hk2
      have hpm : p = 5 + 2 * m := by omega
      have hsub : p - 2 = 3 + 2 * m := by omega
      have hbound : (-x) ^ (p - 2) ≤
          ∑ i ∈ Finset.range p, x ^ i := by
        rw [hsub, hpm]
        simpa using cyclotomic_neg_sum_bound (-x) ht m
      have hgrowth := cyclotomic_pow_growth p hp5
      have hpow : (2 : ℤ) ^ (p - 2) ≤ (-x) ^ (p - 2) :=
        pow_le_pow_left₀ (by norm_num) ht (p - 2)
      have hsum : 0 ≤ ∑ i ∈ Finset.range p, x ^ i := by
        have htpos : 0 ≤ (-x) ^ (p - 2) := pow_nonneg (by omega) _
        nlinarith [hbound]
      rw [abs_of_nonneg hsum]
      exact lt_of_lt_of_le hgrowth (hpow.trans hbound)


end Catalan
