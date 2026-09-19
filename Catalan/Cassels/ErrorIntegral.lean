import Catalan.Cassels.Denominator
import Catalan.Cassels.RemainderArithmetic

open scoped BigOperators

namespace Catalan

lemma cassels_denexp_strictMono (q : ℕ) (hq : q.Prime) :
    StrictMono (casselsDenExp q) := by
  let : Fact q.Prime := ⟨hq⟩
  apply strictMono_nat_of_lt_succ
  intro k
  simp only [casselsDenExp, Nat.factorial_succ,
    padicValNat.mul (Nat.succ_ne_zero k) (Nat.factorial_ne_zero k)]
  omega

lemma cassels_denexp_bound (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hqp : q < p) :
    casselsDenExp q (casselsIndex p q) ≤ p - 2 := by
  let : Fact q.Prime := ⟨hq⟩
  let m := casselsIndex p q
  have hq3 : 3 ≤ q := by have ht := hq.two_le; omega
  have hp5 : 5 ≤ p := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    omega
  have hm0 : m ≠ 0 := Nat.succ_ne_zero (p / q)
  have hv := sub_one_mul_padicValNat_factorial_lt_of_ne_zero q hm0
  have hdiv := Nat.div_add_mod p q
  have hmq : m * q ≤ p + q := by
    dsimp [m, casselsIndex]
    have := Nat.div_mul_le_self p q
    nlinarith
  have hp1 : p - 1 + 1 = p := by omega
  have hp2' : p - 2 + 2 = p := by omega
  have hq1 : q - 1 + 1 = q := by omega
  have hq2' : q - 2 + 2 = q := by omega
  have hproduct : 3 ≤ (p - 2) * (q - 2) := by
    have h1 : 3 ≤ p - 2 := by omega
    have h2 : 1 ≤ q - 2 := by omega
    calc
      3 = 3 * 1 := by norm_num
      _ ≤ (p - 2) * (q - 2) := Nat.mul_le_mul h1 h2
  have hcomp : p + q ≤ (p - 1) * (q - 1) := by
    have he : (p - 1) * (q - 1) + 3 = p + q + (p - 2) * (q - 2) := by
      calc
        _ = ((p - 2) + 1) * ((q - 2) + 1) + 3 := by
          rw [show p - 1 = (p - 2) + 1 by omega,
            show q - 1 = (q - 2) + 1 by omega]
        _ = ((p - 2) + 2) + ((q - 2) + 2) + (p - 2) * (q - 2) := by ring
        _ = _ := by rw [hp2', hq2']
    omega
  have hmul : (q - 1) * casselsDenExp q m < (q - 1) * (p - 1) := by
    have he : (q - 1) * casselsDenExp q m + m =
        m * q + (q - 1) * padicValNat q m.factorial := by
      dsimp [casselsDenExp]
      calc
        _ = m * ((q - 1) + 1) + (q - 1) * padicValNat q m.factorial := by ring
        _ = _ := by rw [hq1]
    have hfirst : (q - 1) * casselsDenExp q m < m * q := by
      apply Nat.lt_of_add_lt_add_right (n := m)
      rw [he]
      exact Nat.add_lt_add_left hv _
    exact hfirst.trans_le (by simpa only [Nat.mul_comm] using hmq.trans hcomp)
  have hlt : casselsDenExp q m < p - 1 := by
    by_contra hn
    have hn' : p - 1 ≤ casselsDenExp q m := by omega
    have ht := Nat.mul_le_mul_left (q - 1) hn'
    omega
  change casselsDenExp q m ≤ p - 2
  omega

lemma cassels_error_integral_nonzero (p q : ℕ) (hq : q.Prime)
    (hqp : ¬ q ∣ p) (a y : ℤ) :
    ∃ N : ℤ, N ≠ 0 ∧ (N : ℚ) =
      (casselsScale p q : ℚ) * casselsError p q a y := by
  classical
  obtain ⟨B, hBunit, hB⟩ := cassels_coeff_denominator p q hq hqp
  let m := casselsIndex p q
  let E := casselsDenExp q m
  let D : ℤ := (q : ℤ) ^ E
  let c : ℕ → ℤ := fun k => (q : ℤ) ^ (E - casselsDenExp q k) * B k
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hmono := cassels_denexp_strictMono q hq
  have hclear : ∀ k, k ≤ m → (c k : ℚ) = (D : ℚ) * casselsCoeff p q k := by
    intro k hk
    have hEk : casselsDenExp q k ≤ E := hmono.monotone hk
    have he : E - casselsDenExp q k + casselsDenExp q k = E := by omega
    have hpow : (q : ℚ) ^ E =
        (q : ℚ) ^ (E - casselsDenExp q k) * (q : ℚ) ^ casselsDenExp q k := by
      rw [← pow_add, he]
    dsimp [c, D]
    push_cast
    rw [hB k, hpow]
    field_simp [hq0] <;> ring
  have hcdiv : ∀ k, k < m → (q : ℤ) ∣ c k := by
    intro k hk
    have hEk : casselsDenExp q k < E := hmono hk
    have hdelta := Nat.sub_pos_of_lt hEk
    obtain ⟨j, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdelta)
    dsimp [c]
    rw [he, pow_succ]
    refine ⟨(q : ℤ) ^ j * B k, ?_⟩
    ring
  have hcmm : c m = B m := by
    simp only [c, E, Nat.sub_self, pow_zero, one_mul]
  have hmpos : 0 < m := Nat.succ_pos (p / q)
  have hE0 : E ≠ 0 := by
    apply Nat.ne_of_gt
    exact Nat.add_pos_left hmpos _
  have hDdiv : (q : ℤ) ∣ D := dvd_pow_self (q : ℤ) hE0
  let L : ℤ := ∑ k ∈ Finset.range m, c k * a ^ (q * (m - k))
  let N : ℤ := D * a ^ (m * q - p) * y -
    ∑ k ∈ Finset.range (m + 1), c k * a ^ (q * (m - k))
  have hLdiv : (q : ℤ) ∣ L := by
    apply Finset.dvd_sum
    intro k hk
    exact dvd_mul_of_dvd_left (hcdiv k (Finset.mem_range.mp hk)) _
  have hfirst : (q : ℤ) ∣ D * a ^ (m * q - p) * y :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hDdiv _) _
  have hNform : N = D * a ^ (m * q - p) * y - (L + B m) := by
    dsimp [N, L]
    rw [Finset.sum_range_succ, hcmm]
    simp only [Nat.sub_self, mul_zero, pow_zero, mul_one]
  have hN0 : N ≠ 0 := by
    intro h0
    have he : D * a ^ (m * q - p) * y - L = B m := by
      rw [hNform] at h0
      linarith
    have ht := dvd_sub hfirst hLdiv
    rw [he] at ht
    exact hBunit m ht
  refine ⟨N, hN0, ?_⟩
  have hsum :
      (∑ k ∈ Finset.range (m + 1), (c k : ℚ) * (a : ℚ) ^ (q * (m - k))) =
      (D : ℚ) * ∑ k ∈ Finset.range (m + 1),
        casselsCoeff p q k * (a : ℚ) ^ (q * (m - k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hclear k (by have ht := Finset.mem_range.mp hk; omega)]
    ring
  change (N : ℚ) = (D : ℚ) * casselsError p q a y
  dsimp [N, casselsError]
  push_cast
  change (D : ℚ) * (a : ℚ) ^ (m * q - p) * (y : ℚ) -
      (∑ k ∈ Finset.range (m + 1), (c k : ℚ) * (a : ℚ) ^ (q * (m - k))) =
    (D : ℚ) * ((a : ℚ) ^ (m * q - p) * (y : ℚ) -
      ∑ k ∈ Finset.range (m + 1), casselsCoeff p q k * (a : ℚ) ^ (q * (m - k)))
  rw [hsum]
  ring


#print axioms cassels_denexp_bound
#print axioms cassels_error_integral_nonzero

end Catalan
