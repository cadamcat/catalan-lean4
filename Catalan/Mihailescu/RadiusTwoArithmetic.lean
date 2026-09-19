import Catalan.Mihailescu.BoundsDefs
import Catalan.Mihailescu.Numerical

set_option autoImplicit false
noncomputable section
namespace Catalan

lemma prop42_real_contradiction (d n P X H : ℝ) (hd : 0 < d)
    (hn : 0 < n) (hP : 0 < P) (hX : 0 < X)
    (hH : H < Real.log (0.8 * n) + Real.log P / d)
    (hrec : Real.log X ≤ n * H + 3 * Real.log 2)
    (hbig : 8 * (0.8 * n * P ^ (1 / d)) ^ n ≤ X) : False := by
  have hn08 : 0 < 0.8 * n := mul_pos (by norm_num) hn
  have hPpow : 0 < P ^ (1 / d) := Real.rpow_pos_of_pos hP _
  have hbase : 0 < 0.8 * n * P ^ (1 / d) := mul_pos hn08 hPpow
  have hpown : 0 < (0.8 * n * P ^ (1 / d)) ^ n := Real.rpow_pos_of_pos hbase _
  have hlog := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 8) hpown) hbig
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hpown.ne', Real.log_rpow hbase,
    Real.log_mul hn08.ne' hPpow.ne', Real.log_rpow hP, hlog8] at hlog
  have hh := mul_lt_mul_of_pos_left hH hn
  simp only [div_eq_mul_inv, one_mul] at hlog hH hh
  nlinarith

lemma cor43_power_domination (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hpq : p < q) :
    36 * 2 ^ (p - 1) / ((p - 1 : ℝ) ^ 2) ≤ 8 * (0.8 * q) ^ q := by
  have hp3 : 3 ≤ p := by have h := (Fact.out : p.Prime).two_le; omega
  have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hqr : (4 : ℝ) ≤ q := by exact_mod_cast (show 4 ≤ q by omega)
  have hd0 : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hd4 : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
  have ht : 0 ≤ (2 : ℝ) ^ (p - 1) := by positivity
  have hleft : 36 * (2 : ℝ) ^ (p - 1) / ((p - 1 : ℝ) ^ 2) ≤
      9 * (2 : ℝ) ^ (p - 1) := by
    apply (div_le_iff₀ hd0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hd4 ht]
  have hb : (2 : ℝ) ≤ 0.8 * q := by linarith
  have hr : 2 * (2 : ℝ) ^ (p - 1) ≤ (0.8 * q) ^ q := by
    calc
      2 * (2 : ℝ) ^ (p - 1) = (2 : ℝ) ^ p := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      _ ≤ (2 : ℝ) ^ q := pow_le_pow_right₀ (by norm_num) hpq.le
      _ ≤ (0.8 * q) ^ q := pow_le_pow_left₀ (by norm_num) hb q
  exact hleft.trans (by nlinarith)

/-- Bilu's p' in equation (9). -/
def pPrime (p : ℕ) (x : ℤ) : ℕ := if x ≡ 1 [ZMOD p] then 1 else p

lemma pPrime_pos (p : ℕ) [Fact p.Prime] (x : ℤ) : 0 < pPrime p x := by
  unfold pPrime
  split_ifs
  · norm_num
  · exact (Fact.out : p.Prime).pos

lemma radius_ge_one (p q : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (ε : ℝ)
    (hdim : (p : ℝ) ≤ (2 - ε) * q + 1) : 1 ≤ mihRadius p q ε := by
  have hp3 : 3 ≤ p := by have h := (Fact.out : p.Prime).two_le; omega
  have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hd : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  unfold mihRadius
  apply (le_div_iff₀ hd).mpr
  linarith

lemma h9_implies_h8 (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (x : ℤ)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (h9 : (|x| : ℝ) ≥ max (mihThreshold p ε)
      (8 * (0.8 * q * (pPrime p x : ℝ) ^ (1 / (p - 1 : ℝ))) ^ q)) :
    (|x| : ℝ) ≥ max (mihThreshold p ε)
      (4 / Real.pi * (q : ℝ) / (p - 1) + 1) := by
  have hp3 : 3 ≤ p := by have h := (Fact.out : p.Prime).two_le; omega
  have hq3 : 3 ≤ q := by have h := (Fact.out : q.Prime).two_le; omega
  have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hq3r : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hd : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpp : 1 ≤ (pPrime p x : ℝ) := by exact_mod_cast pPrime_pos p x
  have hppr : 1 ≤ (pPrime p x : ℝ) ^ (1 / (p - 1 : ℝ)) :=
    Real.one_le_rpow hpp (le_of_lt (one_div_pos.mpr hd))
  have hb : 0.8 * (q : ℝ) ≤ 0.8 * q * (pPrime p x : ℝ) ^ (1 / (p - 1 : ℝ)) :=
    le_mul_of_one_le_right (by positivity) hppr
  have hb1 : 1 ≤ 0.8 * (q : ℝ) * (pPrime p x : ℝ) ^ (1 / (p - 1 : ℝ)) := by
    linarith
  have hpow : 0.8 * (q : ℝ) * (pPrime p x : ℝ) ^ (1 / (p - 1 : ℝ)) ≤
      (0.8 * (q : ℝ) * (pPrime p x : ℝ) ^ (1 / (p - 1 : ℝ))) ^ q := by
    exact le_self_pow₀ hb1 (Fact.out : q.Prime).ne_zero
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hcoef : 4 / Real.pi ≤ (2 : ℝ) := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    linarith
  have hquot : 4 / Real.pi * (q : ℝ) / (p - 1) ≤ q := by
    apply (div_le_iff₀ hd).mpr
    have h1 := mul_le_mul_of_nonneg_right hcoef (by positivity : (0 : ℝ) ≤ q)
    have h2 := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ p - 1 by linarith)
      (by positivity : (0 : ℝ) ≤ q)
    nlinarith
  apply max_le_iff.mpr
  refine ⟨(max_le_iff.mp h9).1, ?_⟩
  have hlarge := (max_le_iff.mp h9).2
  nlinarith

end Catalan
