import Catalan.Cassels.Hyyro
import Catalan.Mihailescu.BoundsDefs

namespace Catalan

lemma hyyro_implies_h8_one
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp5 : 5 ≤ p) (hpq : p < q)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1) :
    max (mihThreshold p 1) (4 / Real.pi * (q : ℝ) / (p - 1) + 1) ≤ (|x| : ℝ) := by
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
  have hqR : (6 : ℝ) ≤ q := by exact_mod_cast (show 6 ≤ q by omega)
  have hgap : p + 1 ≤ q - 1 := by
    obtain ⟨a, ha⟩ := hp.odd_of_ne_two hp2
    obtain ⟨b, hb⟩ := hq.odd_of_ne_two hq2
    omega
  have hH : (p : ℝ) ^ (q - 1) * ((q : ℝ) - 1) ^ q + 1 ≤ (|x| : ℝ) := by
    exact_mod_cast hyyro_bound p q hp hq hp2 hq2 x y hx hy h
  have hP : (p : ℝ) ^ 2 * 2 ^ (p - 1) ≤ (p : ℝ) ^ (q - 1) := by
    calc
      (p : ℝ) ^ 2 * 2 ^ (p - 1) ≤ (p : ℝ) ^ 2 * (p : ℝ) ^ (p - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by linarith) _)
          (sq_nonneg _)
      _ = (p : ℝ) ^ (p + 1) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ (p : ℝ) ^ (q - 1) := pow_le_pow_right₀ (by linarith) hgap
  have hQ : (q : ℝ) ≤ ((q : ℝ) - 1) ^ q := by
    calc
      (q : ℝ) ≤ ((q : ℝ) - 1) ^ 2 := by nlinarith
      _ ≤ ((q : ℝ) - 1) ^ q := pow_le_pow_right₀ (by linarith) hq.two_le
  have hQ1 : 1 ≤ ((q : ℝ) - 1) ^ q := by linarith
  have hP1 : 1 ≤ (p : ℝ) ^ (q - 1) := one_le_pow₀ (by linarith)
  have hden : 0 < ((p : ℝ) - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have h36 : (36 : ℝ) ≤ (p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2 := by
    have h25 : (25 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have h16 : (16 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have h400 := mul_le_mul h25 h16 (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg (p : ℝ))
    norm_num at h400
    linarith
  have hthreshold : mihThreshold p 1 ≤ (|x| : ℝ) := by
    simp only [mihThreshold, div_one, Real.rpow_one]
    calc
      36 * 2 ^ (p - 1) / ((p : ℝ) - 1) ^ 2 ≤ (p : ℝ) ^ 2 * 2 ^ (p - 1) := by
        apply (div_le_iff₀ hden).mpr
        calc
          36 * 2 ^ (p - 1) ≤ ((p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 2) * 2 ^ (p - 1) :=
            mul_le_mul_of_nonneg_right h36 (by positivity)
          _ = ((p : ℝ) ^ 2 * 2 ^ (p - 1)) * ((p : ℝ) - 1) ^ 2 := by ring
      _ ≤ (p : ℝ) ^ (q - 1) := hP
      _ ≤ (p : ℝ) ^ (q - 1) * ((q : ℝ) - 1) ^ q :=
        le_mul_of_one_le_right (by positivity) hQ1
      _ ≤ (|x| : ℝ) := by linarith
  have hqX : (q : ℝ) + 1 ≤ (|x| : ℝ) := by
    have hm : ((q : ℝ) - 1) ^ q ≤ (p : ℝ) ^ (q - 1) * ((q : ℝ) - 1) ^ q :=
      le_mul_of_one_le_left (by positivity) hP1
    linarith
  have hfactor : 4 / Real.pi / ((p : ℝ) - 1) ≤ 1 := by
    apply (div_le_iff₀ (show 0 < (p : ℝ) - 1 by linarith)).mpr
    simp only [one_mul]
    apply (div_le_iff₀ Real.pi_pos).mpr
    exact (show (4 : ℝ) ≤ (p : ℝ) - 1 by linarith).trans
      (le_mul_of_one_le_right (by linarith) (by linarith [Real.pi_gt_three]))
  apply max_le hthreshold
  calc
    4 / Real.pi * (q : ℝ) / (p - 1) + 1 =
        (4 / Real.pi / ((p : ℝ) - 1)) * q + 1 := by ring
    _ ≤ (q : ℝ) + 1 := by
      have hm := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg q)
      linarith
    _ ≤ (|x| : ℝ) := hqX


end Catalan
