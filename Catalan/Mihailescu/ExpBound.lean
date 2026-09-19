import Mathlib

namespace Catalan

lemma expm1_seven_fifths (z : ℂ) (hz : ‖z‖ ≤ Real.pi / 5) :
    ‖Complex.exp z - 1‖ ≤ (7 / 5 : ℝ) * ‖z‖ := by
  have hr0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hr : ‖z‖ ≤ (63 / 100 : ℝ) := by
    have hpi := Real.pi_lt_d2
    linarith
  have hr1 : ‖z‖ ≤ 1 := by linarith
  have ht := Complex.exp_bound (x := z) hr1 (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ] at ht
  have hpoly : ‖z + z ^ 2 / 2 + z ^ 3 / 6‖ ≤ ‖z‖ + ‖z‖ ^ 2 / 2 + ‖z‖ ^ 3 / 6 := by
    calc
      ‖z + z ^ 2 / 2 + z ^ 3 / 6‖ ≤ ‖z + z ^ 2 / 2‖ + ‖z ^ 3 / 6‖ :=
        norm_add_le _ _
      _ ≤ (‖z‖ + ‖z ^ 2 / 2‖) + ‖z ^ 3 / 6‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by norm_num [norm_div, norm_pow]
  have htotal : ‖Complex.exp z - 1‖ ≤
      ‖Complex.exp z - (1 + z + z ^ 2 / 2 + z ^ 3 / 6)‖ +
        ‖z + z ^ 2 / 2 + z ^ 3 / 6‖ := by
    have h := norm_add_le (Complex.exp z - (1 + z + z ^ 2 / 2 + z ^ 3 / 6))
      (z + z ^ 2 / 2 + z ^ 3 / 6)
    convert h using 1
    congr 1
    ring
  have hpow (n : ℕ) : ‖z‖ ^ (n + 1) ≤ ‖z‖ * (63 / 100 : ℝ) ^ n := by
    rw [pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr n) hr0
  have h2 := hpow 1
  have h3 := hpow 2
  have h4 := hpow 3
  norm_num at h2 h3 h4
  nlinarith

end Catalan

