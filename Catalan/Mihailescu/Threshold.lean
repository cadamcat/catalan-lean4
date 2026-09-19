import Catalan.Mihailescu.BoundsDefs
import Catalan.Mihailescu.Numerical
import Mathlib

namespace Catalan

lemma h8_consequences (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (x : ℤ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (h8 : (|x| : ℝ) ≥ max (mihThreshold p ε)
      (4 / Real.pi * (q : ℝ) / (p - 1) + 1)) :
    36 ≤ (|x| : ℝ) ∧
    mihRadius p q ε < Real.pi / 2 * ((|x| : ℝ) - 1) ∧
    Real.log (36 * 2 ^ (p - 1) / ((p - 1 : ℝ) ^ 2)) ≤
      ε * Real.log (|x| : ℝ) := by
  have hp3 : 3 ≤ p := by
    have hp2' := (Fact.out : p.Prime).two_le
    omega
  have hp3r : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hdpos : 0 < (p : ℝ) - 1 := by linarith
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast (Fact.out : q.Prime).pos
  have hpi : 0 < Real.pi := Real.pi_pos
  let B : ℝ := 36 * 2 ^ (p - 1) / ((p - 1 : ℝ) ^ 2)
  have hBpow : ((p - 1 : ℝ) ^ 2) ≤ (2 : ℝ) ^ (p - 1) :=
    even_degree_power_bound p hp2
  have hBsquarepos : 0 < ((p - 1 : ℝ) ^ 2) := sq_pos_of_pos hdpos
  have hB36 : 36 ≤ B := by
    dsimp [B]
    apply (le_div_iff₀ hBsquarepos).2
    exact mul_le_mul_of_nonneg_left hBpow (by norm_num)
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB36
  have hB1 : 1 ≤ B := by linarith
  have hεinv : (1 : ℝ) ≤ 1 / ε := by
    apply (le_div_iff₀ hε0).2
    linarith
  have hB_rpow : B ≤ B ^ (1 / ε) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hB1 hεinv)
  have hXT : B ^ (1 / ε) ≤ (|x| : ℝ) := by
    have hmax := (le_max_left (mihThreshold p ε)
      (4 / Real.pi * (q : ℝ) / (p - 1) + 1)).trans h8
    simpa only [mihThreshold, B] using hmax
  have hX36 : 36 ≤ (|x| : ℝ) := hB36.trans (hB_rpow.trans hXT)
  have hXS : 4 / Real.pi * (q : ℝ) / (p - 1) + 1 ≤ (|x| : ℝ) :=
    (le_max_right (mihThreshold p ε)
      (4 / Real.pi * (q : ℝ) / (p - 1) + 1)).trans h8
  have hXminus : 4 / Real.pi * (q : ℝ) / ((p : ℝ) - 1) ≤
      (|x| : ℝ) - 1 := by
    linarith
  have hradlt : (2 - ε) * (q : ℝ) / ((p : ℝ) - 1) <
      2 * (q : ℝ) / ((p : ℝ) - 1) := by
    apply (div_lt_div_iff_of_pos_right hdpos).2
    exact mul_lt_mul_of_pos_right (by linarith) hqpos
  have hradbound : 2 * (q : ℝ) / ((p : ℝ) - 1) ≤
      Real.pi / 2 * ((|x| : ℝ) - 1) := by
    calc
      2 * (q : ℝ) / ((p : ℝ) - 1) =
          (Real.pi / 2) * (4 / Real.pi * (q : ℝ) / ((p : ℝ) - 1)) := by
            field_simp [ne_of_gt hpi, ne_of_gt hdpos]
            ring
      _ ≤ (Real.pi / 2) * ((|x| : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hXminus (by positivity)
  have hrad : mihRadius p q ε < Real.pi / 2 * ((|x| : ℝ) - 1) := by
    simpa only [mihRadius] using hradlt.trans_le hradbound
  have hlogT : Real.log (B ^ (1 / ε)) ≤ Real.log (|x| : ℝ) :=
    Real.log_le_log (Real.rpow_pos_of_pos hBpos _) hXT
  have hlogB : Real.log B ≤ ε * Real.log (|x| : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlogT hε0.le
    rw [Real.log_rpow hBpos] at hmul
    calc
      Real.log B = ε * ((1 / ε) * Real.log B) := by
        field_simp [ne_of_gt hε0]
      _ ≤ ε * Real.log (|x| : ℝ) := by
        simpa only [mul_assoc] using hmul
  refine ⟨hX36, hrad, ?_⟩
  simpa only [B] using hlogB

end Catalan
