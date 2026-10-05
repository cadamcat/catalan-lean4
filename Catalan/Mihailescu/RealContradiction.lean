module

public import Catalan.Mihailescu.BoundsDefs
public import Catalan.Mihailescu.Numerical
public import Mathlib

/-!
# `Catalan.Mihailescu.RealContradiction`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan

lemma prop49_real_contradiction (d : ℕ) (hd : 2 ≤ d)
    (n X ε s H U : ℝ) (hn : 0 < n) (hX : 36 ≤ X)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hs0 : 0 < s)
    (hs : s ≤ 2 * ((2 - ε) * n / (d : ℝ)))
    (hthreshold : Real.log (36 * 2 ^ d / ((d : ℝ) ^ 2)) ≤ ε * Real.log X)
    (hH : H ≤ s / (2 * n) * Real.log (X + 1) + Real.log 2)
    (hU0 : 0 ≤ U) (hU : U ≤ (7 / 5 : ℝ) * (s / (n * (X - 1))))
    (hL : Real.exp (-((d : ℝ) * H)) ≤ U ^ 2) : False := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hXpos : 0 < X := by linarith
  have hXmpos : 0 < X - 1 := by linarith
  have hXppos : 0 < X + 1 := by linarith
  have hsd : s * (d : ℝ) ≤ 2 * (2 - ε) * n := by
    calc
      s * (d : ℝ) ≤ (2 * ((2 - ε) * n / (d : ℝ))) * d :=
        mul_le_mul_of_nonneg_right hs hdpos.le
      _ = 2 * (2 - ε) * n := by field_simp
  have hcoef : (d : ℝ) * (s / (2 * n)) ≤ 2 - ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2 * n)).mpr
    nlinarith
  have hlogXp : 0 ≤ Real.log (X + 1) := Real.log_nonneg (by linarith)
  have hH' : (d : ℝ) * H ≤ (2 - ε) * Real.log (X + 1) + d * Real.log 2 := by
    calc
      (d : ℝ) * H ≤ d * (s / (2 * n) * Real.log (X + 1) + Real.log 2) :=
        mul_le_mul_of_nonneg_left hH hdpos.le
      _ ≤ (2 - ε) * Real.log (X + 1) + d * Real.log 2 := by
        rw [mul_add, ← mul_assoc]
        exact add_le_add (mul_le_mul_of_nonneg_right hcoef hlogXp) le_rfl
  have hsn : s / n ≤ 4 / (d : ℝ) := by
    apply (div_le_div_iff₀ hn hdpos).mpr
    nlinarith [mul_pos hε0 hn]
  have hUB : U ≤ ((28 / 5 : ℝ) / (d : ℝ)) / (X - 1) := by
    calc
      U ≤ (7 / 5 : ℝ) * (s / (n * (X - 1))) := hU
      _ = ((7 / 5 : ℝ) * (s / n)) / (X - 1) := by
        field_simp
      _ ≤ ((7 / 5 : ℝ) * (4 / (d : ℝ))) / (X - 1) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsn (by norm_num)) hXmpos.le
      _ = ((28 / 5 : ℝ) / (d : ℝ)) / (X - 1) := by ring
  have hUpos : 0 < U := by nlinarith [Real.exp_pos (-((d : ℝ) * H))]
  have hLlog := Real.log_le_log (Real.exp_pos (-((d : ℝ) * H))) hL
  rw [Real.log_exp, Real.log_pow] at hLlog
  have hUlog := Real.log_le_log hUpos hUB
  rw [Real.log_div (by positivity) hXmpos.ne',
    Real.log_div (by norm_num) hdpos.ne'] at hUlog
  have hεlog : ε * Real.log X ≤ ε * Real.log (X + 1) :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hXpos (by linarith)) hε0.le
  have hratio : (X + 1) / (X - 1) ≤ (37 / 35 : ℝ) := by
    apply (div_le_iff₀ hXmpos).mpr
    linarith
  have hratioLog : Real.log (X + 1) - Real.log (X - 1) ≤ Real.log (37 / 35 : ℝ) := by
    rw [← Real.log_div hXppos.ne' hXmpos.ne']
    exact Real.log_le_log (div_pos hXppos hXmpos) hratio
  have ht := hthreshold
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at ht
  have hfinal : Real.log 36 ≤ 2 * Real.log (28 / 5 : ℝ) + 2 * Real.log (37 / 35 : ℝ) := by
    norm_num only [Nat.cast_ofNat] at hLlog ht
    nlinarith
  have hconstant : 2 * Real.log (28 / 5 : ℝ) + 2 * Real.log (37 / 35 : ℝ) < Real.log 36 := by
    calc
      _ = Real.log (((28 / 5 : ℝ) * (37 / 35 : ℝ)) ^ 2) := by
        rw [Real.log_pow, Real.log_mul (by norm_num) (by norm_num)]
        norm_num
        ring
      _ < Real.log 36 := Real.log_lt_log (by norm_num) (by norm_num)
  exact (not_lt_of_ge hfinal) hconstant

end Catalan

