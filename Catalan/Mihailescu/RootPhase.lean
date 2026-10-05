module

public import Catalan.Mihailescu.BoundsDefs
public import Catalan.Mihailescu.Numerical
public import Mathlib

/-!
# `Catalan.Mihailescu.RootPhase`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan
variable (q : ℕ) [Fact q.Prime]

private lemma phase_sin_pi_div_lower (q : ℕ) (hq3 : 3 ≤ q) :
    (5 / 2 : ℝ) / q < Real.sin (Real.pi / q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq3R : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have ht0 : 0 < Real.pi / q := div_pos Real.pi_pos hq
  have ht : Real.pi / q ≤ (21 / 20 : ℝ) := by
    have h := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num : (0 : ℝ) < 3) hq3R
    have hp := Real.pi_lt_d2
    linarith
  have ht2 := pow_le_pow_left₀ ht0.le ht 2
  have ht3 : (Real.pi / q) ^ 3 ≤ (441 / 400 : ℝ) * (Real.pi / q) := by
    have h := mul_le_mul_of_nonneg_right ht2 ht0.le
    nlinarith only [h]
  have hc : (5 / 2 : ℝ) / q < (1959 / 2400 : ℝ) * (Real.pi / q) := by
    rw [← mul_div_assoc, div_lt_div_iff_of_pos_right hq]
    have hp := Real.pi_gt_d2
    nlinarith only [hp]
  have hb : (1959 / 2400 : ℝ) * (Real.pi / q) ≤
      Real.pi / q - (Real.pi / q) ^ 3 / 6 := by
    nlinarith only [ht3]
  exact hc.trans_le (hb.trans (Real.sin_ge_sub_cube ht0.le))

private lemma phase_abs_sin_arg_le (a : ℂ) :
    |Real.sin a.arg| ≤ ‖a - 1‖ := by
  have hd : ‖a - 1‖ ^ 2 = ‖a‖ ^ 2 - 2 * a.re + 1 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    ring
  have hc := Complex.norm_mul_cos_arg a
  have htrig := Real.sin_sq_add_cos_sq a.arg
  have hs : (Real.sin a.arg) ^ 2 ≤ ‖a - 1‖ ^ 2 := by
    nlinarith only [hd, hc, htrig, sq_nonneg (‖a‖ - Real.cos a.arg)]
  simpa only [abs_norm] using (sq_le_sq.mp hs)

lemma root_phase_separation (hq2 : q ≠ 2) (a : ℂ) (ha : a ≠ 0)
    (η : rootsOfUnity q ℂ) (hη : η ≠ 1)
    (hlog : ‖Complex.log (a / ((η : ℂˣ) : ℂ))‖ < Real.pi / q) :
    (5 / 2 : ℝ) / q < ‖a - 1‖ := by
  have hq3 : 3 ≤ q := by have := (Fact.out : q.Prime).two_le; omega
  have hq3R : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have ht0 : 0 < Real.pi / q := div_pos Real.pi_pos hq
  have ht2 : Real.pi / q ≤ Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith)
  by_contra! hclose
  have hdist1 : ‖a - 1‖ < 1 := by
    have hrad : (5 / 2 : ℝ) / q < 1 := (div_lt_one hq).mpr (by linarith)
    exact hclose.trans_lt hrad
  have hre : 0 < a.re := by
    have hh := Complex.abs_re_le_norm (a - 1)
    simp only [Complex.sub_re, Complex.one_re] at hh
    have := (abs_lt.mp (hh.trans_lt hdist1)).1
    linarith
  have harg2 : |a.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hsin : Real.sin |a.arg| < Real.sin (Real.pi / q) := by
    rw [← Real.abs_sin_eq_sin_abs_of_abs_le_pi (Complex.abs_arg_le_pi a)]
    exact (phase_abs_sin_arg_le a).trans_lt (hclose.trans_lt (phase_sin_pi_div_lower q hq3))
  have harg : |a.arg| < Real.pi / q := by
    by_contra! hge
    have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi / q) harg2.le hge
    exact (not_lt_of_ge hmono) hsin
  have hη0 : ((η : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hηq : (((η : ℂˣ) : ℂ)) ^ q = 1 := (mem_rootsOfUnity' q _).mp η.property
  let u := Complex.log a
  let v := Complex.log (a / ((η : ℂˣ) : ℂ))
  have hu : |((q : ℂ) * u).im| < Real.pi := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
      zero_mul, add_zero, u, Complex.log_im, abs_mul, abs_of_pos hq]
    have hh := (lt_div_iff₀ hq).mp harg
    nlinarith only [hh]
  have hv : |((q : ℂ) * v).im| < Real.pi := by
    apply (Complex.abs_im_le_norm _).trans_lt
    rw [norm_mul, Complex.norm_natCast]
    have hh := (lt_div_iff₀ hq).mp hlog
    dsimp [v]
    nlinarith only [hh]
  have hexp : Complex.exp ((q : ℂ) * u) = Complex.exp ((q : ℂ) * v) := by
    simp only [Complex.exp_nat_mul, u, v, Complex.exp_log ha,
      Complex.exp_log (div_ne_zero ha hη0), div_pow, hηq, div_one]
  have huv : u = v := by
    apply mul_left_cancel₀ hqC
    exact Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (abs_lt.mp hu).1 (abs_lt.mp hu).2.le (abs_lt.mp hv).1 (abs_lt.mp hv).2.le hexp
  have hdiv : a = a / ((η : ℂˣ) : ℂ) := by
    simpa only [u, v, Complex.exp_log ha, Complex.exp_log (div_ne_zero ha hη0)]
      using congrArg Complex.exp huv
  apply hη
  apply rootsOfUnity.coe_injective
  have he : a * ((η : ℂˣ) : ℂ) = a := (eq_div_iff hη0).mp hdiv
  apply mul_left_cancel₀ ha
  simpa only [OneMemClass.coe_one, Units.val_one, mul_one] using he

end Catalan

