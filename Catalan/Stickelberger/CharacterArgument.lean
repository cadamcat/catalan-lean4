import Mathlib

namespace Catalan

lemma arg_one_sub_exp_two_pi (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Complex.arg (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) =
      Real.pi * t - Real.pi / 2 := by
  have hangle0 : 0 < Real.pi * t := mul_pos Real.pi_pos ht.1
  have hangleπ : Real.pi * t < Real.pi := by nlinarith [Real.pi_pos, ht.2]
  have hr : 0 < 2 * Real.sin (Real.pi * t) :=
    mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi hangle0 hangleπ)
  have hstrip : Real.pi * t - Real.pi / 2 ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have he : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) =
      ((2 * (Real.pi * t) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hfactor : 1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) =
      ((2 * Real.sin (Real.pi * t) : ℝ) : ℂ) *
        ((Real.cos (Real.pi * t - Real.pi / 2) : ℂ) +
          (Real.sin (Real.pi * t - Real.pi / 2) : ℂ) * Complex.I) := by
    rw [he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        zero_mul, mul_zero, add_zero, sub_zero,
        Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi * t)]
    · simp only [Complex.sub_im, Complex.one_im, Complex.add_im,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        zero_mul, mul_zero, mul_one, add_zero, zero_add, zero_sub,
        Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, Real.sin_two_mul]
      ring
  rw [hfactor]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
    Complex.arg_mul_cos_add_sin_mul_I hr hstrip

lemma log_one_sub_exp_two_pi_difference (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    -Complex.log (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) +
      Complex.log (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 - t : ℝ) : ℂ))) =
      (2 * Complex.I) * ((Real.pi : ℂ) * ((1 / 2 : ℂ) - (t : ℂ))) := by
  have ht' : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((1 - t : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I + -(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) := by
    push_cast
    ring
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 - t : ℝ) : ℂ)) =
      starRingEnd ℂ (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) := by
    rw [he, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul, ← Complex.exp_conj]
    apply congrArg Complex.exp
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_mul]
  have hconj : 1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 - t : ℝ) : ℂ)) =
      starRingEnd ℂ (1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) := by
    rw [map_sub, map_one, hexp]
  have hnorm : ‖1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((1 - t : ℝ) : ℂ))‖ =
      ‖1 - Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))‖ := by
    rw [hconj, Complex.norm_conj]
  have harg := arg_one_sub_exp_two_pi t ht
  have harg' := arg_one_sub_exp_two_pi (1 - t) ht'
  apply Complex.ext
  · simp only [Complex.add_re, Complex.neg_re, Complex.log_re, hnorm]
    norm_num
  · simp only [Complex.add_im, Complex.neg_im, Complex.log_im, harg, harg']
    norm_num
    ring

end Catalan
