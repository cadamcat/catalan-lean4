import Mathlib

namespace Catalan

lemma log_one_sub_bound (z : ℂ) (hz : ‖z‖ < 1) :
    ‖Complex.log (1 - z)‖ ≤ ‖z‖ / (1 - ‖z‖) := by
  have h := Complex.norm_log_sub_logTaylor_le 0
    (show ‖-z‖ < 1 by simpa only [norm_neg] using hz)
  simpa [Complex.logTaylor, norm_neg, sub_eq_add_neg, div_eq_mul_inv] using h

lemma norm_log_exp_le (z : ℂ) : ‖Complex.log (Complex.exp z)‖ ≤ ‖z‖ := by
  by_cases hstrip : -Real.pi < z.im ∧ z.im ≤ Real.pi
  · rw [Complex.log_exp hstrip.1 hstrip.2]
  · have hpi : Real.pi ≤ |z.im| := by
      by_cases hlo : -Real.pi < z.im
      · have hhi : Real.pi < z.im := lt_of_not_ge (fun h => hstrip ⟨hlo, h⟩)
        exact hhi.le.trans (le_abs_self _)
      · have h : z.im ≤ -Real.pi := le_of_not_gt hlo
        calc
          Real.pi ≤ -z.im := by linarith
          _ ≤ |z.im| := neg_le_abs _
    have him : |(Complex.log (Complex.exp z)).im| ≤ |z.im| := by
      apply le_trans _ hpi
      exact abs_le.mpr ⟨(Complex.neg_pi_lt_log_im _).le, Complex.log_im_le_pi _⟩
    have hre : (Complex.log (Complex.exp z)).re = z.re := by
      rw [Complex.log_re, Complex.norm_exp, Real.log_exp]
    have hsq : (Complex.log (Complex.exp z)).im ^ 2 ≤ z.im ^ 2 :=
      sq_le_sq.mpr him
    rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    simp only [Complex.normSq_apply, hre]
    nlinarith

end Catalan

