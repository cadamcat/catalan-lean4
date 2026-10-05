module

public import Mathlib

/-!
# `Catalan.Stickelberger.CharacterCircle`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
namespace Catalan

lemma exp_two_pi_norm (t : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
  norm_num [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

lemma exp_two_pi_ne_one (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ≠ 1 := by
  intro he
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  have hi := congrArg Complex.im hn
  norm_num [Complex.mul_re, Complex.mul_im] at hi
  have htn : t = (n : ℝ) := by
    apply mul_left_cancel₀ (show (2 : ℝ) * Real.pi ≠ 0 by positivity)
    nlinarith only [hi]
  rw [htn] at ht
  have hn0 : (0 : ℤ) < n := by exact_mod_cast ht.1
  have hn1 : n < (1 : ℤ) := by exact_mod_cast ht.2
  omega

lemma exp_two_pi_pow (t : ℝ) (n : ℕ) :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) ^ n =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * (n : ℂ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

end Catalan
