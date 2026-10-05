module

public import Mathlib

/-!
# `Catalan.Mihailescu.RootLog`

Part of the Catalan formalization.
-/

@[expose] public section

namespace Catalan

lemma rootsOfUnity_eq_of_log_div_norm_lt
    (q : ℕ) [NeZero q] (a : ℂ) (ha : a ≠ 0)
    (η ξ : rootsOfUnity q ℂ)
    (hη : ‖Complex.log (a / ((η : ℂˣ) : ℂ))‖ < Real.pi / q)
    (hξ : ‖Complex.log (a / ((ξ : ℂˣ) : ℂ))‖ < Real.pi / q) : η = ξ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hη0 : ((η : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hξ0 : ((ξ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hηq : (((η : ℂˣ) : ℂ)) ^ q = 1 := (mem_rootsOfUnity' q _).mp η.property
  have hξq : (((ξ : ℂˣ) : ℂ)) ^ q = 1 := (mem_rootsOfUnity' q _).mp ξ.property
  let u := Complex.log (a / ((η : ℂˣ) : ℂ))
  let v := Complex.log (a / ((ξ : ℂˣ) : ℂ))
  have hu : ‖(q : ℂ) * u‖ < Real.pi := by
    rw [norm_mul, Complex.norm_natCast]
    have h := (lt_div_iff₀ hq).mp hη
    dsimp [u]
    nlinarith
  have hv : ‖(q : ℂ) * v‖ < Real.pi := by
    rw [norm_mul, Complex.norm_natCast]
    have h := (lt_div_iff₀ hq).mp hξ
    dsimp [v]
    nlinarith
  have hstrip (w : ℂ) (hw : ‖w‖ < Real.pi) :
      -Real.pi < w.im ∧ w.im ≤ Real.pi := by
    have h := (Complex.abs_im_le_norm w).trans_lt hw
    exact ⟨(abs_lt.mp h).1, (abs_lt.mp h).2.le⟩
  have hexp : Complex.exp ((q : ℂ) * u) = Complex.exp ((q : ℂ) * v) := by
    simp only [Complex.exp_nat_mul, u, v, Complex.exp_log (div_ne_zero ha hη0),
      Complex.exp_log (div_ne_zero ha hξ0), div_pow, hηq, hξq, div_one]
  have huv : u = v := by
    apply mul_left_cancel₀ hqC
    exact Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (hstrip _ hu).1 (hstrip _ hu).2 (hstrip _ hv).1 (hstrip _ hv).2 hexp
  have hdiv : a / ((η : ℂˣ) : ℂ) = a / ((ξ : ℂˣ) : ℂ) := by
    simpa only [u, v, Complex.exp_log (div_ne_zero ha hη0),
      Complex.exp_log (div_ne_zero ha hξ0)] using congrArg Complex.exp huv
  apply rootsOfUnity.coe_injective
  exact (mul_left_cancel₀ ha ((div_eq_div_iff hη0 hξ0).mp hdiv)).symm

end Catalan

