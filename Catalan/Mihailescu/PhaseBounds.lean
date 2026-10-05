module

public import Catalan.Mihailescu.PhaseCore
public import Catalan.Mihailescu.RootLog

/-!
# `Catalan.Mihailescu.PhaseBounds`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan
open NumberField
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (q : ℕ) [Fact q.Prime] (x : ℤ) (φ : K →+* ℂ)

lemma xi_small_log (hp2 : p ≠ 2) (hx : 1 < (|x| : ℝ))
    (r : ℝ) (hr : r < Real.pi / 2 * ((|x| : ℝ) - 1))
    (Θ : mihAug p K q x hp2) (hΘ : (size p K Θ.val : ℝ) ≤ 2 * r) :
    ‖Complex.log (alphaC p K q x φ hp2 Θ /
      (((xi p K q x φ hp2 hx Θ : rootsOfUnity q ℂ) : ℂˣ) : ℂ))‖ ≤
        (size p K Θ.val : ℝ) / ((q : ℝ) * ((|x| : ℝ) - 1)) ∧
    (size p K Θ.val : ℝ) / ((q : ℝ) * ((|x| : ℝ) - 1)) < Real.pi / q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hxm : 0 < (|x| : ℝ) - 1 := by linarith
  have ha : alphaC p K q x φ hp2 Θ ≠ 0 := by
    intro h
    apply Units.ne_zero (augAlpha p K q x hp2 Θ)
    apply φ.injective
    simpa only [alphaC, map_zero] using h
  have hquot : alphaC p K q x φ hp2 Θ /
      (((xi p K q x φ hp2 hx Θ : rootsOfUnity q ℂ) : ℂˣ) : ℂ) =
      Complex.exp (linearLog p K φ x Θ.val / (q : ℂ)) := by
    rw [xi_val, phaseValue, div_mul_eq_div_div, div_self ha, one_div,
      neg_div, Complex.exp_neg, inv_inv]
  constructor
  · rw [hquot]
    refine (norm_log_exp_le _).trans ?_
    rw [norm_div, Complex.norm_natCast]
    calc
      ‖linearLog p K φ x Θ.val‖ / (q : ℝ) ≤
          ((size p K Θ.val : ℝ) / ((|x| : ℝ) - 1)) / q :=
        div_le_div_of_nonneg_right (linearLog_bound p K φ x hx Θ.val) hqpos.le
      _ = _ := by rw [div_div, mul_comm]
  · have hs : (size p K Θ.val : ℝ) < Real.pi * ((|x| : ℝ) - 1) := by
      nlinarith only [hΘ, hr]
    rw [div_lt_div_iff₀ (mul_pos hqpos hxm) hqpos]
    nlinarith only [mul_lt_mul_of_pos_right hs hqpos]

lemma xi_unique (hp2 : p ≠ 2) (hx : 1 < (|x| : ℝ))
    (r : ℝ) (hr : r < Real.pi / 2 * ((|x| : ℝ) - 1))
    (Θ : mihAug p K q x hp2) (hΘ : (size p K Θ.val : ℝ) ≤ 2 * r)
    (η : rootsOfUnity q ℂ)
    (hη : ‖Complex.log (alphaC p K q x φ hp2 Θ / ((η : ℂˣ) : ℂ))‖ ≤
      (size p K Θ.val : ℝ) / ((q : ℝ) * ((|x| : ℝ) - 1))) :
    η = xi p K q x φ hp2 hx Θ := by
  have instPhaseQ : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hs := xi_small_log p K q x φ hp2 hx r hr Θ hΘ
  have ha : alphaC p K q x φ hp2 Θ ≠ 0 := by
    intro h
    apply Units.ne_zero (augAlpha p K q x hp2 Θ)
    apply φ.injective
    simpa only [alphaC, map_zero] using h
  exact rootsOfUnity_eq_of_log_div_norm_lt q _ ha η (xi p K q x φ hp2 hx Θ)
    (hη.trans_lt hs.2) (hs.1.trans_lt hs.2)

lemma xi_local_add (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (hx : 1 < (|x| : ℝ)) (r : ℝ)
    (Θ Ψ : mihAug p K q x hp2)
    (_hΘ : (size p K Θ.val : ℝ) ≤ r) (_hΨ : (size p K Ψ.val : ℝ) ≤ r) :
    xi p K q x φ hp2 hx (Θ + Ψ) =
      xi p K q x φ hp2 hx Θ * xi p K q x φ hp2 hx Ψ := by
  exact xi_add p K q x φ hp2 hpq hq2 hx Θ Ψ

end Catalan

