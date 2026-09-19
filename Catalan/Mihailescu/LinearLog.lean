import Catalan.Mihailescu.Ideal
import Catalan.Mihailescu.LogBounds

set_option autoImplicit false
noncomputable section
namespace Catalan
open NumberField
open scoped BigOperators

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
local instance linearLogFintypeG : Fintype (G p K) := Fintype.ofFinite _

/-- The linear logarithmic lift used in Bilu's Proposition 4.5. -/
def linearLog (φ : K →+* ℂ) (x : ℤ) (Θ : R p K) : ℂ :=
  ∑ τ : G p K, (Θ.coeff τ : ℂ) * Complex.log (1 - φ (τ (ζ p K)) / (x : ℂ))

lemma linearLog_zero (φ : K →+* ℂ) (x : ℤ) :
    linearLog p K φ x 0 = 0 := by
  simp only [linearLog, MonoidAlgebra.coeff_zero, Finsupp.zero_apply,
    Int.cast_zero, zero_mul, Finset.sum_const_zero]

lemma linearLog_add (φ : K →+* ℂ) (x : ℤ) (Θ Ψ : R p K) :
    linearLog p K φ x (Θ + Ψ) = linearLog p K φ x Θ + linearLog p K φ x Ψ := by
  simp only [linearLog, MonoidAlgebra.coeff_add, Finsupp.add_apply,
    Int.cast_add, add_mul, Finset.sum_add_distrib]

lemma linearLog_neg (φ : K →+* ℂ) (x : ℤ) (Θ : R p K) :
    linearLog p K φ x (-Θ) = -linearLog p K φ x Θ := by
  simp only [linearLog, MonoidAlgebra.coeff_neg, Finsupp.neg_apply,
    Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

lemma linearLog_sub (φ : K →+* ℂ) (x : ℤ) (Θ Ψ : R p K) :
    linearLog p K φ x (Θ - Ψ) = linearLog p K φ x Θ - linearLog p K φ x Ψ := by
  rw [sub_eq_add_neg, linearLog_add, linearLog_neg, sub_eq_add_neg]

lemma norm_conj_zeta_div_int (φ : K →+* ℂ) (x : ℤ) (τ : G p K) :
    ‖φ (τ (ζ p K)) / (x : ℂ)‖ = 1 / (|x| : ℝ) := by
  rw [norm_div, norm_conj_zeta p K φ τ]
  congr 1
  simp

lemma conj_zeta_div_int_norm_lt_one (φ : K →+* ℂ) (x : ℤ)
    (hx : 1 < (|x| : ℝ)) (τ : G p K) : ‖φ (τ (ζ p K)) / (x : ℂ)‖ < 1 := by
  rw [norm_conj_zeta_div_int]
  exact (div_lt_one (by linarith)).mpr hx

lemma exp_linearLog (φ : K →+* ℂ) (x : ℤ) (hp2 : p ≠ 2)
    (hx : 1 < (|x| : ℝ)) (Θ : R p K) (hw : weight p K Θ = 0) :
    Complex.exp (linearLog p K φ x Θ) =
      φ ((upow p K (xmζ p K x hp2) Θ : Kˣ) : K) := by
  classical
  have hx0 : x ≠ 0 := by intro h; norm_num [h] at hx
  have hxC : (x : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hx0
  have hfac (τ : G p K) : 1 - φ (τ (ζ p K)) / (x : ℂ) ≠ 0 := by
    intro h
    have he : φ (τ (ζ p K)) / (x : ℂ) = 1 := (sub_eq_zero.mp h).symm
    have hn := conj_zeta_div_int_norm_lt_one p K φ x hx τ
    rw [he, norm_one] at hn
    exact lt_irrefl _ hn
  have hsplit (τ : G p K) : (x : ℂ) - φ (τ (ζ p K)) =
      (x : ℂ) * (1 - φ (τ (ζ p K)) / (x : ℂ)) := by
    field_simp
  have hprod : ∀ s : Finset (G p K), (∏ τ ∈ s, (x : ℂ) ^ Θ.coeff τ) =
      (x : ℂ) ^ (∑ τ ∈ s, Θ.coeff τ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp only [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hxC]
  rw [linearLog, Complex.exp_sum, map_upow_xmζ]
  simp_rw [Complex.exp_int_mul, Complex.exp_log (hfac _), hsplit, mul_zpow]
  rw [Finset.prod_mul_distrib, hprod, ← weight_eq_sum, hw, zpow_zero, one_mul]

lemma linearLog_bound (φ : K →+* ℂ) (x : ℤ)
    (hx : 1 < (|x| : ℝ)) (Θ : R p K) :
    ‖linearLog p K φ x Θ‖ ≤ (size p K Θ : ℝ) / ((|x| : ℝ) - 1) := by
  have hX0 : (|x| : ℝ) ≠ 0 := by linarith
  have hXm : (|x| : ℝ) - 1 ≠ 0 := by linarith
  have hlog (τ : G p K) :
      ‖Complex.log (1 - φ (τ (ζ p K)) / (x : ℂ))‖ ≤ 1 / ((|x| : ℝ) - 1) := by
    have h := log_one_sub_bound (φ (τ (ζ p K)) / (x : ℂ))
      (conj_zeta_div_int_norm_lt_one p K φ x hx τ)
    rw [norm_conj_zeta_div_int] at h
    have he : (1 / (|x| : ℝ)) / (1 - 1 / (|x| : ℝ)) = 1 / ((|x| : ℝ) - 1) := by
      field_simp
    rwa [he] at h
  calc
    ‖linearLog p K φ x Θ‖ ≤ ∑ τ : G p K,
        ‖(Θ.coeff τ : ℂ) * Complex.log (1 - φ (τ (ζ p K)) / (x : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ τ : G p K, ((|Θ.coeff τ| : ℤ) : ℝ) * (1 / ((|x| : ℝ) - 1)) := by
      apply Finset.sum_le_sum
      intro τ _
      rw [norm_mul, Complex.norm_intCast, ← Int.cast_abs]
      exact mul_le_mul_of_nonneg_left (hlog τ) (by positivity)
    _ = (size p K Θ : ℝ) / ((|x| : ℝ) - 1) := by
      simp only [← Finset.sum_mul, ← Int.cast_sum, ← size_eq_sum, div_eq_mul_inv, one_mul]

lemma prop45_principal_log (φ : K →+* ℂ) (x : ℤ) (hp2 : p ≠ 2)
    (hx : 1 < (|x| : ℝ)) (Θ : R p K) (hw : weight p K Θ = 0) :
    ‖Complex.log (φ ((upow p K (xmζ p K x hp2) Θ : Kˣ) : K))‖ ≤
      (size p K Θ : ℝ) / ((|x| : ℝ) - 1) := by
  rw [← exp_linearLog p K φ x hp2 hx Θ hw]
  exact (norm_log_exp_le _).trans (linearLog_bound p K φ x hx Θ)

end Catalan
