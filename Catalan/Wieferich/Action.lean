module

public import Catalan.Wieferich.Defs
public import Mathlib

/-!
# `Catalan.Wieferich.Action`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField
open scoped BigOperators
namespace Catalan.A1e
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

omit hp [IsCyclotomicExtension {p} ℚ K] in
lemma upow_base_div (a b : Kˣ) (T : R p K) :
    upow p K (a / b) T = upow p K a T / upow p K b T := by
  simp only [upow_fintype, map_div, div_zpow, Finset.prod_div_distrib]

omit hp [IsCyclotomicExtension {p} ℚ K] in
lemma actUnit_one (a : Kˣ) : actUnit p K 1 a = a := by
  apply Units.ext
  rfl

omit hp in
lemma upow_actUnit_commute (a : Kˣ) (T : R p K) (τ : G p K) :
    upow p K (actUnit p K τ a) T = actUnit p K τ (upow p K a T) := by
  classical
  have instGalComm : IsMulCommutative (G p K) :=
    IsCyclotomicExtension.isMulCommutative {p} ℚ K
  simp only [upow_fintype, map_prod, map_zpow]
  apply Finset.prod_congr rfl
  intro σ _
  rw [← actUnit_mul, ← actUnit_mul, mul_comm' σ τ]

lemma upow_minusPart_eq (a : Kˣ) (T : R p K) :
    upow p K a (minusPart p K T) =
      upow p K a T / actUnit p K (ι p K) (upow p K a T) := by
  rw [minusPart, sub_mul, sub_eq_add_neg, upow_add, upow_neg,
    upow_mul_single, upow_mul_single, actUnit_one, div_eq_mul_inv]

lemma upow_minusPart_base (a : Kˣ) (T : R p K) :
    upow p K a (minusPart p K T) = upow p K (a / actUnit p K (ι p K) a) T := by
  rw [upow_minusPart_eq, upow_base_div, upow_actUnit_commute]

omit hp [IsCyclotomicExtension {p} ℚ K] in
lemma upow_pow_eq_one (a : Kˣ) (T : R p K) (n : ℕ) (ha : a ^ n = 1) :
    upow p K a T ^ n = 1 := by
  rw [← upow_pow, ha, upow_base_one]

lemma iota_apply_zeta : ι p K (ζ p K) = (ζ p K)⁻¹ := by
  rw [ι, σ_apply_ζ]
  have hn : (((-1 : (ZMod p)ˣ) : ZMod p)).val = p - 1 := by
    change (-1 : ZMod p).val = p - 1
    rw [ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one'' hp.out.ne_one]
  rw [hn]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le, (ζ_spec p K).pow_eq_one]

lemma minus_root_quotient (d : Kˣ) (hd : (d : K) = 1 - ζ p K) :
    ((d / actUnit p K (ι p K) d : Kˣ) : K) = -ζ p K := by
  simp only [Units.val_div_eq_div_val]
  change (d : K) / ι p K (d : K) = _
  rw [hd, map_sub, map_one, iota_apply_zeta]
  have hz0 : ζ p K ≠ 0 := (ζ_spec p K).ne_zero hp.out.ne_zero
  have hden : 1 - (ζ p K)⁻¹ ≠ 0 := by
    intro h
    have hi : (ζ p K)⁻¹ = 1 := (sub_eq_zero.mp h).symm
    exact (ζ_spec p K).ne_one hp.out.one_lt (inv_eq_one.mp hi)
  apply (div_eq_iff hden).mpr
  field_simp
  ring

end Catalan.A1e
