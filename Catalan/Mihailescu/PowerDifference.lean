module

public import Catalan.Mihailescu.PhaseCore

/-!
# `Catalan.Mihailescu.PowerDifference`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan
open NumberField
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable (q : ℕ) [Fact q.Prime] (x : ℤ)

lemma prop42_power_difference (hp2 : p ≠ 2)
    (Θ : mihAug p K q x hp2) (σ τ : G p K)
    (hshape : Θ.val = MonoidAlgebra.single σ 1 - MonoidAlgebra.single τ 1) :
    (((augAlpha p K q x hp2 Θ : Kˣ) : K) ^ q) - 1 =
      (τ (ζ p K) - σ (ζ p K)) / ((x : K) - τ (ζ p K)) := by
  let u : Kˣ := xmζ p K x hp2
  have hαpowU : (augAlpha p K q x hp2 Θ) ^ q = upow p K u Θ.val := by
    simpa only [augAlpha, u] using
      (alpha_pow p K q x hp2 ⟨Θ.val, Θ.property.1⟩)
  have hαpowK : ((augAlpha p K q x hp2 Θ : Kˣ) : K) ^ q =
      (upow p K u Θ.val : K) := by
    simpa only [Units.val_pow_eq_pow_val] using
      congrArg (fun a : Kˣ => (a : K)) hαpowU
  have hupowU : upow p K u Θ.val =
      actUnit p K σ u * (actUnit p K τ u)⁻¹ := by
    rw [hshape, sub_eq_add_neg, upow_add, upow_neg, upow_single, upow_single]
    simp only [zpow_one]
  have hσval : (actUnit p K σ u : K) = σ ((x : K) - ζ p K) := by
    change σ ((x : K) - ζ p K) = _
    rfl
  have hτval : (actUnit p K τ u : K) = τ ((x : K) - ζ p K) := by
    change τ ((x : K) - ζ p K) = _
    rfl
  have hτden : (x : K) - τ (ζ p K) ≠ 0 := by
    intro hzero
    have hzero' := congrArg (fun z : K => τ.symm z) hzero
    apply x_sub_ζ_ne_zero p K x hp2
    simpa only [map_sub, map_intCast, map_zero, AlgEquiv.symm_apply_apply] using hzero'
  have hratio : ((augAlpha p K q x hp2 Θ : Kˣ) : K) ^ q =
      ((x : K) - σ (ζ p K)) / ((x : K) - τ (ζ p K)) := by
    rw [hαpowK, hupowU]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, hσval, hτval]
    rw [map_sub, map_intCast, map_sub, map_intCast]
    simp only [div_eq_mul_inv]
  rw [hratio]
  field_simp [hτden]
  ring

end Catalan
