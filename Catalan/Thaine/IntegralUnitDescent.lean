module

public import Mathlib

/-!
# `Catalan.Thaine.IntegralUnitDescent`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma exists_integral_unit_of_field_image
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (u : (𝓞 L)ˣ) (x : F) (hx : algebraMap F L x = ((u : 𝓞 L) : L)) :
    ∃ v : (𝓞 F)ˣ, ((v : 𝓞 F) : F) = x ∧
      Units.map (algebraMap (𝓞 F) (𝓞 L)).toMonoidHom v = u := by
  letI : IsScalarTower ℤ F L :=
    IsScalarTower.of_algebraMap_eq (fun z => by simp)
  have hxi : IsIntegral ℤ x := by
    apply (isIntegral_algebraMap_iff (R := ℤ) (A := F) (B := L) (x := x)).mp
    rw [hx]
    exact (u : 𝓞 L).isIntegral_coe
  have hxinv : algebraMap F L x⁻¹ = (((u⁻¹ : (𝓞 L)ˣ) : 𝓞 L) : L) := by
    rw [map_inv₀, hx]
    exact (map_units_inv (algebraMap (𝓞 L) L) u).symm
  have hxii : IsIntegral ℤ x⁻¹ := by
    apply (isIntegral_algebraMap_iff (R := ℤ) (A := F) (B := L) (x := x⁻¹)).mp
    rw [hxinv]
    exact ((u⁻¹ : (𝓞 L)ˣ) : 𝓞 L).isIntegral_coe
  have hx0 : x ≠ 0 := by
    intro hzero
    have hu0 : ((u : 𝓞 L) : L) = 0 := by rw [← hx, hzero, map_zero]
    exact (Units.map (algebraMap (𝓞 L) L).toMonoidHom u).ne_zero hu0
  let v : (𝓞 F)ˣ :=
    { val := ⟨x, hxi⟩
      inv := ⟨x⁻¹, hxii⟩
      val_inv := RingOfIntegers.ext (mul_inv_cancel₀ hx0)
      inv_val := RingOfIntegers.ext (inv_mul_cancel₀ hx0) }
  refine ⟨v, rfl, ?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  exact hx

end Catalan.Thaine
