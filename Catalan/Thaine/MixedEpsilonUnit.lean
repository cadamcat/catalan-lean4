import Catalan.Thaine.MixedRootUnits

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma exists_mixed_epsilon_unit
    (K : Type*) [Field K] [NumberField K]
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpe : p ≠ ell)
    (z w : K) (hz : IsPrimitiveRoot z p) (hw : IsPrimitiveRoot w ell)
    (a : (ZMod p)ˣ) (m : ℤ) :
    ∃ u : (𝓞 K)ˣ, ((u : 𝓞 K) : K) =
      z ^ m * (z ^ (a : ZMod p).val - w) / (z - w) := by
  have hza : IsPrimitiveRoot (z ^ (a : ZMod p).val) p :=
    hz.pow_of_coprime _ (ZMod.val_coe_unit_coprime a)
  have hnum := primitive_roots_difference_isUnit K p ell hpe _ w hza hw
  have hden := primitive_roots_difference_isUnit K p ell hpe z w hz hw
  have hzunit := hz.toInteger_isPrimitiveRoot.isUnit (Fact.out : p.Prime).ne_zero
  let uz : (𝓞 K)ˣ := hzunit.unit
  let un : (𝓞 K)ˣ := hnum.unit
  let ud : (𝓞 K)ˣ := hden.unit
  have huz : ((uz : 𝓞 K) : K) = z := by
    rw [show (uz : 𝓞 K) = hz.toInteger from hzunit.unit_spec]
    rfl
  have hun : ((un : 𝓞 K) : K) = z ^ (a : ZMod p).val - w := by
    rw [show (un : 𝓞 K) = hza.toInteger - hw.toInteger from hnum.unit_spec]
    rfl
  have hud : ((ud : 𝓞 K) : K) = z - w := by
    rw [show (ud : 𝓞 K) = hz.toInteger - hw.toInteger from hden.unit_spec]
    rfl
  refine ⟨uz ^ m * un / ud, ?_⟩
  change ((Units.map (algebraMap (𝓞 K) K).toMonoidHom
    (uz ^ m * un / ud) : Kˣ) : K) = _
  rw [map_div, map_mul, map_zpow]
  simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_zpow_eq_zpow_val,
    Units.coe_map]
  change ((uz : 𝓞 K) : K) ^ m * ((un : 𝓞 K) : K) / ((ud : 𝓞 K) : K) = _
  rw [huz, hun, hud]

end Catalan.Thaine
