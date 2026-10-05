module

public import Catalan.Thaine.LiteralMaps
public import Catalan.Thaine.IntegralUnitPow

/-!
# `Catalan.Thaine.LiteralRestrictionAction`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma literal_real_unit_action_compat
    (p : ℕ) [Fact p.Prime]
    (g : A3.Bsub p p ≃ₐ[ℚ] A3.Bsub p p) (u : (𝓞 (A3.F p))ˣ) :
    literalRealUnitMap p (Circular.unitAction p (A3.F p) (literalRestriction p g) u) =
      Circular.unitAction p (A3.Bsub p p) g (literalRealUnitMap p u) := by
  have hmapO (x : 𝓞 (A3.F p)) :
      ((algebraMap (𝓞 (A3.F p)) (𝓞 (A3.Bsub p p)) x : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) =
        algebraMap (A3.F p) (A3.Bsub p p) (x : A3.F p) := by
    change ((NumberField.RingOfIntegers.mapRingHom
      (algebraMap (A3.F p) (A3.Bsub p p)) x : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) = _
    rw [NumberField.RingOfIntegers.mapRingHom_apply]
  apply Units.ext
  apply RingOfIntegers.coe_injective
  calc
    ((literalRealUnitMap p (Circular.unitAction p (A3.F p)
      (literalRestriction p g) u) : 𝓞 (A3.Bsub p p)) : A3.Bsub p p) =
        algebraMap (A3.F p) (A3.Bsub p p)
          ((Circular.unitAction p (A3.F p) (literalRestriction p g) u : 𝓞 (A3.F p)) : A3.F p) := by
      rw [literalRealUnitMap, Units.coe_map]
      exact hmapO _
    _ = g (algebraMap (A3.F p) (A3.Bsub p p) (u : A3.F p)) := by
      rw [Circular.unitAction_coe]
      exact literalRestriction_commutes p g (u : A3.F p)
    _ = ((Circular.unitAction p (A3.Bsub p p) g (literalRealUnitMap p u) :
          𝓞 (A3.Bsub p p)) : A3.Bsub p p) := by
      rw [Circular.unitAction_coe, literalRealUnitMap, Units.coe_map]
      exact congrArg g (hmapO (u : 𝓞 (A3.F p))).symm

lemma literal_integralUnitPow_compat
    (p : ℕ) [Fact p.Prime] (u : (𝓞 (A3.F p))ˣ) (Theta : R p (A3.Bsub p p)) :
    literalRealUnitMap p
      (UnitModule.integralUnitPow p (A3.F p) u (literalRestrictionRing p Theta)) =
      UnitModule.integralUnitPow p (A3.Bsub p p) (literalRealUnitMap p u) Theta := by
  refine MonoidAlgebra.induction_linear Theta ?_ ?_ ?_
  · simp only [UnitModule.integralUnitPow_zero, map_zero, map_one]
  · intro A B hA hB
    simp only [map_add, UnitModule.integralUnitPow_add, map_mul, hA, hB]
  · intro g m
    simp only [UnitModule.integralUnitPow_single, literalRestrictionRing,
      MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
      map_zpow, literal_real_unit_action_compat]

end Catalan.Thaine
