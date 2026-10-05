module

public import Catalan.Thaine.LiteralNorms

/-!
# `Catalan.Thaine.LiteralFieldPowers`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma literal_field_action_compat
    (p : ℕ) [Fact p.Prime] (g : G p (A3.Bsub p p)) (a : (A3.F p)ˣ) :
    literalFieldUnitMap p (actUnit p (A3.F p) (literalRestriction p g) a) =
      actUnit p (A3.Bsub p p) g (literalFieldUnitMap p a) := by
  apply Units.ext
  exact literalRestriction_commutes p g (a : A3.F p)

lemma literal_field_upow_compat
    (p : ℕ) [Fact p.Prime] (a : (A3.F p)ˣ) (Theta : R p (A3.Bsub p p)) :
    literalFieldUnitMap p (upow p (A3.F p) a (literalRestrictionRing p Theta)) =
      upow p (A3.Bsub p p) (literalFieldUnitMap p a) Theta := by
  refine MonoidAlgebra.induction_linear Theta ?_ ?_ ?_
  · simp only [map_zero, upow_zero, map_one]
  · intro A B hA hB
    simp only [map_add, upow_add, map_mul, hA, hB]
  · intro g m
    simp only [literalRestrictionRing, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, upow_single, map_zpow, literal_field_action_compat]

lemma literal_field_integral_unit
    (p : ℕ) (u : (𝓞 (A3.F p))ˣ) :
    literalFieldUnitMap p (Units.map (algebraMap (𝓞 (A3.F p)) (A3.F p)).toMonoidHom u) =
      Units.map (algebraMap (𝓞 (A3.Bsub p p)) (A3.Bsub p p)).toMonoidHom (literalRealUnitMap p u) := by
  apply Units.ext
  rfl

end Catalan.Thaine
