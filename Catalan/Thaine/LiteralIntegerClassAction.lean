module

public import Catalan.Thaine.IntegralClassAction
public import Catalan.Thaine.LiteralClassRepresentation

/-!
# `Catalan.Thaine.LiteralIntegerClassAction`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

def literalIntegerClassAction (p : ℕ) [Fact p.Prime] :
    R p (A3.Bsub p p) →+* Module.End ℤ (Additive (ClassGroup (𝓞 (A3.F p)))) :=
  (integralClassRepresentation (A3.F p)).asAlgebraHom.toRingHom.comp (literalRestrictionRing p)

lemma literalIntegerClassAction_single
    (p : ℕ) [Fact p.Prime] (g : G p (A3.Bsub p p)) (m : ℤ)
    (a : Additive (ClassGroup (𝓞 (A3.F p)))) :
    literalIntegerClassAction p (MonoidAlgebra.single g m) a =
      m • Additive.ofMul (ordinaryClassAction (A3.F p) (literalRestriction p g) (Additive.toMul a)) := by
  change (integralClassRepresentation (A3.F p)).asAlgebraHom
    (literalRestrictionRing p (MonoidAlgebra.single g m)) a = _
  simp only [literalRestrictionRing, MonoidAlgebra.mapDomainRingHom_apply,
    MonoidAlgebra.mapDomain_single, Representation.asAlgebraHom_single, LinearMap.smul_apply]
  rfl

lemma literalIntegerClassAction_powerClass
    (p q : ℕ) [Fact p.Prime] (Theta : R p (A3.Bsub p p))
    (a : Additive (ClassGroup (𝓞 (A3.F p)))) :
    UnitQuotient.powerClass q (Additive.toMul (literalIntegerClassAction p Theta a)) =
      (literalClassRepresentation p q).asAlgebraHom (Runge.reduceFull p (A3.Bsub p p) q Theta)
        (UnitQuotient.powerClass q (Additive.toMul a)) := by
  rw [literalClassRepresentation_reduce]
  exact powerClass_integralClassRepresentation p q (A3.F p) (literalRestrictionRing p Theta) a

lemma literalIntegerClassAction_image_nsmul
    (p q : ℕ) [Fact p.Prime] (Theta : R p (A3.Bsub p p))
    (hTheta : ∀ z : UnitQuotient.PowerQuotient (ClassGroup (𝓞 (A3.F p))) q,
      (literalClassRepresentation p q).asAlgebraHom
        (Runge.reduceFull p (A3.Bsub p p) q Theta) z = 0) :
    ∀ a : Additive (ClassGroup (𝓞 (A3.F p))), ∃ b : Additive (ClassGroup (𝓞 (A3.F p))),
      literalIntegerClassAction p Theta a = q • b := by
  apply integralClassRepresentation_image_nsmul p q (A3.F p) (literalRestrictionRing p Theta)
  intro z
  simpa only [literalClassRepresentation_reduce] using hTheta z

end Catalan.Thaine
