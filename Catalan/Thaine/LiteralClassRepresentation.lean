module

public import Catalan.Thaine.LiteralMaps
public import Catalan.Thaine.ClassRepresentation
public import Catalan.Runge.Reduction

/-!
# `Catalan.Thaine.LiteralClassRepresentation`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

def literalClassRepresentation (p q : ℕ) [Fact p.Prime] :
    Representation (ZMod q) (G p (A3.Bsub p p))
      (UnitQuotient.PowerQuotient (ClassGroup (𝓞 (A3.F p))) q) :=
  (classRepresentation (A3.F p) q).comp (literalRestriction p)

lemma literalClassRepresentation_reduce
    (p q : ℕ) [Fact p.Prime] (Theta : R p (A3.Bsub p p)) :
    (literalClassRepresentation p q).asAlgebraHom (Runge.reduceFull p (A3.Bsub p p) q Theta) =
      (classRepresentation (A3.F p) q).asAlgebraHom
        (Runge.reduceFull p (A3.F p) q (literalRestrictionRing p Theta)) := by
  refine MonoidAlgebra.induction_linear Theta ?_ ?_ ?_
  · simp only [map_zero]
  · intro A B hA hB
    simp only [map_add, hA, hB]
  · intro g m
    simp only [literalRestrictionRing, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, Runge.reduceFull, MonoidAlgebra.mapRingHom_single,
      Int.coe_castRingHom, Representation.asAlgebraHom_single]
    rfl

end Catalan.Thaine
