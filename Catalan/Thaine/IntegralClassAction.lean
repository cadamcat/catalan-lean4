module

public import Catalan.Thaine.ClassRepresentation
public import Catalan.Runge.Reduction

/-!
# `Catalan.Thaine.IntegralClassAction`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

def integralClassRepresentation (F : Type*) [Field F] [NumberField F] :
    Representation ℤ (F ≃ₐ[ℚ] F) (Additive (ClassGroup (𝓞 F))) where
  toFun g := (ordinaryClassAction F g).toAdditive.toIntLinearMap
  map_one' := by
    apply LinearMap.ext
    intro a
    change Additive.ofMul (ordinaryClassAction F 1 (Additive.toMul a)) =
      Additive.ofMul (Additive.toMul a)
    exact congrArg Additive.ofMul (DFunLike.congr_fun (ordinaryClassAction F).map_one (Additive.toMul a))
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro a
    change Additive.ofMul (ordinaryClassAction F (g * h) (Additive.toMul a)) =
      Additive.ofMul (ordinaryClassAction F g (ordinaryClassAction F h (Additive.toMul a)))
    exact congrArg Additive.ofMul
      (DFunLike.congr_fun ((ordinaryClassAction F).map_mul g h) (Additive.toMul a))

lemma integralClassRepresentation_apply
    (F : Type*) [Field F] [NumberField F]
    (g : F ≃ₐ[ℚ] F) (c : ClassGroup (𝓞 F)) :
    integralClassRepresentation F g (Additive.ofMul c) =
      Additive.ofMul (ordinaryClassAction F g c) := rfl

lemma powerClass_integralClassRepresentation
    (p q : ℕ) (F : Type*) [Field F] [NumberField F]
    (Theta : R p F) (a : Additive (ClassGroup (𝓞 F))) :
    UnitQuotient.powerClass q
        (Additive.toMul ((integralClassRepresentation F).asAlgebraHom Theta a)) =
      (classRepresentation F q).asAlgebraHom (Runge.reduceFull p F q Theta)
        (UnitQuotient.powerClass q (Additive.toMul a)) := by
  let pi : Additive (ClassGroup (𝓞 F)) →+
      UnitQuotient.PowerQuotient (ClassGroup (𝓞 F)) q :=
    (QuotientGroup.mk' (UnitQuotient.qPowers (ClassGroup (𝓞 F)) q)).toAdditive
  change pi ((integralClassRepresentation F).asAlgebraHom Theta a) =
    (classRepresentation F q).asAlgebraHom (Runge.reduceFull p F q Theta) (pi a)
  refine MonoidAlgebra.induction_linear Theta ?_ ?_ ?_
  · simp only [map_zero, LinearMap.zero_apply]
  · intro A B hA hB
    simp only [map_add, LinearMap.add_apply, hA, hB]
  · intro g m
    simp only [Runge.reduceFull, MonoidAlgebra.mapRingHom_single, Int.coe_castRingHom,
      Representation.asAlgebraHom_single, LinearMap.smul_apply]
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
    congr 1

lemma integralClassRepresentation_image_nsmul
    (p q : ℕ) (F : Type*) [Field F] [NumberField F] (Theta : R p F)
    (hTheta : ∀ z : UnitQuotient.PowerQuotient (ClassGroup (𝓞 F)) q,
      (classRepresentation F q).asAlgebraHom (Runge.reduceFull p F q Theta) z = 0) :
    ∀ a : Additive (ClassGroup (𝓞 F)), ∃ b : Additive (ClassGroup (𝓞 F)),
      (integralClassRepresentation F).asAlgebraHom Theta a = q • b := by
  intro a
  have hz : UnitQuotient.powerClass q
      (Additive.toMul ((integralClassRepresentation F).asAlgebraHom Theta a)) = 0 :=
    (powerClass_integralClassRepresentation p q F Theta a).trans (hTheta _)
  change (QuotientGroup.mk (Additive.toMul ((integralClassRepresentation F).asAlgebraHom Theta a)) :
    ClassGroup (𝓞 F) ⧸ UnitQuotient.qPowers (ClassGroup (𝓞 F)) q) = 1 at hz
  obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff _).mp hz
  refine ⟨Additive.ofMul b, ?_⟩
  exact congrArg Additive.ofMul hb.symm

end Catalan.Thaine
