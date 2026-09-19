import Catalan.IdealAction.Composition

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

private lemma ordinary_idealAct_one
    (F : Type*) [Field F] [NumberField F] (I : FracIdealUnit F) :
    idealAct F (1 : F ≃ₐ[ℚ] F) I = I := by
  apply Units.ext
  apply FractionalIdeal.coeToSubmodule_injective
  change ((I : FracIdeal F).extended F
      (integerAut_preserves_nonZeroDivisors F (1 : F ≃ₐ[ℚ] F)) : Submodule (𝓞 F) F) =
    (I : FracIdeal F)
  rw [FractionalIdeal.coe_extended_eq_span, localization_map_integerAut]
  change Submodule.span (𝓞 F) (id '' ((I : FracIdeal F) : Set F)) = (I : FracIdeal F)
  rw [Set.image_id]
  exact Submodule.span_eq _

lemma exists_ordinary_class_action
    (F : Type*) [Field F] [NumberField F] :
    ∃ act : (F ≃ₐ[ℚ] F) →* Monoid.End (ClassGroup (𝓞 F)),
      ∀ (g : F ≃ₐ[ℚ] F) (I : FracIdealUnit F),
        act g (ClassGroup.mk F I) = ClassGroup.mk F (idealAct F g I) := by
  let S : Subgroup (FracIdealUnit F) := (principalIdeal F).range
  let e : ClassGroup (𝓞 F) ≃* FracIdealUnit F ⧸ S := ClassGroup.equiv F
  have he (I : FracIdealUnit F) : e (ClassGroup.mk F I) = QuotientGroup.mk' S I := by
    change ClassGroup.equiv F (ClassGroup.mk F I) = QuotientGroup.mk' S I
    rw [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self]
    apply congrArg (QuotientGroup.mk' S)
    apply Units.ext
    rfl
  have hS (g : F ≃ₐ[ℚ] F) : S ≤ S.comap (idealAct F g) := by
    rintro I ⟨u, rfl⟩
    exact ⟨elementAct F g u, (idealAct_principalIdeal F g u).symm⟩
  let f (g : F ≃ₐ[ℚ] F) : Monoid.End (ClassGroup (𝓞 F)) :=
    e.symm.toMonoidHom.comp
      ((QuotientGroup.map S S (idealAct F g) (hS g)).comp e.toMonoidHom)
  have hf (g : F ≃ₐ[ℚ] F) (I : FracIdealUnit F) :
      f g (ClassGroup.mk F I) = ClassGroup.mk F (idealAct F g I) := by
    apply e.injective
    change e (e.symm (QuotientGroup.map S S (idealAct F g) (hS g)
      (e (ClassGroup.mk F I)))) = e (ClassGroup.mk F (idealAct F g I))
    rw [e.apply_symm_apply, he, QuotientGroup.map_mk', he]
    rfl
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, hf⟩
  · ext c
    refine ClassGroup.induction (K := F) (fun I => ?_) c
    change f 1 (ClassGroup.mk F I) = ClassGroup.mk F I
    rw [hf, ordinary_idealAct_one]
  · intro g h
    ext c
    refine ClassGroup.induction (K := F) (fun I => ?_) c
    change f (g * h) (ClassGroup.mk F I) = f g (f h (ClassGroup.mk F I))
    rw [hf, hf, hf, idealAct_comp]

end Catalan.Thaine
