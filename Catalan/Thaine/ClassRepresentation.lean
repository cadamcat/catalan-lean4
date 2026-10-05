module

public import Catalan.Thaine.OrdinaryClassAction
public import Catalan.Thaine.ConjugateResidue
public import Catalan.CaseOne.PowerQuotient

/-!
# `Catalan.Thaine.ClassRepresentation`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

def ordinaryClassAction (F : Type*) [Field F] [NumberField F] :
    (F ≃ₐ[ℚ] F) →* Monoid.End (ClassGroup (𝓞 F)) :=
  Classical.choose (exists_ordinary_class_action F)

lemma ordinaryClassAction_mk
    (F : Type*) [Field F] [NumberField F]
    (g : F ≃ₐ[ℚ] F) (I : FracIdealUnit F) :
    ordinaryClassAction F g (ClassGroup.mk F I) = ClassGroup.mk F (idealAct F g I) :=
  Classical.choose_spec (exists_ordinary_class_action F) g I

def classRepresentation (F : Type*) [Field F] [NumberField F] (q : ℕ) :
    Representation (ZMod q) (F ≃ₐ[ℚ] F)
      (UnitQuotient.PowerQuotient (ClassGroup (𝓞 F)) q) where
  toFun g := UnitQuotient.powerMap q (ordinaryClassAction F g)
  map_one' := by
    apply LinearMap.ext
    intro v
    induction v using QuotientGroup.induction_on with
    | _ c =>
      change UnitQuotient.powerMap q (ordinaryClassAction F 1)
        (UnitQuotient.powerClass q c) = UnitQuotient.powerClass q c
      change UnitQuotient.powerClass q (ordinaryClassAction F 1 c) = UnitQuotient.powerClass q c
      exact congrArg (UnitQuotient.powerClass q)
        (DFunLike.congr_fun (ordinaryClassAction F).map_one c)
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro v
    induction v using QuotientGroup.induction_on with
    | _ c =>
      change UnitQuotient.powerMap q (ordinaryClassAction F (g * h))
        (UnitQuotient.powerClass q c) =
          UnitQuotient.powerMap q (ordinaryClassAction F g)
            (UnitQuotient.powerMap q (ordinaryClassAction F h) (UnitQuotient.powerClass q c))
      change UnitQuotient.powerClass q (ordinaryClassAction F (g * h) c) =
        UnitQuotient.powerClass q (ordinaryClassAction F g (ordinaryClassAction F h c))
      exact congrArg (UnitQuotient.powerClass q)
        (DFunLike.congr_fun ((ordinaryClassAction F).map_mul g h) c)

lemma classRepresentation_powerClass
    (F : Type*) [Field F] [NumberField F] (q : ℕ)
    (g : F ≃ₐ[ℚ] F) (c : ClassGroup (𝓞 F)) :
    classRepresentation F q g (UnitQuotient.powerClass q c) =
      UnitQuotient.powerClass q (ordinaryClassAction F g c) :=
  UnitQuotient.powerMap_apply q (ordinaryClassAction F g) c

lemma classRepresentation_prime
    (F : Type*) [Field F] [NumberField F] (q : ℕ)
    (g : F ≃ₐ[ℚ] F) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    classRepresentation F q g
        (UnitQuotient.powerClass q (ClassGroup.mk F (FractionalIdealGroup.prime v))) =
      UnitQuotient.powerClass q (ClassGroup.mk F (FractionalIdealGroup.prime
        (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv (A3.integralAut g) v))) := by
  rw [classRepresentation_powerClass, ordinaryClassAction_mk, ← conjugate_prime_eq_idealAct]

end Catalan.Thaine
