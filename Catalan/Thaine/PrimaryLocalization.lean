import Catalan.CaseOne.PrimaryUnits
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

set_option autoImplicit false
noncomputable section
namespace Catalan.Thaine

def primaryDenominators (A : Type*) [CommRing A] (q : ℕ) : Submonoid A :=
  (IsUnit.submonoid (UnitQuotient.ModSquare A q)).comap
    (Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A))).toMonoidHom ⊓ nonZeroDivisors A

def primaryLocalization
    (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (q : ℕ) : Subalgebra A K :=
  Localization.subalgebra.ofField K (primaryDenominators A q) inf_le_right

local instance primaryLocalizationIsLocalization
    (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (q : ℕ) :
    IsLocalization (primaryDenominators A q) (primaryLocalization A K q) :=
  Localization.subalgebra.isLocalization_ofField K (primaryDenominators A q) inf_le_right

local instance primaryLocalizationClosed
    (A K : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] (q : ℕ) :
    IsIntegrallyClosed (primaryLocalization A K q) :=
  isIntegrallyClosed_of_isLocalization (primaryLocalization A K q)
    (primaryDenominators A q) inf_le_right

def primaryLocalizationResidue
    (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (q : ℕ) :
    primaryLocalization A K q →+* UnitQuotient.ModSquare A q :=
  IsLocalization.lift (M := primaryDenominators A q)
    (S := primaryLocalization A K q)
    (g := Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A)))
    (fun y => y.property.1)

lemma primaryLocalizationResidue_algebraMap
    (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (q : ℕ) (a : A) :
    primaryLocalizationResidue A K q (algebraMap A (primaryLocalization A K q) a) =
      Ideal.Quotient.mk (Ideal.span ({(q : A) ^ 2} : Set A)) a := by
  unfold primaryLocalizationResidue
  exact IsLocalization.lift_eq _ a

end Catalan.Thaine
