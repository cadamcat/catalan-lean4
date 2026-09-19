import Catalan.Thaine.ClassFactorization

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors
noncomputable section
namespace Catalan.Thaine

lemma multiplicity_hasFiniteSupport
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (I : Ideal R) (hI : I ≠ ⊥) :
    Function.HasFiniteSupport (fun v : HeightOneSpectrum R => multiplicity v.asIdeal I) := by
  apply (Ideal.finite_factors hI).subset
  intro v hv
  exact dvd_of_multiplicity_pos (Nat.pos_of_ne_zero hv)

lemma principal_class_finsum_eq_zero
    (F : Type*) [Field F] [NumberField F] (q : ℕ)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hprincipal : I.IsPrincipal) :
    (∑ᶠ v : HeightOneSpectrum (𝓞 F),
      multiplicity v.asIdeal I •
        UnitQuotient.powerClass q (ClassGroup.mk F (FractionalIdealGroup.prime v))) = 0 := by
  rw [← class_power_eq_finsum_multiplicity F q I hI]
  have hclass : ClassGroup.mk F (idealUnit F I hI) = 1 := by
    unfold idealUnit
    rw [ClassGroup.mk_mk0]
    exact (ClassGroup.mk0_eq_one_iff _).mpr hprincipal
  rw [hclass]
  rfl

end Catalan.Thaine
