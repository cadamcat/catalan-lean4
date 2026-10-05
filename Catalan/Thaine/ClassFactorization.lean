module

public import Catalan.IdealAction
public import Catalan.CaseOne.PowerQuotient
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap

/-!
# `Catalan.Thaine.ClassFactorization`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped BigOperators
noncomputable section
namespace Catalan.Thaine

lemma class_power_eq_finsum_multiplicity
    (F : Type*) [Field F] [NumberField F] (q : ℕ)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    UnitQuotient.powerClass q (ClassGroup.mk F (idealUnit F I hI)) =
      ∑ᶠ v : HeightOneSpectrum (𝓞 F),
        multiplicity v.asIdeal I •
          UnitQuotient.powerClass q (ClassGroup.mk F (FractionalIdealGroup.prime v)) := by
  classical
  have hfinite : Function.HasFiniteSupport
      (fun v : HeightOneSpectrum (𝓞 F) => multiplicity v.asIdeal I) := by
    apply (Ideal.finite_factors hI).subset
    intro v hv
    by_contra hnot
    exact hv (multiplicity_eq_zero_of_not_dvd hnot)
  let s : Finset (HeightOneSpectrum (𝓞 F)) := hfinite.toFinset
  have hzero (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ s) :
      multiplicity v.asIdeal I = 0 := by
    by_contra hne
    exact hv (hfinite.mem_toFinset.mpr hne)
  have hprodSupport : Function.mulSupport
      (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal ^ multiplicity v.asIdeal I) ⊆ s := by
    intro v hv
    by_contra hvs
    exact hv (by dsimp only; rw [hzero v hvs, pow_zero])
  have hprod : (∏ v ∈ s, v.asIdeal ^ multiplicity v.asIdeal I) = I :=
    (finprod_eq_prod_of_mulSupport_subset _ hprodSupport).symm.trans
      (Ideal.finprod_heightOneSpectrum_pow_multiplicity hI)
  have hprodUnits : idealUnit F I hI =
      ∏ v ∈ s, (FractionalIdealGroup.prime v) ^ multiplicity v.asIdeal I := by
    apply Units.ext
    rw [coe_idealUnit, Units.coe_prod]
    change (I : FracIdeal F) =
      ∏ v ∈ s, (v.asIdeal : FracIdeal F) ^ multiplicity v.asIdeal I
    have hmap := congrArg (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 F)) F) hprod
    simpa only [map_prod, map_pow, FractionalIdeal.coeIdealHom_apply] using hmap.symm
  have hsumSupport : Function.support
      (fun v : HeightOneSpectrum (𝓞 F) => multiplicity v.asIdeal I •
        UnitQuotient.powerClass q (ClassGroup.mk F (FractionalIdealGroup.prime v))) ⊆ s := by
    intro v hv
    by_contra hvs
    exact hv (by dsimp only; rw [hzero v hvs, zero_nsmul])
  let h : FracIdealUnit F →* (ClassGroup (𝓞 F) ⧸ UnitQuotient.qPowers (ClassGroup (𝓞 F)) q) :=
    (QuotientGroup.mk' (UnitQuotient.qPowers (ClassGroup (𝓞 F)) q)).comp (ClassGroup.mk F)
  have hclasses := congrArg (fun J : FracIdealUnit F => Additive.ofMul (h J)) hprodUnits
  rw [finsum_eq_sum_of_support_subset _ hsumSupport]
  simpa only [map_prod, map_pow, ofMul_prod, ofMul_pow, h, MonoidHom.comp_apply,
    QuotientGroup.mk'_apply, UnitQuotient.powerClass] using hclasses

end Catalan.Thaine
