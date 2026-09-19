import Catalan.Thaine.ClassFactorization
import Catalan.Thaine.PrincipalClassRelation

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma prime_class_span_top
    (F : Type*) [Field F] [NumberField F] (q : ℕ) :
    Submodule.span (ZMod q)
      (Set.range (fun v : HeightOneSpectrum (𝓞 F) =>
        UnitQuotient.powerClass q (ClassGroup.mk F (FractionalIdealGroup.prime v)))) = ⊤ := by
  classical
  let W := Submodule.span (ZMod q)
    (Set.range (fun v : HeightOneSpectrum (𝓞 F) =>
      UnitQuotient.powerClass q (ClassGroup.mk F (FractionalIdealGroup.prime v))))
  change W = ⊤
  apply top_unique
  intro x _
  induction x using QuotientGroup.induction_on with
  | _ c =>
    change UnitQuotient.powerClass q c ∈ W
    obtain ⟨I, hIc⟩ := ClassGroup.mk0_surjective (R := 𝓞 F) c
    have hI : (I : Ideal (𝓞 F)) ≠ ⊥ :=
      mem_nonZeroDivisors_iff_ne_zero.mp I.property
    have hclass : ClassGroup.mk F (idealUnit F (I : Ideal (𝓞 F)) hI) = c := by
      unfold idealUnit
      rw [ClassGroup.mk_mk0]
      exact hIc
    rw [← hclass, class_power_eq_finsum_multiplicity F q (I : Ideal (𝓞 F)) hI]
    have hfinite : Function.HasFiniteSupport
        (fun v : HeightOneSpectrum (𝓞 F) => multiplicity v.asIdeal (I : Ideal (𝓞 F)) •
          UnitQuotient.powerClass q (ClassGroup.mk F (FractionalIdealGroup.prime v))) := by
      apply (multiplicity_hasFiniteSupport (𝓞 F) (I : Ideal (𝓞 F)) hI).subset
      intro v hv hzero
      apply hv
      dsimp only at hzero ⊢
      rw [hzero, zero_nsmul]
    rw [finsum_eq_sum _ hfinite]
    apply W.sum_mem
    intro v _
    simpa only [Nat.cast_smul_eq_nsmul] using
      W.smul_mem (multiplicity v.asIdeal (I : Ideal (𝓞 F)) : ZMod q)
        (Submodule.subset_span ⟨v, rfl⟩)

end Catalan.Thaine
