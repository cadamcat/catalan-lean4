import Catalan.Thaine.PrimeNormProduct
import Catalan.Thaine.PrimeClassSpan
import Catalan.Thaine.ClassRepresentation
import Catalan.CaseOne.NormSum

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped BigOperators nonZeroDivisors
noncomputable section
namespace Catalan.Thaine

local instance classNormGalFintype (F : Type*) [Field F] [NumberField F] :
    Fintype (F ≃ₐ[ℚ] F) := Fintype.ofFinite _

lemma classRepresentation_norm_prime_eq_zero
    (F : Type*) [Field F] [NumberField F] [IsGalois ℚ F]
    (q : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    (∑ᶠ g : F ≃ₐ[ℚ] F, classRepresentation F q g
      (UnitQuotient.powerClass q (ClassGroup.mk F (FractionalIdealGroup.prime v)))) = 0 := by
  classical
  let J : Ideal (𝓞 F) := Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.relNorm ℤ v.asIdeal)
  have hJ : J ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot
    (Ideal.relNorm_eq_bot_iff.not.mpr v.ne_bot)
  have hJprincipal : J.IsPrincipal := by
    change (Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.relNorm ℤ v.asIdeal)).IsPrincipal
    rw [Ideal.relNorm_int, Ideal.map_span, Set.image_singleton]
    exact ⟨⟨_, rfl⟩⟩
  have hprime : FractionalIdealGroup.prime v = idealUnit F v.asIdeal v.ne_bot := by
    apply Units.ext
    rfl
  have hprod : (∏ g : F ≃ₐ[ℚ] F, idealAct F g (FractionalIdealGroup.prime v)) =
      idealUnit F J hJ := by
    apply Units.ext
    rw [Units.coe_prod, coe_idealUnit]
    have h := congrArg (FractionalIdeal.coeIdealHom (𝓞 F)⁰ F)
      (galois_prime_norm_product F v)
    rw [finprod_eq_prod_of_fintype, map_prod] at h
    calc
      _ = ∏ g : F ≃ₐ[ℚ] F,
          ((Ideal.map (A3.integralAut g).toRingHom v.asIdeal : Ideal (𝓞 F)) : FracIdeal F) := by
        apply Finset.prod_congr rfl
        intro g _
        rw [hprime]
        exact idealAct_idealUnit F g v.asIdeal v.ne_bot
      _ = (J : FracIdeal F) := h
  have hclassJ : ClassGroup.mk F (idealUnit F J hJ) = 1 := by
    unfold idealUnit
    rw [ClassGroup.mk_mk0]
    exact (ClassGroup.mk0_eq_one_iff _).mpr hJprincipal
  have hprodClass : (∏ g : F ≃ₐ[ℚ] F,
      ClassGroup.mk F (idealAct F g (FractionalIdealGroup.prime v))) = 1 := by
    rw [← map_prod, hprod, hclassJ]
  let f : ClassGroup (𝓞 F) →* ClassGroup (𝓞 F) ⧸ UnitQuotient.qPowers (ClassGroup (𝓞 F)) q :=
    QuotientGroup.mk' _
  have hzero := congrArg (fun c : ClassGroup (𝓞 F) => Additive.ofMul (f c)) hprodClass
  rw [finsum_eq_sum_of_fintype]
  simp_rw [classRepresentation_powerClass, ordinaryClassAction_mk]
  simpa only [map_prod, map_one, ofMul_prod, ofMul_one, f, QuotientGroup.mk'_apply,
    UnitQuotient.powerClass] using hzero

lemma classRepresentation_norm_eq_zero
    (F : Type*) [Field F] [NumberField F] [IsGalois ℚ F]
    (q : ℕ) (z : UnitQuotient.PowerQuotient (ClassGroup (𝓞 F)) q) :
    (∑ᶠ g : F ≃ₐ[ℚ] F, classRepresentation F q g z) = 0 := by
  let T : Module.End (ZMod q) (UnitQuotient.PowerQuotient (ClassGroup (𝓞 F)) q) :=
    ∑ g : F ≃ₐ[ℚ] F, classRepresentation F q g
  have hker : ⊤ ≤ LinearMap.ker T := by
    rw [← prime_class_span_top F q]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    change T (UnitQuotient.powerClass q (ClassGroup.mk F (FractionalIdealGroup.prime v))) = 0
    simpa only [T, LinearMap.sum_apply, finsum_eq_sum_of_fintype] using
      classRepresentation_norm_prime_eq_zero F q v
  have hz : T z = 0 := hker (Submodule.mem_top : z ∈ (⊤ : Submodule (ZMod q) _))
  simpa only [T, LinearMap.sum_apply, finsum_eq_sum_of_fintype] using hz

lemma classRepresentation_groupNorm_eq_zero
    (F : Type*) [Field F] [NumberField F] [IsGalois ℚ F]
    (q : ℕ) (z : UnitQuotient.PowerQuotient (ClassGroup (𝓞 F)) q) :
    (classRepresentation F q).asAlgebraHom
      (UnitReduction.groupNorm (ZMod q) (F ≃ₐ[ℚ] F)) z = 0 := by
  simpa only [UnitReduction.groupNorm, map_sum, Representation.asAlgebraHom_single_one,
    LinearMap.sum_apply, finsum_eq_sum_of_fintype] using classRepresentation_norm_eq_zero F q z

end Catalan.Thaine
