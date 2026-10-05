module

public import Mathlib

/-!
# `Catalan.Thaine.ResidueExtension`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma exists_residue_extension_of_inertia_one
    (F L k : Type*) [Field F] [NumberField F] [Field L] [NumberField L] [Field k]
    [Algebra F L] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver v.asIdeal] (hf : P.asIdeal.inertiaDeg (𝓞 F) = 1)
    (red : 𝓞 F →+* k) (hsurj : Function.Surjective red) (hker : RingHom.ker red = v.asIdeal) :
    ∃ redL : 𝓞 L →+* k, Function.Surjective redL ∧ RingHom.ker redL = P.asIdeal ∧
      ∀ x : 𝓞 F, redL (algebraMap (𝓞 F) (𝓞 L) x) = red x := by
  let residueExtensionBaseField : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let residueExtensionTopField : Field (𝓞 L ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  have hdim : Module.finrank (𝓞 F ⧸ v.asIdeal) (𝓞 L ⧸ P.asIdeal) = 1 := by
    rw [← Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal P.asIdeal]
    exact hf
  have hbij : Function.Bijective (algebraMap (𝓞 F ⧸ v.asIdeal) (𝓞 L ⧸ P.asIdeal)) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdim
  let e : (𝓞 F ⧸ v.asIdeal) ≃+* (𝓞 L ⧸ P.asIdeal) :=
    RingEquiv.ofBijective (algebraMap (𝓞 F ⧸ v.asIdeal) (𝓞 L ⧸ P.asIdeal)) hbij
  let b : (𝓞 F ⧸ v.asIdeal) ≃+* k :=
    (Ideal.quotEquivOfEq hker.symm).trans (red.quotientKerEquivOfSurjective hsurj)
  let E : (𝓞 L ⧸ P.asIdeal) ≃+* k := e.symm.trans b
  let redL : 𝓞 L →+* k := E.toRingHom.comp (Ideal.Quotient.mk P.asIdeal)
  refine ⟨redL, E.surjective.comp Ideal.Quotient.mk_surjective, ?_, ?_⟩
  · ext x
    change E (Ideal.Quotient.mk P.asIdeal x) = 0 ↔ x ∈ P.asIdeal
    constructor
    · intro hx
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply E.injective
      simpa only [map_zero] using hx
    · intro hx
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · intro x
    change E (Ideal.Quotient.mk P.asIdeal (algebraMap (𝓞 F) (𝓞 L) x)) = red x
    rw [← Ideal.Quotient.algebraMap_mk_of_liesOver P.asIdeal v.asIdeal x]
    change b (e.symm (e (Ideal.Quotient.mk v.asIdeal x))) = red x
    rw [e.symm_apply_apply]
    change red.quotientKerEquivOfSurjective hsurj
      (Ideal.quotEquivOfEq hker.symm (Ideal.Quotient.mk v.asIdeal x)) = red x
    rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

end Catalan.Thaine
