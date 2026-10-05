module

public import Catalan.Density.Definitions
public import Catalan.IdealAction.Composition
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap

/-!
# `Catalan.Thaine.ConjugateResidue`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma residue_map_conjugate
    (F k : Type*) [Field F] [NumberField F] [CommRing k]
    (v : HeightOneSpectrum (𝓞 F)) (g : F ≃ₐ[ℚ] F)
    (red : 𝓞 F →+* k) (hsurj : Function.Surjective red)
    (hker : RingHom.ker red = v.asIdeal) :
    Function.Surjective (red.comp (A3.integralAut g⁻¹).toRingHom) ∧
      RingHom.ker (red.comp (A3.integralAut g⁻¹).toRingHom) =
        (HeightOneSpectrum.equivOfRingEquiv (A3.integralAut g) v).asIdeal := by
  let e : (𝓞 F) ≃+* (𝓞 F) := A3.integralAut g
  have hinv : A3.integralAut g⁻¹ = e.symm := by
    ext x
    simp [e, A3.integralAut, NumberField.RingOfIntegers.mapRingEquiv_apply,
      NumberField.RingOfIntegers.mapRingEquiv_symm_apply]
  constructor
  · intro y
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨e x, ?_⟩
    change red (A3.integralAut g⁻¹ (e x)) = y
    rw [hinv]
    simpa only [RingEquiv.symm_apply_apply] using hx
  · rw [← RingHom.comap_ker, hker, hinv]
    rfl

lemma conjugate_prime_eq_idealAct
    (F : Type*) [Field F] [NumberField F]
    (g : F ≃ₐ[ℚ] F) (v : HeightOneSpectrum (𝓞 F)) :
    FractionalIdealGroup.prime
        (HeightOneSpectrum.equivOfRingEquiv (A3.integralAut g) v) =
      idealAct F g (FractionalIdealGroup.prime v) := by
  let e : (𝓞 F) ≃+* (𝓞 F) := A3.integralAut g
  have hmap : Ideal.map e.toRingHom v.asIdeal =
      (HeightOneSpectrum.equivOfRingEquiv e v).asIdeal := by
    rw [HeightOneSpectrum.equivOfRingEquiv_apply]
    exact Ideal.map_comap_of_equiv (I := v.asIdeal) e
  have hprime : FractionalIdealGroup.prime v =
      Catalan.idealUnit F v.asIdeal v.ne_bot := by
    apply Units.ext
    rfl
  apply Units.ext
  change ((HeightOneSpectrum.equivOfRingEquiv e v).asIdeal :
      FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
    (idealAct F g (FractionalIdealGroup.prime v) :
      FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
  calc
    ((HeightOneSpectrum.equivOfRingEquiv e v).asIdeal :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      ((Ideal.map e.toRingHom v.asIdeal : Ideal (𝓞 F)) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
        rw [hmap]
    _ = (idealAct F g (Catalan.idealUnit F v.asIdeal v.ne_bot) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :=
      (Catalan.idealAct_idealUnit F g v.asIdeal v.ne_bot).symm
    _ = (idealAct F g (FractionalIdealGroup.prime v) :
        FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by rw [hprime]

end Catalan.Thaine
