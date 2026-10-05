module

public import Catalan.Density.UnramifiedWitness
public import Catalan.Density.FieldTransport

/-!
# `Catalan.Density.UnramifiedModel`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma exists_unramifiedAbelianQ_model
    (p q : ℕ) (E : Type*) [Field E] [NumberField E] [Algebra (F p) E]
    [IsAbelianGalois (F p) E]
    (hpow : ∀ σ : E ≃ₐ[F p] E, σ ^ q = 1)
    (hunram : ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
      Algebra.IsUnramifiedAt (𝓞 (F p)) P.asIdeal) :
    ∃ J : IntermediateField (F p) Omega,
      UnramifiedAbelianQ p q J ∧ Nonempty (E ≃ₐ[F p] J) := by
  let i : E →ₐ[F p] Omega := IsAlgClosed.lift
  let J := i.fieldRange
  let e : E ≃ₐ[F p] J := i.equivFieldRange
  have instNumberFieldJ : NumberField J := NumberField.of_ringEquiv E J e.toRingEquiv
  have instAbelianJ : IsAbelianGalois (F p) J := IsAbelianGalois.of_algHom e.symm.toAlgHom
  refine ⟨J, ?_, ⟨e⟩⟩
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩
  · exact isMulCommutative_iff.mp (inferInstance : IsMulCommutative (J ≃ₐ[F p] J))
  · intro σ
    obtain ⟨τ, rfl⟩ := e.autCongr.surjective σ
    rw [← map_pow, hpow, map_one]
  · intro P hP hPbot
    let eO := RingOfIntegers.mapRingEquiv e.toRingEquiv
    have hmax : (P.comap eO.toRingHom).IsMaximal :=
      hP.comap_bijective eO.toRingHom eO.bijective
    have hbot : P.comap eO.toRingHom ≠ ⊥ := by
      intro hb
      apply hPbot
      apply Ideal.comap_injective_of_surjective eO.toRingHom eO.surjective
      exact hb.trans (Ideal.comap_bot_of_injective eO.toRingHom eO.injective).symm
    have instMax : (P.comap eO.toRingHom).IsMaximal := hmax
    apply inertiaTrivial_of_equiv_equiv (F p) (F p) E J (RingEquiv.refl (F p))
      e.toRingEquiv (fun x => e.commutes x) P
    exact (inertiaTrivial_iff_isUnramifiedAt (F p) E (P.comap eO.toRingHom) hbot).mpr
      (hunram ⟨P.comap eO.toRingHom, hmax.isPrime, hbot⟩)

end Catalan.A3
