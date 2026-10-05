module

public import Catalan.Density.FieldTransport
public import Catalan.Density.ConjugateField

/-!
# `Catalan.Density.ConjugateWitness`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma unramifiedAbelianQ_of_equiv_equiv
    (p q : ℕ) (J J' : IntermediateField (F p) Omega)
    (f : F p ≃+* F p) (e : J ≃+* J')
    (hcompat : ∀ x, e (algebraMap (F p) J x) = algebraMap (F p) J' (f x))
    (hJ : UnramifiedAbelianQ p q J) : UnramifiedAbelianQ p q J' := by
  have instFiniteJ : FiniteDimensional (F p) J := hJ.1
  have instNumberFieldJ : NumberField J := NumberField.of_module_finite (F p) J
  have instNumberFieldJ' : NumberField J' := NumberField.of_ringEquiv J J' e
  have instGaloisJ : IsGalois (F p) J := hJ.2.1
  have instGaloisJ' : IsGalois (F p) J' := IsGalois.of_equiv_equiv (f := f) (g := e) (by
    apply RingHom.ext
    intro x
    exact (hcompat x).symm)
  let E := galEquivOfFieldEquivs (F p) (F p) J J' f e hcompat
  refine ⟨inferInstance, instGaloisJ', ?_, ?_, ?_⟩
  · intro σ τ
    obtain ⟨s, rfl⟩ := E.surjective σ
    obtain ⟨t, rfl⟩ := E.surjective τ
    rw [← map_mul, ← map_mul, hJ.2.2.1 s t]
  · intro σ
    obtain ⟨s, rfl⟩ := E.surjective σ
    rw [← map_pow, hJ.2.2.2.1 s, map_one]
  · intro P hP hPbot
    let eO := RingOfIntegers.mapRingEquiv e
    have hmax : (P.comap eO.toRingHom).IsMaximal :=
      hP.comap_bijective eO.toRingHom eO.bijective
    have hbot : P.comap eO.toRingHom ≠ ⊥ := by
      intro hb
      apply hPbot
      apply Ideal.comap_injective_of_surjective eO.toRingHom eO.surjective
      exact hb.trans (Ideal.comap_bot_of_injective eO.toRingHom eO.injective).symm
    exact inertiaTrivial_of_equiv_equiv (F p) (F p) J J' f e hcompat P
      (hJ.2.2.2.2 (P.comap eO.toRingHom) hmax hbot)

lemma unramifiedAbelianQ_conjugate_exists
    (p q : ℕ) (hp : 0 < p) (σ : Omega ≃ₐ[ℚ] Omega)
    (J : IntermediateField (F p) Omega) (hJ : UnramifiedAbelianQ p q J) :
    ∃ J' : IntermediateField (F p) Omega,
      UnramifiedAbelianQ p q J' ∧
      J'.restrictScalars ℚ = (J.restrictScalars ℚ).map σ.toAlgHom := by
  have instAbelianF : IsAbelianGalois ℚ (F p) := isAbelianGalois_F p hp
  obtain ⟨J', e, he, himage⟩ := conjugateIntermediateField_exists p hp σ J
  let f : F p ≃ₐ[ℚ] F p := σ.restrictNormal (F p)
  refine ⟨J', unramifiedAbelianQ_of_equiv_equiv p q J J' f.toRingEquiv e ?_ hJ, himage⟩
  intro x
  apply Subtype.ext
  change (e (algebraMap (F p) J x) : Omega) = algebraMap (F p) Omega (f x)
  rw [he]
  exact (σ.restrictNormal_commutes (F p) x).symm

end Catalan.A3
