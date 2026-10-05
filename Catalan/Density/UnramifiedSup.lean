module

public import Catalan.Density.BaseFields
public import Catalan.Density.InertiaRestrictions
public import Catalan.Density.SupExt

/-!
# `Catalan.Density.UnramifiedSup`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma unramifiedAbelianQ_sup (p q : ℕ)
    (A B : IntermediateField (F p) Omega)
    (hA : UnramifiedAbelianQ p q A) (hB : UnramifiedAbelianQ p q B) :
    UnramifiedAbelianQ p q (A ⊔ B) := by
  let instFiniteA : FiniteDimensional (F p) A := hA.1
  let instFiniteB : FiniteDimensional (F p) B := hB.1
  let instNumberFieldA : NumberField A := NumberField.of_module_finite (F p) A
  let instNumberFieldB : NumberField B := NumberField.of_module_finite (F p) B
  let instNumberFieldSup : NumberField (A ⊔ B : IntermediateField (F p) Omega) :=
    NumberField.of_module_finite (F p) (A ⊔ B : IntermediateField (F p) Omega)
  let instGaloisA : IsGalois (F p) A := hA.2.1
  let instGaloisB : IsGalois (F p) B := hB.2.1
  let instGaloisSup : IsGalois (F p) (A ⊔ B : IntermediateField (F p) Omega) := {}
  let instAlgebraA : Algebra A (A ⊔ B : IntermediateField (F p) Omega) :=
    (IntermediateField.inclusion (show A ≤ A ⊔ B from le_sup_left)).toRingHom.toAlgebra
  let instAlgebraB : Algebra B (A ⊔ B : IntermediateField (F p) Omega) :=
    (IntermediateField.inclusion (show B ≤ A ⊔ B from le_sup_right)).toRingHom.toAlgebra
  let instTowerA : IsScalarTower (F p) A (A ⊔ B : IntermediateField (F p) Omega) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let instTowerB : IsScalarTower (F p) B (A ⊔ B : IntermediateField (F p) Omega) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hgen : ∀ σ : (A ⊔ B : IntermediateField (F p) Omega) ≃ₐ[F p] (A ⊔ B : IntermediateField (F p) Omega),
      σ.restrictNormal A = 1 → σ.restrictNormal B = 1 → σ = 1 := by
    intro σ hσA hσB
    have hhom := Catalan.FieldTower.sup_algHom_ext (F p) Omega
      (A ⊔ B : IntermediateField (F p) Omega) A B σ.toAlgHom
      (1 : (A ⊔ B : IntermediateField (F p) Omega) ≃ₐ[F p] (A ⊔ B : IntermediateField (F p) Omega)).toAlgHom
      (fun x => ?_) (fun x => ?_)
    · exact AlgEquiv.ext fun x => congrArg (fun f => f x) hhom
    · change σ (algebraMap A (A ⊔ B : IntermediateField (F p) Omega) x) = algebraMap A (A ⊔ B : IntermediateField (F p) Omega) x
      simpa only [hσA, AlgEquiv.one_apply] using
        (σ.restrictNormal_commutes A x).symm
    · change σ (algebraMap B (A ⊔ B : IntermediateField (F p) Omega) x) = algebraMap B (A ⊔ B : IntermediateField (F p) Omega) x
      simpa only [hσB, AlgEquiv.one_apply] using
        (σ.restrictNormal_commutes B x).symm
  refine ⟨inferInstance, instGaloisSup, ?_, ?_, ?_⟩
  · intro σ τ
    apply mul_inv_eq_one.mp
    apply hgen
    · change (AlgEquiv.restrictNormalHom A) ((σ * τ) * (τ * σ)⁻¹) = 1
      rw [map_mul, map_inv, map_mul, map_mul]
      exact mul_inv_eq_one.mpr (hA.2.2.1 _ _)
    · change (AlgEquiv.restrictNormalHom B) ((σ * τ) * (τ * σ)⁻¹) = 1
      rw [map_mul, map_inv, map_mul, map_mul]
      exact mul_inv_eq_one.mpr (hB.2.2.1 _ _)
  · intro σ
    apply hgen
    · change (AlgEquiv.restrictNormalHom A) (σ ^ q) = 1
      rw [map_pow]
      exact hA.2.2.2.1 _
    · change (AlgEquiv.restrictNormalHom B) (σ ^ q) = 1
      rw [map_pow]
      exact hB.2.2.2.1 _
  · intro P hP hPbot
    let instMaximalP : P.IsMaximal := hP
    apply inertiaTrivial_of_restrictions (F p) A B (A ⊔ B : IntermediateField (F p) Omega) hgen P
    · exact hA.2.2.2.2 (P.under (𝓞 A)) inferInstance (Ideal.under_ne_bot (𝓞 A) hPbot)
    · exact hB.2.2.2.2 (P.under (𝓞 B)) inferInstance (Ideal.under_ne_bot (𝓞 B) hPbot)

end Catalan.A3
