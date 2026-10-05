module

public import Catalan.Density.FStructure

/-!
# `Catalan.Density.ConjugateField`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma conjugateIntermediateField_exists
    (p : ℕ) (hp : 0 < p) (σ : Omega ≃ₐ[ℚ] Omega)
    (J : IntermediateField (F p) Omega) :
    ∃ (J' : IntermediateField (F p) Omega) (e : J ≃+* J'),
      (∀ x : J, (e x : Omega) = σ (x : Omega)) ∧
      J'.restrictScalars ℚ = (J.restrictScalars ℚ).map σ.toAlgHom := by
  have instAbelianF : IsAbelianGalois ℚ (F p) := isAbelianGalois_F p hp
  let τ : F p ≃ₐ[ℚ] F p := σ.restrictNormal (F p)
  have hcontains (a : F p) :
      algebraMap (F p) Omega a ∈ J.toSubfield.map σ.toRingHom := by
    apply Subfield.mem_map.mpr
    refine ⟨algebraMap (F p) Omega (τ.symm a), J.algebraMap_mem (τ.symm a), ?_⟩
    calc
      σ (algebraMap (F p) Omega (τ.symm a)) =
          algebraMap (F p) Omega (τ (τ.symm a)) :=
        (σ.restrictNormal_commutes (F p) (τ.symm a)).symm
      _ = algebraMap (F p) Omega a := congrArg (algebraMap (F p) Omega) (τ.apply_symm_apply a)
  let J' : IntermediateField (F p) Omega :=
    (J.toSubfield.map σ.toRingHom).toIntermediateField hcontains
  let e : J ≃+* J' :=
    (IntermediateField.intermediateFieldMap σ (J.restrictScalars ℚ)).toRingEquiv
  refine ⟨J', e, ?_, ?_⟩
  · intro x
    rfl
  · ext x
    rfl

end Catalan.A3
