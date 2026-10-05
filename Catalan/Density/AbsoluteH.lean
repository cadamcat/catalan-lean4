module

public import Catalan.Density.ConjugateWitness

/-!
# `Catalan.Density.AbsoluteH`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.A3

lemma isGalois_Hsub_rat (p q : ℕ) (hp : 0 < p) :
    IsGalois ℚ (Hsub p q) := by
  have instAlgebraicOmega : Algebra.IsAlgebraic ℚ Omega := AlgebraicClosure.isAlgebraic ℚ
  have instAlgClosureOmega : IsAlgClosure ℚ Omega := ⟨inferInstance, inferInstance⟩
  have instAbelianF : IsAbelianGalois ℚ (F p) := isAbelianGalois_F p hp
  have instNormalH : Normal ℚ (Hsub p q) := by
    change Normal ℚ ((Hsub p q).restrictScalars ℚ)
    apply IntermediateField.normal_iff_forall_map_le'.mpr
    intro σ
    let D : IntermediateField (F p) Omega :=
      ((Hsub p q).toSubfield.comap σ.toRingHom).toIntermediateField (fun x => by
        change σ (algebraMap (F p) Omega x) ∈ Hsub p q
        rw [← σ.restrictNormal_commutes (F p) x]
        exact (Hsub p q).algebraMap_mem _)
    have hle : Hsub p q ≤ D := by
      apply sSup_le
      intro J hJ
      obtain ⟨J', hJ', heq⟩ := unramifiedAbelianQ_conjugate_exists p q hp σ J hJ
      intro x hx
      change σ x ∈ Hsub p q
      apply (show J' ≤ Hsub p q from le_sSup hJ')
      change σ x ∈ J'.restrictScalars ℚ
      rw [heq]
      exact ⟨x, hx, rfl⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hle hx
  exact {}

end Catalan.A3
