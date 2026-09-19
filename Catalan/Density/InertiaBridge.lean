import Catalan.Density.Definitions

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma inertiaTrivial_iff_isUnramifiedAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (P : Ideal (𝓞 L)) [P.IsMaximal] (hP : P ≠ ⊥) :
    InertiaTrivial K L P ↔ Algebra.IsUnramifiedAt (𝓞 K) P := by
  have hInertia : InertiaTrivial K L P ↔ P.inertia (L ≃ₐ[K] L) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    constructor
    · intro h σ hσ
      change ∀ x : 𝓞 L, integralAut σ x - x ∈ P at hσ
      apply h σ _ hσ
      intro x
      constructor
      · intro hx
        simpa only [sub_sub_cancel] using P.sub_mem hx (hσ x)
      · intro hx
        simpa only [sub_add_cancel] using P.add_mem (hσ x) hx
    · intro h σ _ hσ
      apply h σ
      change ∀ x : 𝓞 L, integralAut σ x - x ∈ P
      exact hσ
  rw [hInertia, Subgroup.eq_bot_iff_card,
    Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.under (𝓞 K)) P,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P (L ≃ₐ[K] L),
    Ideal.ramificationIdx_eq_one_iff]

end Catalan.A3
