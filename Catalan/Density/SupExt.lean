import Mathlib

set_option autoImplicit false
noncomputable section
namespace Catalan.FieldTower

lemma sup_algHom_ext
    (F L E : Type*) [Field F] [Field L] [Field E] [Algebra F L] [Algebra F E]
    (H M : IntermediateField F L) (φ ψ : ↥(H ⊔ M) →ₐ[F] E)
    (hH : ∀ x : H, φ (IntermediateField.inclusion (show H ≤ H ⊔ M from le_sup_left) x) =
      ψ (IntermediateField.inclusion (show H ≤ H ⊔ M from le_sup_left) x))
    (hM : ∀ x : M, φ (IntermediateField.inclusion (show M ≤ H ⊔ M from le_sup_right) x) =
      ψ (IntermediateField.inclusion (show M ≤ H ⊔ M from le_sup_right) x)) :
    φ = ψ := by
  have hsup : H ⊔ M = IntermediateField.adjoin F ((H : Set L) ∪ (M : Set L)) := by
    simp only [IntermediateField.adjoin_union, IntermediateField.adjoin_self]
  apply IntermediateField.algHom_ext_of_eq_adjoin F hsup
  intro x hx
  rcases hx with hx | hx
  · exact hH ⟨x, hx⟩
  · exact hM ⟨x, hx⟩

end Catalan.FieldTower
