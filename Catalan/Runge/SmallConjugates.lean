import Catalan.Runge.Definitions

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Runge

lemma small_conjugates_zero (K : Type*) [Field K] [NumberField K] (a : 𝓞 K)
    (ha : ∀ τ : K →+* ℂ, ‖τ (a : K)‖ < 1) : a = 0 := by
  by_contra hne
  obtain ⟨τ, hτ⟩ := NumberField.exists_conjugate_one_le_norm hne
  exact (not_le_of_gt (ha τ)) hτ

end Catalan.Runge
