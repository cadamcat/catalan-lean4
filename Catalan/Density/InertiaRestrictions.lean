module

public import Catalan.Density.Definitions

/-!
# `Catalan.Density.InertiaRestrictions`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3
variable (K A B L : Type*) [Field K] [NumberField K]
variable [Field A] [NumberField A] [Field B] [NumberField B] [Field L] [NumberField L]
variable [Algebra K A] [Algebra K B] [Algebra K L] [Algebra A L] [Algebra B L]
variable [IsScalarTower K A L] [IsScalarTower K B L] [Normal K A] [Normal K B]

lemma inertiaTrivial_of_restrictions
    (hgen : ∀ σ : L ≃ₐ[K] L, σ.restrictNormal A = 1 → σ.restrictNormal B = 1 → σ = 1)
    (P : Ideal (𝓞 L))
    (hA : InertiaTrivial K A (P.under (𝓞 A)))
    (hB : InertiaTrivial K B (P.under (𝓞 B))) :
    InertiaTrivial K L P := by
  intro σ _ hσ
  have hdiffA (x : 𝓞 A) : integralAut (σ.restrictNormal A) x - x ∈ P.under (𝓞 A) := by
    rw [Ideal.mem_under, map_sub]
    have hcompat : algebraMap (𝓞 A) (𝓞 L) (integralAut (σ.restrictNormal A) x) =
        integralAut σ (algebraMap (𝓞 A) (𝓞 L) x) := by
      apply RingOfIntegers.coe_injective
      change algebraMap A L (σ.restrictNormal A (x : A)) = σ (algebraMap A L (x : A))
      exact σ.restrictNormal_commutes A (x : A)
    rw [hcompat]
    exact hσ (algebraMap (𝓞 A) (𝓞 L) x)
  have hdiffB (x : 𝓞 B) : integralAut (σ.restrictNormal B) x - x ∈ P.under (𝓞 B) := by
    rw [Ideal.mem_under, map_sub]
    have hcompat : algebraMap (𝓞 B) (𝓞 L) (integralAut (σ.restrictNormal B) x) =
        integralAut σ (algebraMap (𝓞 B) (𝓞 L) x) := by
      apply RingOfIntegers.coe_injective
      change algebraMap B L (σ.restrictNormal B (x : B)) = σ (algebraMap B L (x : B))
      exact σ.restrictNormal_commutes B (x : B)
    rw [hcompat]
    exact hσ (algebraMap (𝓞 B) (𝓞 L) x)
  apply hgen σ
  · apply hA (σ.restrictNormal A) _ hdiffA
    intro x
    constructor
    · intro hx
      simpa only [sub_sub_cancel] using (P.under (𝓞 A)).sub_mem hx (hdiffA x)
    · intro hx
      simpa only [sub_add_cancel] using (P.under (𝓞 A)).add_mem (hdiffA x) hx
  · apply hB (σ.restrictNormal B) _ hdiffB
    intro x
    constructor
    · intro hx
      simpa only [sub_sub_cancel] using (P.under (𝓞 B)).sub_mem hx (hdiffB x)
    · intro hx
      simpa only [sub_add_cancel] using (P.under (𝓞 B)).add_mem (hdiffB x) hx

end Catalan.A3
