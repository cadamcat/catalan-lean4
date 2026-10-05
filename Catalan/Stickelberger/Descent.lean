module

public import Mathlib

/-!
# `Catalan.Stickelberger.Descent`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
namespace Catalan.Stickelberger
open NumberField

/-- Galois 下降：被 `Gal(L/K)` 全体固定的元素来自 `K`。 -/
theorem exists_algebraMap_eq_of_forall_fixed
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (x : L) (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    ∃ y : K, algebraMap K L y = x := by
  have hx' : x ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact hx σ
  rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at hx'
  exact hx'

/-- 整性下降：若 `y : K` 在 `L` 中的像是代数整数，则 `y` 本身是代数整数。 -/
theorem isIntegral_of_algebraMap_isIntegral
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (y : K) (hx : IsIntegral ℤ (algebraMap K L y)) :
    IsIntegral ℤ y := by
  exact IsIntegral.tower_bot (algebraMap K L).injective hx

/-- 合起来：`𝓞 L` 中被 `Gal(L/K)` 全体固定的元素来自 `𝓞 K`。 -/
theorem exists_ringOfIntegers_of_forall_fixed
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsScalarTower ℚ K L] [IsGalois K L]
    (x : 𝓞 L) (hx : ∀ σ : L ≃ₐ[K] L, σ (x : L) = (x : L)) :
    ∃ y : 𝓞 K, algebraMap (𝓞 K) (𝓞 L) y = x := by
  have hfd : FiniteDimensional K L := inferInstance
  obtain ⟨y, hy⟩ := exists_algebraMap_eq_of_forall_fixed K L (x : L) hx
  have hy_int : IsIntegral ℤ (algebraMap K L y) := by
    rw [hy]
    exact RingOfIntegers.isIntegral_coe x
  have hy' : IsIntegral ℤ y := isIntegral_of_algebraMap_isIntegral K L y hy_int
  refine ⟨⟨y, hy'⟩, ?_⟩
  apply RingOfIntegers.ext
  change algebraMap K L y = (x : L)
  exact hy

end Catalan.Stickelberger
