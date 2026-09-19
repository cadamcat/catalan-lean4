import Catalan.Density.Definitions

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

lemma relativeFrob_congruence_of_rationalFrob_compatible
    (K E L : Type*) [Field K] [NumberField K] [Field E] [NumberField E]
    [Field L] [NumberField L] [Algebra K E] [Algebra K L] [Algebra E L]
    [IsScalarTower K E L] (ell : ℕ) (P : Ideal (𝓞 L))
    (sigma : L ≃ₐ[ℚ] L) (tau : E ≃ₐ[K] E)
    (hfrob : IsArithmeticFrob ell P sigma)
    (hcompat : ∀ x : E,
      sigma (algebraMap E L x) = algebraMap E L (tau x))
    (hcard : Nat.card (𝓞 K ⧸ (P.under (𝓞 E)).under (𝓞 K)) = ell) :
    ∀ x : 𝓞 E, integralAut tau x -
      x ^ Nat.card (𝓞 K ⧸ (P.under (𝓞 E)).under (𝓞 K)) ∈ P.under (𝓞 E) := by
  intro x
  rw [Ideal.mem_under, map_sub]
  have hcompat_int :
      algebraMap (𝓞 E) (𝓞 L) (integralAut tau x) =
        integralAut sigma (algebraMap (𝓞 E) (𝓞 L) x) := by
    apply RingOfIntegers.coe_injective
    change algebraMap E L (tau (x : E)) = sigma (algebraMap E L (x : E))
    exact (hcompat (x : E)).symm
  rw [hcompat_int, map_pow, hcard]
  exact hfrob.2.2.2.2.2.2 (algebraMap (𝓞 E) (𝓞 L) x)

end Catalan.A3
