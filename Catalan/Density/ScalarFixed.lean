module

public import Catalan.Density.RootCharacter

/-!
# `Catalan.Density.ScalarFixed`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Kummer
variable (L : Type*) [Field L] (n : ℕ) [NeZero n]
variable (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ n)

lemma rootCoordinateScalar_eq_one_iff (σ : L ≃+* L) :
    rootCoordinateScalar L n ζ hζ σ = 1 ↔ σ (ζ : L) = (ζ : L) := by
  let e := rootsOfUnityCoordinate L n ζ hζ
  let u : rootsOfUnity n L := Additive.toMul (e.symm 1)
  have hu : (u : Lˣ) = ζ := by
    simpa only [Nat.cast_one, pow_one] using
      rootsOfUnityCoordinate_symm_nat L n ζ hζ 1
  change e (Additive.ofMul (σ.toMulEquiv.restrictRootsOfUnity n u)) = 1 ↔ _
  rw [← e.apply_symm_apply 1, e.injective.eq_iff]
  change σ.toMulEquiv.restrictRootsOfUnity n u = u ↔ _
  rw [Subtype.ext_iff, Units.ext_iff]
  change σ ((u : Lˣ) : L) = ((u : Lˣ) : L) ↔ _
  rw [hu]

end Catalan.Kummer
