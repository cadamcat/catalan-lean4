module

public import Mathlib

/-!
# `Catalan.Density.RootCoordinates`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Kummer
variable (L : Type*) [Field L] (n : ℕ) [NeZero n]
variable (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ n)

def rootsToPowers : rootsOfUnity n L ≃* Subgroup.zpowers ζ where
  toFun u := ⟨u.val, by rw [hζ.zpowers_eq]; exact u.property⟩
  invFun u := ⟨u.val, by rw [← hζ.zpowers_eq]; exact u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def rootsOfUnityCoordinate : Additive (rootsOfUnity n L) ≃+ ZMod n :=
  (rootsToPowers L n ζ hζ).toAdditive.trans hζ.zmodEquivZPowers.symm

lemma rootsOfUnityCoordinate_symm_nat (i : ℕ) :
    ((Additive.toMul ((rootsOfUnityCoordinate L n ζ hζ).symm (i : ZMod n)) :
      rootsOfUnity n L) : Lˣ) = ζ ^ i := by
  change ((Additive.toMul (hζ.zmodEquivZPowers (i : ZMod n)) : Subgroup.zpowers ζ) : Lˣ) = ζ ^ i
  rw [hζ.zmodEquivZPowers_apply_coe_nat]
  rfl

end Catalan.Kummer

