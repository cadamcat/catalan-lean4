module

public import Catalan.Density.RootCoordinates

/-!
# `Catalan.Density.RootCoordinateAction`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Kummer
variable (L : Type*) [Field L] (n : ℕ) [NeZero n]
variable (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ n)

lemma rootsOfUnityCoordinate_aut (σ : L ≃+* L) (u : rootsOfUnity n L) :
    rootsOfUnityCoordinate L n ζ hζ
      (Additive.ofMul (σ.toMulEquiv.restrictRootsOfUnity n u)) =
      rootsOfUnityCoordinate L n ζ hζ
        (Additive.ofMul (σ.toMulEquiv.restrictRootsOfUnity n
          (Additive.toMul ((rootsOfUnityCoordinate L n ζ hζ).symm 1)))) *
      rootsOfUnityCoordinate L n ζ hζ (Additive.ofMul u) := by
  let e := rootsOfUnityCoordinate L n ζ hζ
  let f : ZMod n →+ ZMod n := e.toAddMonoidHom.comp
    ((σ.toMulEquiv.restrictRootsOfUnity n).toAdditive.toAddMonoidHom.comp
      e.symm.toAddMonoidHom)
  have hf (a : ZMod n) : f a = f 1 * a := by
    have h := (f.toZModLinearMap n).map_smul a (1 : ZMod n)
    simpa only [AddMonoidHom.coe_toZModLinearMap, smul_eq_mul, mul_one, mul_comm]
      using h
  have h := hf (e (Additive.ofMul u))
  simpa [f] using h

end Catalan.Kummer
