import Catalan.Density.RootCoordinateAction

set_option autoImplicit false
noncomputable section
namespace Catalan.Kummer
variable (L : Type*) [Field L] (n : ℕ) [NeZero n]
variable (ζ : Lˣ) (hζ : IsPrimitiveRoot ζ n)

def rootCoordinateScalar (σ : L ≃+* L) : ZMod n :=
  rootsOfUnityCoordinate L n ζ hζ
    (Additive.ofMul (σ.toMulEquiv.restrictRootsOfUnity n
      (Additive.toMul ((rootsOfUnityCoordinate L n ζ hζ).symm 1))))

lemma rootCoordinateScalar_one :
    rootCoordinateScalar L n ζ hζ (RingEquiv.refl L) = 1 := by
  let e := rootsOfUnityCoordinate L n ζ hζ
  change e (e.symm 1) = 1
  exact e.apply_symm_apply _

lemma rootCoordinateScalar_trans (σ τ : L ≃+* L) :
    rootCoordinateScalar L n ζ hζ (σ.trans τ) =
      rootCoordinateScalar L n ζ hζ σ * rootCoordinateScalar L n ζ hζ τ := by
  let e := rootsOfUnityCoordinate L n ζ hζ
  let u : rootsOfUnity n L := Additive.toMul (e.symm 1)
  have htrans :
      (σ.trans τ).toMulEquiv.restrictRootsOfUnity n u =
        τ.toMulEquiv.restrictRootsOfUnity n
          (σ.toMulEquiv.restrictRootsOfUnity n u) := by
    apply Subtype.ext
    rfl
  have h := rootsOfUnityCoordinate_aut L n ζ hζ τ
    (σ.toMulEquiv.restrictRootsOfUnity n u)
  have h' :
      e (Additive.ofMul
          (τ.toMulEquiv.restrictRootsOfUnity n
            (σ.toMulEquiv.restrictRootsOfUnity n u))) =
        e (Additive.ofMul
            (τ.toMulEquiv.restrictRootsOfUnity n u)) *
          e (Additive.ofMul (σ.toMulEquiv.restrictRootsOfUnity n u)) := by
    simpa [e, u] using h
  change e (Additive.ofMul ((σ.trans τ).toMulEquiv.restrictRootsOfUnity n u)) =
    e (Additive.ofMul (σ.toMulEquiv.restrictRootsOfUnity n u)) *
      e (Additive.ofMul (τ.toMulEquiv.restrictRootsOfUnity n u))
  rw [htrans, h']
  ring

lemma isUnit_rootCoordinateScalar (σ : L ≃+* L) :
    IsUnit (rootCoordinateScalar L n ζ hζ σ) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨rootCoordinateScalar L n ζ hζ σ.symm, ?_⟩
  rw [← rootCoordinateScalar_trans L n ζ hζ σ σ.symm,
    show σ.trans σ.symm = RingEquiv.refl L from RingEquiv.symm_trans_self σ.symm,
    rootCoordinateScalar_one]

end Catalan.Kummer
