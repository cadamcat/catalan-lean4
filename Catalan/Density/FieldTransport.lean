module

public import Catalan.Density.Definitions

/-!
# `Catalan.Density.FieldTransport`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.A3

def galEquivOfFieldEquivs
    (K K' L L' : Type*)
    [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    (f : K ≃+* K') (e : L ≃+* L')
    (hcompat : ∀ x, e (algebraMap K L x) = algebraMap K' L' (f x)) :
    (L ≃ₐ[K] L) ≃* (L' ≃ₐ[K'] L') := by
  have hinvcompat (x : K') :
      e.symm (algebraMap K' L' x) = algebraMap K L (f.symm x) := by
    apply e.injective
    rw [e.apply_symm_apply, hcompat, f.apply_symm_apply]
  let forward (σ : L ≃ₐ[K] L) : L' ≃ₐ[K'] L' :=
    AlgEquiv.ofRingEquiv (f := e.symm.trans (σ.toRingEquiv.trans e)) (by
      intro x
      change e (σ (e.symm (algebraMap K' L' x))) = algebraMap K' L' x
      rw [hinvcompat, σ.commutes, hcompat, f.apply_symm_apply])
  let backward (σ : L' ≃ₐ[K'] L') : L ≃ₐ[K] L :=
    AlgEquiv.ofRingEquiv (f := e.trans (σ.toRingEquiv.trans e.symm)) (by
      intro x
      change e.symm (σ (e (algebraMap K L x))) = algebraMap K L x
      rw [hcompat, σ.commutes, hinvcompat, f.symm_apply_apply])
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · intro σ
    apply AlgEquiv.ext
    intro x
    change e.symm (e (σ (e.symm (e x)))) = σ x
    simp only [e.symm_apply_apply]
  · intro σ
    apply AlgEquiv.ext
    intro x
    change e (e.symm (σ (e (e.symm x)))) = σ x
    simp only [e.apply_symm_apply]
  · intro σ τ
    apply AlgEquiv.ext
    intro x
    change e (σ (τ (e.symm x))) = e (σ (e.symm (e (τ (e.symm x)))))
    rw [e.symm_apply_apply]


lemma galEquivOfFieldEquivs_apply
    (K K' L L' : Type*)
    [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    (f : K ≃+* K') (e : L ≃+* L')
    (hcompat : ∀ x, e (algebraMap K L x) = algebraMap K' L' (f x))
    (σ : L ≃ₐ[K] L) (x : L') :
    galEquivOfFieldEquivs K K' L L' f e hcompat σ x = e (σ (e.symm x)) := by
  rfl


lemma inertiaTrivial_of_equiv_equiv
    (K K' L L' : Type*)
    [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L']
    (f : K ≃+* K') (e : L ≃+* L')
    (hcompat : ∀ x, e (algebraMap K L x) = algebraMap K' L' (f x))
    (P : Ideal (𝓞 L'))
    (hP : InertiaTrivial K L
      (P.comap (NumberField.RingOfIntegers.mapRingEquiv e).toRingHom)) :
    InertiaTrivial K' L' P := by
  intro τ _ hτ
  obtain ⟨σ, rfl⟩ := (galEquivOfFieldEquivs K K' L L' f e hcompat).surjective τ
  have heq (x : 𝓞 L) :
      (RingOfIntegers.mapRingEquiv e) (integralAut σ x) =
        integralAut (galEquivOfFieldEquivs K K' L L' f e hcompat σ)
          ((RingOfIntegers.mapRingEquiv e) x) := by
    apply RingOfIntegers.coe_injective
    change e (σ (x : L)) =
      galEquivOfFieldEquivs K K' L L' f e hcompat σ (e (x : L))
    rw [galEquivOfFieldEquivs_apply, e.symm_apply_apply]
  have hdiff : ∀ x : 𝓞 L, integralAut σ x - x ∈
      P.comap (RingOfIntegers.mapRingEquiv e).toRingHom := by
    intro x
    change (RingOfIntegers.mapRingEquiv e) (integralAut σ x - x) ∈ P
    rw [map_sub, heq]
    exact hτ ((RingOfIntegers.mapRingEquiv e) x)
  have hpres : PreservesPrime σ (P.comap (RingOfIntegers.mapRingEquiv e).toRingHom) := by
    intro x
    constructor
    · intro hx
      simpa only [sub_sub_cancel] using
        (P.comap (RingOfIntegers.mapRingEquiv e).toRingHom).sub_mem hx (hdiff x)
    · intro hx
      simpa only [sub_add_cancel] using
        (P.comap (RingOfIntegers.mapRingEquiv e).toRingHom).add_mem (hdiff x) hx
  rw [hP σ hpres hdiff, map_one]

end Catalan.A3
