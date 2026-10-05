module

public import Mathlib

/-!
# `Catalan.Density.ConjugateOver`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Catalan.Kummer
variable (k B L : Type*) [Field k] [Field B] [Field L]
variable [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L] [Normal k B]

def conjugateOver (σ : L ≃ₐ[k] L) (τ : L ≃ₐ[B] L) : L ≃ₐ[B] L where
  toRingEquiv := (σ * τ.restrictScalars k * σ⁻¹).toRingEquiv
  commutes' b := by
    change σ (τ (σ⁻¹ (algebraMap B L b))) = algebraMap B L b
    rw [← (σ⁻¹).restrictNormal_commutes B b, τ.commutes,
      (σ⁻¹).restrictNormal_commutes B b]
    exact σ.apply_symm_apply _

lemma conjugateOver_apply (σ : L ≃ₐ[k] L) (τ : L ≃ₐ[B] L) (x : L) :
    conjugateOver k B L σ τ x = σ (τ (σ⁻¹ x)) := rfl

lemma conjugateOver_restrictScalars (σ : L ≃ₐ[k] L) (τ : L ≃ₐ[B] L) :
    (conjugateOver k B L σ τ).restrictScalars k = σ * τ.restrictScalars k * σ⁻¹ := by
  ext x
  rfl

lemma conjugateOver_eq_self_of_commute (σ : L ≃ₐ[k] L) (τ : L ≃ₐ[B] L)
    (h : σ * τ.restrictScalars k = τ.restrictScalars k * σ) :
    conjugateOver k B L σ τ = τ := by
  have heq : (conjugateOver k B L σ τ).restrictScalars k = τ.restrictScalars k := by
    rw [conjugateOver_restrictScalars, h, mul_assoc, mul_inv_cancel, mul_one]
  apply AlgEquiv.ext
  intro x
  exact DFunLike.congr_fun heq x

end Catalan.Kummer
