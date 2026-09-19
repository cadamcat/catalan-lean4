import Catalan.CaseOne.Places
import Catalan.CaseOne.LogSpaceEquiv

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitLog
variable (K : Type*) [Field K] [NumberField K]

def groupZeroSum : Submodule ℝ ((K ≃ₐ[ℚ] K) → ℝ) where
  carrier := {f | ∑ σ, f σ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change (∑ σ, (f σ + g σ)) = 0
    rw [Finset.sum_add_distrib, hf, hg, add_zero]
  smul_mem' := by
    intro c f hf
    change (∑ σ, c * f σ) = 0
    rw [← Finset.mul_sum, hf, mul_zero]

noncomputable def regularZeroSumAction (τ : K ≃ₐ[ℚ] K) : groupZeroSum K →ₗ[ℝ] groupZeroSum K where
  toFun f := ⟨fun σ => f.val (σ * τ), by
    change (∑ σ, f.val (Equiv.mulRight τ σ)) = 0
    rw [Equiv.sum_comp]
    exact f.property⟩
  map_add' f g := rfl
  map_smul' c f := rfl

lemma regularZeroSumAction_apply (τ : K ≃ₐ[ℚ] K) (f : groupZeroSum K) (σ : K ≃ₐ[ℚ] K) :
    (regularZeroSumAction K τ f).val σ = f.val (σ * τ) := rfl

variable [IsTotallyReal K] [IsGalois ℚ K]

noncomputable def zeroSumRegularEquiv (w : InfinitePlace K) : zeroSum K ≃ₗ[ℝ] groupZeroSum K where
  toFun f := ⟨fun σ => f.val (galPlaceEquiv K w σ), by
    change (∑ σ, f.val (galPlaceEquiv K w σ)) = 0
    rw [Equiv.sum_comp]
    exact f.property⟩
  invFun f := ⟨fun v => f.val ((galPlaceEquiv K w).symm v), by
    change (∑ v, f.val ((galPlaceEquiv K w).symm v)) = 0
    rw [Equiv.sum_comp]
    exact f.property⟩
  left_inv f := by
    apply Subtype.ext
    funext v
    exact congrArg f.val ((galPlaceEquiv K w).apply_symm_apply v)
  right_inv f := by
    apply Subtype.ext
    funext σ
    exact congrArg f.val ((galPlaceEquiv K w).symm_apply_apply σ)
  map_add' f g := rfl
  map_smul' c f := rfl

lemma zeroSumRegularEquiv_apply (w : InfinitePlace K) (f : zeroSum K) (σ : K ≃ₐ[ℚ] K) :
    (zeroSumRegularEquiv K w f).val σ = f.val (galPlaceEquiv K w σ) := rfl

lemma zeroSumRegularEquiv_intertwining (w : InfinitePlace K) (p : ℕ) (τ : G p K)
    (f : zeroSum K) :
    zeroSumRegularEquiv K w (zeroSumAction K p τ f) =
      regularZeroSumAction K τ (zeroSumRegularEquiv K w f) := by
  apply Subtype.ext
  funext σ
  change f.val ((galPlaceEquiv K w σ).comap τ.toRingEquiv.toRingHom) =
    f.val (galPlaceEquiv K w (σ * τ))
  rw [galPlaceEquiv_mul]

end Catalan.UnitLog
