import Mathlib

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitLog
variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] [IsGalois ℚ K]

lemma gal_place_bijective (w : InfinitePlace K) :
    Function.Bijective (fun σ : K ≃ₐ[ℚ] K => w.comap σ.toRingEquiv.toRingHom) := by
  let instFreeInfinitePlaces : IsCancelSMul (K ≃ₐ[ℚ] K) (InfinitePlace K) :=
    isCancelSMul_iff_stabilizer_eq_bot.mpr fun v =>
      ((IsTotallyReal.isReal v).isUnramified ℚ).stabilizer_eq_bot
  constructor
  · intro σ τ h
    have haction : σ⁻¹ • w = τ⁻¹ • w := h
    exact inv_injective (IsCancelSMul.right_cancel σ⁻¹ τ⁻¹ w haction)
  · intro v
    have hbase : w.comap (algebraMap ℚ K) = v.comap (algebraMap ℚ K) :=
      Subsingleton.elim _ _
    obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq hbase
    exact ⟨σ⁻¹, hσ⟩

noncomputable def galPlaceEquiv (w : InfinitePlace K) : (K ≃ₐ[ℚ] K) ≃ InfinitePlace K :=
  Equiv.ofBijective (fun σ => w.comap σ.toRingEquiv.toRingHom) (gal_place_bijective K w)

lemma galPlaceEquiv_mul (w : InfinitePlace K) (σ τ : K ≃ₐ[ℚ] K) :
    galPlaceEquiv K w (σ * τ) =
      (galPlaceEquiv K w σ).comap τ.toRingEquiv.toRingHom := by
  rfl

end Catalan.UnitLog
