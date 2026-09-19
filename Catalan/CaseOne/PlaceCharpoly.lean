import Catalan.CaseOne.PlaceCycle
import Catalan.CaseOne.CyclicZeroSum
import Catalan.CaseOne.UnitCharpoly

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitLog
variable (K : Type*) [Field K] [NumberField K]

/-- Pullback along an actual cycle indexing of the infinite places. -/
def cycleZeroSumEquiv (e : ZMod (Fintype.card (InfinitePlace K)) ≃ InfinitePlace K) :
    zeroSum K ≃ₗ[ℝ] cyclicZeroSum (Fintype.card (InfinitePlace K)) where
  toFun f := ⟨fun i => f.val (e i), by
    change (∑ i, f.val (e i)) = 0
    rw [Equiv.sum_comp]
    exact f.property⟩
  invFun f := ⟨fun w => f.val (e.symm w), by
    change (∑ w, f.val (e.symm w)) = 0
    rw [Equiv.sum_comp]
    exact f.property⟩
  left_inv f := by
    apply Subtype.ext
    funext w
    exact congrArg f.val (e.apply_symm_apply w)
  right_inv f := by
    apply Subtype.ext
    funext i
    exact congrArg f.val (e.symm_apply_apply i)
  map_add' f g := rfl
  map_smul' c f := rfl

lemma cycleZeroSumEquiv_intertwining (p : ℕ) (τ : G p K)
    (e : ZMod (Fintype.card (InfinitePlace K)) ≃ InfinitePlace K)
    (he : ∀ i, e (i + 1) = (e i).comap τ.toRingEquiv.toRingHom) (f : zeroSum K) :
    cycleZeroSumEquiv K e (zeroSumAction K p τ f) =
      cyclicZeroSumShift (Fintype.card (InfinitePlace K)) (cycleZeroSumEquiv K e f) := by
  apply Subtype.ext
  funext i
  rw [cyclicZeroSumShift_apply]
  change f.val ((e i).comap τ.toRingEquiv.toRingHom) = f.val (e (i + 1))
  rw [he]

lemma logRealAction_charpoly_of_generator [IsGalois ℚ K] (p : ℕ) (τ : G p K)
    (hτ : ∀ σ : G p K, σ ∈ Subgroup.zpowers τ) :
    (logRealAction K p τ).charpoly =
      ∑ i ∈ Finset.range (Fintype.card (InfinitePlace K)), (Polynomial.X : Polynomial ℝ) ^ i := by
  classical
  obtain ⟨e, _, he⟩ := exists_place_cycle_equiv K τ hτ Units.dirichletUnitTheorem.w₀
  let f := (logSpaceEquiv K).trans (cycleZeroSumEquiv K e)
  have hconj : f.conj (logRealAction K p τ) =
      cyclicZeroSumShift (Fintype.card (InfinitePlace K)) := by
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := f.surjective v
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    change cycleZeroSumEquiv K e
        (logSpaceEquiv K ((logSpaceEquiv K).symm (zeroSumAction K p τ (logSpaceEquiv K x)))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact cycleZeroSumEquiv_intertwining K p τ e he (logSpaceEquiv K x)
  rw [← LinearEquiv.charpoly_conj f, hconj, cyclicZeroSumShift_charpoly]

end Catalan.UnitLog
namespace Catalan.UnitModule
variable (p : ℕ) (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

lemma integralUnit_charpoly_of_generator (τ : G p K)
    (hτ : ∀ σ : G p K, σ ∈ Subgroup.zpowers τ) :
    (integralUnitRepresentation p K τ).charpoly =
      ∑ i ∈ Finset.range (Fintype.card (InfinitePlace K)), (Polynomial.X : Polynomial ℤ) ^ i := by
  classical
  apply Polynomial.map_injective (Int.castRingHom ℝ) (Int.cast_injective (α := ℝ))
  rw [← integralUnit_charpoly_real, UnitLog.logRealAction_charpoly_of_generator K p τ hτ]
  simp only [Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X]

end Catalan.UnitModule
