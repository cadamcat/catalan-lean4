import Catalan.CaseOne.FullLog

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitLog
variable (K : Type*) [Field K] [NumberField K]

local instance infinitePlaceDecidableEq : DecidableEq (InfinitePlace K) := Classical.decEq _

/-- Recover the deleted logarithmic coordinate by the norm relation. -/
def logSpaceLift : Units.dirichletUnitTheorem.logSpace K →ₗ[ℝ] (InfinitePlace K → ℝ) where
  toFun f w := if hw : w = Units.dirichletUnitTheorem.w₀ then -∑ v, f v else f ⟨w, hw⟩
  map_add' := by
    intro f g
    funext w
    by_cases hw : w = Units.dirichletUnitTheorem.w₀
    · simp [hw, Finset.sum_add_distrib, add_comm]
    · simp [hw]
  map_smul' := by
    intro c f
    funext w
    by_cases hw : w = Units.dirichletUnitTheorem.w₀
    · simp [hw, smul_eq_mul, Finset.mul_sum]
    · simp [hw]

lemma logSpaceLift_mem (f : Units.dirichletUnitTheorem.logSpace K) :
    logSpaceLift K f ∈ zeroSum K := by
  classical
  change ∑ w, logSpaceLift K f w = 0
  rw [Fintype.sum_eq_add_sum_subtype_ne _ Units.dirichletUnitTheorem.w₀]
  have hrest : (∑ w : {w : InfinitePlace K // w ≠ Units.dirichletUnitTheorem.w₀},
      logSpaceLift K f w.val) = ∑ w, f w := by
    apply Finset.sum_congr rfl
    intro w _
    simp [logSpaceLift, w.property]
  rw [hrest]
  simp [logSpaceLift]

/-- The actual deleted-place logarithm space is the full norm-zero hyperplane. -/
def logSpaceEquiv : Units.dirichletUnitTheorem.logSpace K ≃ₗ[ℝ] zeroSum K where
  toFun f := ⟨logSpaceLift K f, logSpaceLift_mem K f⟩
  invFun f w := f.val w.val
  left_inv f := by
    funext w
    simp [logSpaceLift, w.property]
  right_inv f := by
    apply Subtype.ext
    funext w
    change (if hw : w = Units.dirichletUnitTheorem.w₀ then
      -∑ v : {v : InfinitePlace K // v ≠ Units.dirichletUnitTheorem.w₀}, f.val v.val
      else f.val w) = f.val w
    split_ifs with hw
    · subst w
      have hf : ∑ v, f.val v = 0 := f.property
      rw [Fintype.sum_eq_add_sum_subtype_ne _ Units.dirichletUnitTheorem.w₀] at hf
      linarith
    · rfl
  map_add' f g := Subtype.ext ((logSpaceLift K).map_add f g)
  map_smul' c f := Subtype.ext ((logSpaceLift K).map_smul c f)

lemma logSpaceEquiv_logEmbedding (u : (𝓞 K)ˣ) :
    (logSpaceEquiv K (Units.logEmbedding K (Additive.ofMul u)) : InfinitePlace K → ℝ) =
      fullLog K u := by
  funext w
  change (if hw : w = Units.dirichletUnitTheorem.w₀ then
    -∑ v, Units.logEmbedding K (Additive.ofMul u) v else
      Units.logEmbedding K (Additive.ofMul u) ⟨w, hw⟩) = fullLog K u w
  split_ifs with hw
  · subst w
    rw [Units.dirichletUnitTheorem.sum_logEmbedding_component]
    simp only [fullLog, neg_mul, neg_neg]
  · rfl

/-- Pullback of infinite places along the actual field automorphism. -/
def placeEquiv (p : ℕ) (τ : G p K) : InfinitePlace K ≃ InfinitePlace K where
  toFun w := w.comap τ.toRingEquiv.toRingHom
  invFun w := w.comap τ.symm.toRingEquiv.toRingHom
  left_inv w := by
    ext x
    change w (τ (τ.symm x)) = w x
    rw [τ.apply_symm_apply]
  right_inv w := by
    ext x
    change w (τ.symm (τ x)) = w x
    rw [τ.symm_apply_apply]

def zeroSumAction (p : ℕ) (τ : G p K) : zeroSum K →ₗ[ℝ] zeroSum K where
  toFun f := ⟨fun w => f.val (w.comap τ.toRingEquiv.toRingHom), by
    change ∑ w, f.val (placeEquiv K p τ w) = 0
    rw [Equiv.sum_comp]
    exact f.property⟩
  map_add' f g := rfl
  map_smul' c f := rfl

def logRealAction (p : ℕ) (τ : G p K) :
    Units.dirichletUnitTheorem.logSpace K →ₗ[ℝ] Units.dirichletUnitTheorem.logSpace K :=
  (logSpaceEquiv K).symm.toLinearMap.comp
    ((zeroSumAction K p τ).comp (logSpaceEquiv K).toLinearMap)

lemma logRealAction_logEmbedding (p : ℕ) (τ : G p K) (u : (𝓞 K)ˣ) :
    logRealAction K p τ (Units.logEmbedding K (Additive.ofMul u)) =
      Units.logEmbedding K (Additive.ofMul (Circular.unitAction p K τ u)) := by
  apply (logSpaceEquiv K).injective
  change logSpaceEquiv K ((logSpaceEquiv K).symm
    (zeroSumAction K p τ (logSpaceEquiv K (Units.logEmbedding K (Additive.ofMul u))))) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  funext w
  change (logSpaceEquiv K (Units.logEmbedding K (Additive.ofMul u))).val
      (w.comap τ.toRingEquiv.toRingHom) =
    (logSpaceEquiv K (Units.logEmbedding K (Additive.ofMul (Circular.unitAction p K τ u)))).val w
  rw [logSpaceEquiv_logEmbedding, logSpaceEquiv_logEmbedding]
  exact (fullLog_unitAction K p τ u w).symm

end Catalan.UnitLog
