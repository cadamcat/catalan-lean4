module

public import Catalan.CaseOne.CircularUnits

/-!
# `Catalan.CaseOne.FullLog`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
open NumberField
noncomputable section
namespace Catalan.UnitLog
variable (K : Type*) [Field K] [NumberField K]

def fullLog (u : (𝓞 K)ˣ) : InfinitePlace K → ℝ :=
  fun w => (w.mult : ℝ) * Real.log (w ((u : 𝓞 K) : K))

def zeroSum : Submodule ℝ (InfinitePlace K → ℝ) where
  carrier := {f | ∑ w, f w = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change (∑ w, (f w + g w)) = 0
    rw [Finset.sum_add_distrib, hf, hg, add_zero]
  smul_mem' := by
    intro c f hf
    change (∑ w, c * f w) = 0
    rw [← Finset.mul_sum, hf, mul_zero]


lemma fullLog_one : fullLog K 1 = 0 := by
  funext w
  simp [fullLog]

lemma fullLog_mul (u v : (𝓞 K)ˣ) : fullLog K (u * v) = fullLog K u + fullLog K v := by
  funext w
  simp only [fullLog, Pi.add_apply, Units.val_mul, map_mul]
  rw [Real.log_mul (Units.pos_at_place u w).ne' (Units.pos_at_place v w).ne']
  ring

lemma fullLog_sum (u : (𝓞 K)ˣ) : ∑ w, fullLog K u w = 0 :=
  Units.sum_mult_mul_log u

lemma fullLog_eq_zero_iff (u : (𝓞 K)ˣ) :
    fullLog K u = 0 ↔ u ∈ NumberField.Units.torsion K := by
  rw [Units.mem_torsion]
  constructor
  · intro hu w
    exact Units.dirichletUnitTheorem.mult_log_place_eq_zero.mp (congrFun hu w)
  · intro hu
    funext w
    simp only [fullLog, hu w, Real.log_one, mul_zero, Pi.zero_apply]

lemma fullLog_span : Submodule.span ℝ (Set.range (fullLog K)) = zeroSum K := by
  classical
  let w0 : InfinitePlace K := Units.dirichletUnitTheorem.w₀
  let lift : Units.dirichletUnitTheorem.logSpace K →ₗ[ℝ] (InfinitePlace K → ℝ) :=
    { toFun := fun f w => if hw : w = w0 then -∑ v, f v else f ⟨w, hw⟩
      map_add' := by
        intro f g
        funext w
        by_cases hw : w = w0
        · simp [hw, Finset.sum_add_distrib, add_comm]
        · simp [hw]
      map_smul' := by
        intro c f
        funext w
        by_cases hw : w = w0
        · simp [hw, smul_eq_mul, Finset.mul_sum]
        · simp [hw] }
  have hlift (u : (𝓞 K)ˣ) :
      lift (Units.logEmbedding K (Additive.ofMul u)) = fullLog K u := by
    funext w
    change (if hw : w = w0 then -∑ v, Units.logEmbedding K (Additive.ofMul u) v
      else Units.logEmbedding K (Additive.ofMul u) ⟨w, hw⟩) = fullLog K u w
    split_ifs with hw
    · subst w
      rw [Units.dirichletUnitTheorem.sum_logEmbedding_component]
      simp only [fullLog, neg_mul, neg_neg, w0]
    · rfl
  have hspan : ∀ f, lift f ∈ Submodule.span ℝ (Set.range (fullLog K)) := by
    have hle : Submodule.span ℝ (Units.unitLattice K : Set (Units.dirichletUnitTheorem.logSpace K)) ≤
        (Submodule.span ℝ (Set.range (fullLog K))).comap lift := by
      apply Submodule.span_le.mpr
      intro f hf
      obtain ⟨u, hu, rfl⟩ := hf
      change lift (Units.logEmbedding K u) ∈ Submodule.span ℝ (Set.range (fullLog K))
      rw [show u = Additive.ofMul u.toMul from rfl, hlift]
      exact Submodule.subset_span ⟨u.toMul, rfl⟩
    rw [Units.dirichletUnitTheorem.unitLattice_span_eq_top] at hle
    intro f
    exact hle (Submodule.mem_top : f ∈ (⊤ : Submodule ℝ _))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨u, rfl⟩
    exact fullLog_sum K u
  · intro f hf
    let g : Units.dirichletUnitTheorem.logSpace K := fun w => f w.val
    have hfg : lift g = f := by
      funext w
      change (if hw : w = w0 then -∑ v : {w : InfinitePlace K // w ≠ w0}, f v.val else f w) = f w
      split_ifs with hw
      · subst w
        have hsum : ∑ w, f w = 0 := hf
        rw [Fintype.sum_eq_add_sum_subtype_ne _ w0] at hsum
        linarith
      · rfl
    rw [← hfg]
    exact hspan g

lemma fullLog_unitAction (p : ℕ) (τ : G p K) (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    fullLog K (Circular.unitAction p K τ u) w =
      fullLog K u (w.comap τ.toRingEquiv.toRingHom) := by
  classical
  have hmult : (w.comap τ.toRingEquiv.toRingHom).mult = w.mult := by
    unfold InfinitePlace.mult
    exact if_congr (InfinitePlace.isReal_comap_iff τ.toRingEquiv) rfl rfl
  dsimp only [fullLog]
  rw [hmult]
  rfl

end Catalan.UnitLog
