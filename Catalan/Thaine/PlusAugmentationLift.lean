module

public import Catalan.Runge.PlusIdeal
public import Catalan.CaseOne.UnitFiltration

/-!
# `Catalan.Thaine.PlusAugmentationLift`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance plusCircularLiftGalComm
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] : CommGroup (G p K) := UnitModule.cyclotomicGalCommGroup p K

lemma exists_plus_topAnn_lift
    (p q : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K]
    (Theta : R p K)
    (hTheta : Runge.reduceFull p K q Theta ∈
      UnitModule.plusAugIdeal p K q * UnitModule.topUnitAnn p K q) :
    ∃ E : R p K,
      Runge.reduceFull p K q E ∈ UnitModule.topUnitAnn p K q ∧
      (q : ℤ) ∣ weight p K E ∧
      Runge.reduceFull p K q ((1 + MonoidAlgebra.single (ι p K) 1) * E) =
        Runge.reduceFull p K q Theta := by
  classical
  let N := UnitReduction.groupNorm (ZMod q) (G p K)
  let J : Ideal (MonoidAlgebra (ZMod q) (G p K)) := (Ideal.span ({N} : Set _)).annihilator
  change Runge.reduceFull p K q Theta ∈
    (Ideal.span ({1 + MonoidAlgebra.single (ι p K) 1} : Set _) * J) *
      UnitModule.topUnitAnn p K q at hTheta
  rw [mul_assoc] at hTheta
  obtain ⟨e, he, hpe⟩ := Ideal.mem_span_singleton_mul.mp hTheta
  have heJ : e ∈ J := (Ideal.mul_le_inf he).1
  have heI : e ∈ UnitModule.topUnitAnn p K q := (Ideal.mul_le_inf he).2
  obtain ⟨E, hE⟩ := Runge.reduceFull_surjective p K q e
  refine ⟨E, hE.symm ▸ heI, ?_, ?_⟩
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd (weight p K E) q).mp
    have hEN : Runge.reduceFull p K q E * N = 0 := by
      rw [hE]
      simpa only [smul_eq_mul] using (Submodule.mem_annihilator_span_singleton N e).mp heJ
    let plusCircularLiftGalFintype : Fintype (G p K) := Fintype.ofFinite _
    have hNcoeff (g : G p K) : N.coeff g = 1 := by
      simp [N, UnitReduction.groupNorm, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    have hc := congrArg (fun V : MonoidAlgebra (ZMod q) (G p K) => V.coeff 1) hEN
    rw [MonoidAlgebra.coeff_mul_apply_left] at hc
    simp only [hNcoeff, mul_one, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
    have hs : (∑ g : G p K, (Runge.reduceFull p K q E).coeff g) = 0 :=
      (Finsupp.sum_fintype _ (fun _ r => r) (fun _ => rfl)).symm.trans hc
    rw [weight_eq_sum, Int.cast_sum]
    simpa only [Runge.reduceFull, MonoidAlgebra.coeff_mapRingHom, Int.coe_castRingHom] using hs
  · rw [map_mul, hE]
    have hP : Runge.reduceFull p K q (1 + MonoidAlgebra.single (ι p K) 1) =
        1 + MonoidAlgebra.single (ι p K) (1 : ZMod q) := by
      simp only [map_add, map_one, Runge.reduceFull, MonoidAlgebra.mapRingHom_single]
    rw [hP]
    exact hpe

end Catalan.Thaine
