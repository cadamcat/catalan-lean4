import Catalan.Thaine.LiteralMaps
import Catalan.Thaine.IntegralUnitPow
import Catalan.CaseOne.CircularModule

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance fullAnnihilatorCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p

def literalFullUnitAnnihilator (p q : ℕ) [Fact p.Prime]
    (Theta : R p (A3.Bsub p p)) : Prop :=
  ∀ u : (𝓞 (A3.Bsub p p))ˣ,
    UnitQuotient.powerClass q (UnitModule.integralUnitPow p (A3.Bsub p p) u Theta) ∈
      UnitQuotient.powerImage ((𝓞 (A3.Bsub p p))ˣ) q (literalFullCircularUnits p)

lemma unitClass_integralUnitPow
    (p : ℕ) (K : Type*) [Field K] [NumberField K] (q : ℕ)
    (u : (𝓞 K)ˣ) (Theta : R p K) :
    UnitModule.unitClass p K q (UnitModule.integralUnitPow p K u Theta) =
      (Runge.reduceFull p K q Theta) • UnitModule.unitClass p K q u := by
  apply (UnitModule.unitRepresentation p K q).asModuleEquiv.injective
  rw [Representation.asModuleEquiv_map_smul]
  simp only [UnitModule.unitClass, LinearEquiv.apply_symm_apply]
  exact UnitModule.powerClass_integralUnitPow p K q u Theta

lemma literalFullUnitAnnihilator_iff_module_annihilator
    (p q : ℕ) [Fact p.Prime] (Theta : R p (A3.Bsub p p)) :
    literalFullUnitAnnihilator p q Theta ↔
      Runge.reduceFull p (A3.Bsub p p) q Theta ∈
        Module.annihilator (MonoidAlgebra (ZMod q) (G p (A3.Bsub p p)))
          ((UnitModule.UnitPowerModule p (A3.Bsub p p) q) ⧸
            UnitModule.circularImage p (A3.Bsub p p) q) := by
  let W := UnitModule.circularImage p (A3.Bsub p p) q
  let r := Runge.reduceFull p (A3.Bsub p p) q Theta
  have hunit (u : (𝓞 (A3.Bsub p p))ˣ) :
      r • UnitModule.unitClass p (A3.Bsub p p) q u ∈ W ↔
        UnitQuotient.powerClass q (UnitModule.integralUnitPow p (A3.Bsub p p) u Theta) ∈
          UnitQuotient.powerImage ((𝓞 (A3.Bsub p p))ˣ) q (literalFullCircularUnits p) := by
    rw [← unitClass_integralUnitPow]
    rfl
  constructor
  · intro h
    apply Module.mem_annihilator.mpr
    intro z
    obtain ⟨v, rfl⟩ := LinearMap.range_eq_top.mp W.range_mkQ z
    obtain ⟨u, rfl⟩ := UnitModule.unitClass_surjective p (A3.Bsub p p) q v
    rw [← map_smul]
    have hmem := (hunit u).mpr (h u)
    have hker : r • UnitModule.unitClass p (A3.Bsub p p) q u ∈ LinearMap.ker W.mkQ := by
      rwa [W.ker_mkQ]
    exact hker
  · intro h u
    apply (hunit u).mp
    have hz := Module.mem_annihilator.mp h (W.mkQ (UnitModule.unitClass p (A3.Bsub p p) q u))
    have hker : r • UnitModule.unitClass p (A3.Bsub p p) q u ∈ LinearMap.ker W.mkQ := by
      change W.mkQ (r • UnitModule.unitClass p (A3.Bsub p p) q u) = 0
      rw [map_smul]
      exact hz
    rwa [W.ker_mkQ] at hker

end Catalan.Thaine
