module

public import Catalan.CaseOne.UnitNorm
public import Catalan.CaseOne.ThreeStep
public import Catalan.CaseOne.CircularModule
public import Catalan.CaseOne.UnitCyclic

/-!
# `Catalan.CaseOne.UnitFiltration`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.UnitModule
variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
local instance filtrationGalComm : CommGroup (G p K) := cyclotomicGalCommGroup p K

/-- Annihilator of the top factor in the actual circular-unit image filtration. -/
def topUnitAnn (q : ℕ) : Ideal (MonoidAlgebra (ZMod q) (G p K)) :=
  Module.annihilator (MonoidAlgebra (ZMod q) (G p K))
    ((UnitPowerModule p K q) ⧸ circularImage p K q)

/-- Annihilator of the circular image modulo its primary subimage. -/
def middleUnitAnn (q : ℕ) (hq : 0 < q) : Ideal (MonoidAlgebra (ZMod q) (G p K)) :=
  Module.annihilator (MonoidAlgebra (ZMod q) (G p K))
    ((circularImage p K q) ⧸ (primaryCircularImage p K q hq).comap (circularImage p K q).subtype)

/-- Annihilator of the primary circular image. -/
def bottomUnitAnn (q : ℕ) (hq : 0 < q) : Ideal (MonoidAlgebra (ZMod q) (G p K)) :=
  Module.annihilator (MonoidAlgebra (ZMod q) (G p K)) (primaryCircularImage p K q hq)

lemma unit_filtration_pairwise_of_solution (q : ℕ) [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) :
    (topUnitAnn p K q ⊔ middleUnitAnn p K q (Fact.out : q.Prime).pos = ⊤) ∧
    (topUnitAnn p K q ⊔ bottomUnitAnn p K q (Fact.out : q.Prime).pos = ⊤) ∧
    (middleUnitAnn p K q (Fact.out : q.Prime).pos ⊔ bottomUnitAnn p K q (Fact.out : q.Prime).pos = ⊤) := by
  have instSemi : IsSemisimpleModule (MonoidAlgebra (ZMod q) (G p K)) (UnitPowerModule p K q) :=
    unitPower_semisimple p K q (not_dvd_gal_card_of_solution p K q hp2 hq2 x y hx hy h)
  exact UnitReduction.three_step_annihilator_pairwise
    (unit_module_cyclic_of_solution p K q hp2 hq2 x y hx hy h)
    (primaryCircularImage p K q (Fact.out : q.Prime).pos) (circularImage p K q)
    (primaryCircularImage_le p K q (Fact.out : q.Prime).pos)

lemma unit_filtration_product_of_solution (q : ℕ) [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x ^ p = y ^ q + 1) :
    topUnitAnn p K q * middleUnitAnn p K q (Fact.out : q.Prime).pos *
      bottomUnitAnn p K q (Fact.out : q.Prime).pos = normPlusIdeal p K q := by
  have instSemi : IsSemisimpleModule (MonoidAlgebra (ZMod q) (G p K)) (UnitPowerModule p K q) :=
    unitPower_semisimple p K q (not_dvd_gal_card_of_solution p K q hp2 hq2 x y hx hy h)
  rw [← unit_annihilator_eq_normPlus_of_solution p K q hp2 hq2 x y hx hy h]
  exact (UnitReduction.three_step_annihilator_product
    (unit_module_cyclic_of_solution p K q hp2 hq2 x y hx hy h)
    (primaryCircularImage p K q (Fact.out : q.Prime).pos) (circularImage p K q)
    (primaryCircularImage_le p K q (Fact.out : q.Prime).pos)).symm

lemma middleUnitAnn_ne_top (q : ℕ) [Fact q.Prime] (hqp : q < p) :
    middleUnitAnn p K q (Fact.out : q.Prime).pos ≠ ⊤ := by
  intro htop
  have hsub : Subsingleton ((circularImage p K q) ⧸
      (primaryCircularImage p K q (Fact.out : q.Prime).pos).comap (circularImage p K q).subtype) :=
    (Module.annihilator_eq_top_iff).mp htop
  have hle : circularImage p K q ≤ primaryCircularImage p K q (Fact.out : q.Prime).pos := by
    intro v hv
    have hz : (Submodule.Quotient.mk (⟨v, hv⟩ : circularImage p K q) :
        (circularImage p K q) ⧸ (primaryCircularImage p K q (Fact.out : q.Prime).pos).comap
          (circularImage p K q).subtype) = 0 := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero
      ((primaryCircularImage p K q (Fact.out : q.Prime).pos).comap (circularImage p K q).subtype)).mp hz
  exact (primaryCircularImage_lt p K q Fact.out hqp).not_ge hle

end Catalan.UnitModule
