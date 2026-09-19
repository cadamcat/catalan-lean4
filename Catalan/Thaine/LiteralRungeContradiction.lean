import Catalan.Thaine.LiteralPurePower
import Catalan.Thaine.IdealNonzero
import Catalan.Runge.PlusIdeal

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance literalRungeCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p

local instance literalRungeGalComm (p : ℕ) [Fact p.Prime] :
    CommGroup (G p (A3.Bsub p p)) := UnitModule.cyclotomicGalCommGroup p (A3.Bsub p p)

lemma literal_plus_top_bottom_eq_bot
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hq7 : 7 ≤ q) (hqp : q < p)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1) :
    (UnitModule.plusAugIdeal p (A3.Bsub p p) q * UnitModule.topUnitAnn p (A3.Bsub p p) q) *
      UnitModule.bottomUnitAnn p (A3.Bsub p p) q (Fact.out : q.Prime).pos = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro theta htheta
  obtain ⟨Theta, rfl⟩ := Runge.reduceFull_surjective p (A3.Bsub p p) q theta
  have hpure : Theta ∈ mihIdeal p (A3.Bsub p p) q x (by omega) :=
    literal_xm_zeta_pure_power_of_solution p q hp7 (by omega) x y hx hy h Theta htheta
  have hmap : Runge.reduceFull p (A3.Bsub p p) q Theta ∈
      (mihIdeal p (A3.Bsub p p) q x (by omega)).map (Runge.reduceFull p (A3.Bsub p p) q) :=
    (Ideal.mem_map_iff_of_surjective (Runge.reduceFull p (A3.Bsub p p) q)
      (Runge.reduceFull_surjective p (A3.Bsub p p) q)).mpr ⟨Theta, hpure, rfl⟩
  have hB : Runge.reduceFull p (A3.Bsub p p) q Theta ∈ UnitModule.plusAugIdeal p (A3.Bsub p p) q :=
    (Ideal.mul_le_inf (Ideal.mul_le_inf htheta).1).1
  have hinter : Runge.reduceFull p (A3.Bsub p p) q Theta ∈
      (mihIdeal p (A3.Bsub p p) q x (by omega)).map (Runge.reduceFull p (A3.Bsub p p) q) ⊓
        UnitModule.plusAugIdeal p (A3.Bsub p p) q := ⟨hmap, hB⟩
  rw [Runge.reduce_mihIdeal_inf_plusAug_eq_bot_of_solution p (A3.Bsub p p) q
    hq7 hqp (by omega) x y hx hy h] at hinter
  exact hinter

lemma literal_large_odd_primes_no_solution
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hq7 : 7 ≤ q) (hqp : q < p)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ p ≠ y ^ q + 1 := by
  intro h
  have hpair := UnitModule.unit_filtration_pairwise_of_solution p (A3.Bsub p p) q
    (by omega) (by omega) x y hx hy h
  have hann : (UnitModule.plusAugIdeal p (A3.Bsub p p) q).annihilator =
      (UnitModule.topUnitAnn p (A3.Bsub p p) q *
        UnitModule.middleUnitAnn p (A3.Bsub p p) q (Fact.out : q.Prime).pos) *
          UnitModule.bottomUnitAnn p (A3.Bsub p p) q (Fact.out : q.Prime).pos := by
    rw [UnitModule.plusAugIdeal_annihilator_of_solution p (A3.Bsub p p) q
      (by omega) (by omega) x y hx hy h,
      UnitModule.unit_filtration_product_of_solution p (A3.Bsub p p) q
        (by omega) (by omega) x y hx hy h]
  have hnonzero := ideal_triple_product_ne_bot
    (MonoidAlgebra (ZMod q) (G p (A3.Bsub p p)))
    (UnitModule.plusAugIdeal p (A3.Bsub p p) q) (UnitModule.topUnitAnn p (A3.Bsub p p) q)
    (UnitModule.middleUnitAnn p (A3.Bsub p p) q (Fact.out : q.Prime).pos)
    (UnitModule.bottomUnitAnn p (A3.Bsub p p) q (Fact.out : q.Prime).pos)
    hann hpair.1 (by rw [sup_comm]; exact hpair.2.2)
    (UnitModule.middleUnitAnn_ne_top p (A3.Bsub p p) q hqp)
  exact hnonzero (literal_plus_top_bottom_eq_bot p q hp7 hq7 hqp x y hx hy h)

end Catalan.Thaine
