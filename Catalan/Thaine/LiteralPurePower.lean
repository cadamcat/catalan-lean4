import Catalan.Thaine.LiteralPrimaryPower
import Catalan.Thaine.BottomPower

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance literalPurePowerCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p

local instance literalPurePowerGalComm (p : ℕ) [Fact p.Prime] :
    CommGroup (G p (A3.Bsub p p)) := UnitModule.cyclotomicGalCommGroup p (A3.Bsub p p)

lemma literal_xm_zeta_pure_power_of_solution
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp7 : 7 ≤ p) (hq2 : q ≠ 2)
    (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h : x ^ p = y ^ q + 1)
    (Theta : R p (A3.Bsub p p))
    (hTheta : Runge.reduceFull p (A3.Bsub p p) q Theta ∈
      (UnitModule.plusAugIdeal p (A3.Bsub p p) q * UnitModule.topUnitAnn p (A3.Bsub p p) q) *
        UnitModule.bottomUnitAnn p (A3.Bsub p p) q (Fact.out : q.Prime).pos) :
    ∃ b : (A3.Bsub p p)ˣ,
      upow p (A3.Bsub p p) (xmζ p (A3.Bsub p p) x (by omega)) Theta = b ^ q := by
  apply pure_power_of_primary_powers p q (A3.Bsub p p)
    (UnitModule.not_dvd_gal_card_of_solution p (A3.Bsub p p) q (by omega) hq2 x y hx hy h)
    (xmζ p (A3.Bsub p p) x (by omega))
    (UnitModule.plusAugIdeal p (A3.Bsub p p) q * UnitModule.topUnitAnn p (A3.Bsub p p) q)
    ?_ Theta hTheta
  intro Psi hPsi
  exact literal_xm_zeta_primary_power_of_solution p q hp7 hq2 x y hx hy h Psi hPsi

end Catalan.Thaine
