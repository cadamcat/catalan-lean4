import Catalan.Thaine.LiteralFieldPowers
import Catalan.Thaine.LiteralQuadraticNorm

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance normPowersCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p

local instance normPowersGalComm (p : ℕ) [Fact p.Prime] :
    CommGroup (G p (A3.Bsub p p)) := UnitModule.cyclotomicGalCommGroup p (A3.Bsub p p)

lemma literalNormMap_eq_mul_iota
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : (A3.Bsub p p)ˣ) :
    literalFieldUnitMap p (literalNormMap p a) =
      a * actUnit p (A3.Bsub p p) (ι p (A3.Bsub p p)) a := by
  apply Units.ext
  exact literal_norm_eq_mul_iota p hp2 (a : A3.Bsub p p)

lemma literal_norm_upow_compat
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (a : (A3.Bsub p p)ˣ)
    (Theta : R p (A3.Bsub p p)) :
    literalFieldUnitMap p (upow p (A3.F p) (literalNormMap p a) (literalRestrictionRing p Theta)) =
      upow p (A3.Bsub p p) a
        ((1 + MonoidAlgebra.single (ι p (A3.Bsub p p)) 1) * Theta) := by
  have h1 : upow p (A3.Bsub p p) a 1 = a := by
    change upow p (A3.Bsub p p) a (MonoidAlgebra.single 1 1) = a
    rw [upow_single, zpow_one]
    rfl
  have hpair : a * actUnit p (A3.Bsub p p) (ι p (A3.Bsub p p)) a =
      upow p (A3.Bsub p p) a (1 + MonoidAlgebra.single (ι p (A3.Bsub p p)) 1) := by
    rw [upow_add, h1, upow_single, zpow_one]
  rw [literal_field_upow_compat, literalNormMap_eq_mul_iota p hp2, hpair, ← upow_mul, mul_comm]

end Catalan.Thaine
