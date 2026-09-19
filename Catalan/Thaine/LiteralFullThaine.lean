import Catalan.Thaine.LiteralAnnihilatorReflection
import Catalan.Thaine.LiteralClassRepresentation
import Catalan.Thaine.ThaineClassQuotient

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance fullThaineCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p

lemma literalFullUnitAnnihilator_kills_class_quotient
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hpq : p ≠ q) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2)
    (Theta : R p (A3.Bsub p p)) (hTheta : literalFullUnitAnnihilator p q Theta)
    (z : UnitQuotient.PowerQuotient (ClassGroup (𝓞 (A3.F p))) q) :
    (literalClassRepresentation p q).asAlgebraHom (Runge.reduceFull p (A3.Bsub p p) q Theta) z = 0 := by
  rw [literalClassRepresentation_reduce]
  exact real_unit_annihilator_kills_class_quotient p q hp7 hq2 hdegree
    (literalRestrictionRing p Theta)
    (literalFullUnitAnnihilator_restrict p q (by omega) hpq hq2 Theta hTheta) z

lemma literal_full_circular_annihilator_kills_class_quotient
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hpq : p ≠ q) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2)
    (Theta : R p (A3.Bsub p p))
    (hTheta : Runge.reduceFull p (A3.Bsub p p) q Theta ∈
      Module.annihilator (MonoidAlgebra (ZMod q) (G p (A3.Bsub p p)))
        ((UnitModule.UnitPowerModule p (A3.Bsub p p) q) ⧸
          UnitModule.circularImage p (A3.Bsub p p) q))
    (z : UnitQuotient.PowerQuotient (ClassGroup (𝓞 (A3.F p))) q) :
    (literalClassRepresentation p q).asAlgebraHom (Runge.reduceFull p (A3.Bsub p p) q Theta) z = 0 :=
  literalFullUnitAnnihilator_kills_class_quotient p q hp7 hpq hq2 hdegree Theta
    ((literalFullUnitAnnihilator_iff_module_annihilator p q Theta).mpr hTheta) z

end Catalan.Thaine
