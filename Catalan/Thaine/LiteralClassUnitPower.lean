import Catalan.Thaine.IdealClassPower
import Catalan.Thaine.LiteralPrimaryLift

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance classUnitPowerCyclotomic (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (A3.Bsub p p) := literalFullCyclotomic p

lemma literal_annihilator_unit_power
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp7 : 7 ≤ p) (hpq : p ≠ q) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2)
    (Theta : R p (A3.Bsub p p))
    (hTheta : Runge.reduceFull p (A3.Bsub p p) q Theta ∈
      Module.annihilator (MonoidAlgebra (ZMod q) (G p (A3.Bsub p p)))
        ((UnitModule.UnitPowerModule p (A3.Bsub p p) q) ⧸
          UnitModule.circularImage p (A3.Bsub p p) q))
    (lam : (A3.F p)ˣ) (J : FracIdealUnit (A3.F p))
    (hideal : principalIdeal (A3.F p) lam = J ^ q) :
    ∃ u : (𝓞 (A3.F p))ˣ, ∃ b : (A3.F p)ˣ,
      upow p (A3.F p) lam (literalRestrictionRing p Theta) =
        Units.map (algebraMap (𝓞 (A3.F p)) (A3.F p)).toMonoidHom u * b ^ q := by
  have hprincipal : ClassGroup.mk (A3.F p) (principalIdeal (A3.F p) lam) = 1 := by
    apply ClassGroup.mk_eq_one_iff.mpr
    apply (FractionalIdeal.isPrincipal_iff _).mpr
    exact ⟨(lam : A3.F p), coe_toPrincipalIdeal lam⟩
  have hqclass : q • Additive.ofMul (ClassGroup.mk (A3.F p) J) = 0 := by
    change Additive.ofMul ((ClassGroup.mk (A3.F p) J) ^ q) = 0
    rw [← map_pow, ← hideal, hprincipal]
    rfl
  have hkill := literal_full_annihilator_kills_q_torsion p q hp7 hpq hq2 hdegree
    Theta hTheta (Additive.ofMul (ClassGroup.mk (A3.F p) J)) hqclass
  exact upow_eq_unit_mul_pow_of_class_annihilation p q (A3.F p) lam J
    (literalRestrictionRing p Theta) hideal hkill

end Catalan.Thaine
