import Catalan.Thaine.LiteralFullAnnihilator
import Catalan.Thaine.LiteralPowerInjection
import Catalan.Thaine.CircularImageComparison
import Catalan.Thaine.LiteralRestrictionAction
import Catalan.Thaine.RealUnitAnnihilator

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma literalFullUnitAnnihilator_restrict
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hpq : p ≠ q) (hq2 : q ≠ 2)
    (Theta : R p (A3.Bsub p p)) (hTheta : literalFullUnitAnnihilator p q Theta) :
    realUnitAnnihilator p q (literalRestrictionRing p Theta) := by
  intro u
  have hfull := hTheta (literalRealUnitMap p u)
  rw [← literal_integralUnitPow_compat p u Theta] at hfull
  change literalRealPowerMap p q
    (UnitQuotient.powerClass q
      (UnitModule.integralUnitPow p (A3.F p) u (literalRestrictionRing p Theta))) ∈
    UnitQuotient.powerImage ((𝓞 (A3.Bsub p p))ˣ) q (literalFullCircularUnits p) at hfull
  rw [← full_real_circular_powerImage p q hp2 hpq hq2] at hfull
  obtain ⟨z, hz, heq⟩ := Submodule.mem_map.mp hfull
  have hsame := literal_real_unit_powerMap_injective p q hpq hq2 heq
  rwa [hsame] at hz

end Catalan.Thaine
