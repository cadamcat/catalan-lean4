module

public import Catalan.Thaine.CircularClosure
public import Catalan.Thaine.IntegralUnitPow
public import Catalan.CaseOne.PowerImage

/-!
# `Catalan.Thaine.RealUnitAnnihilator`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

def realUnitAnnihilator (p q : ℕ) (Theta : R p (A3.F p)) : Prop :=
  ∀ u : (𝓞 (A3.F p))ˣ,
    UnitQuotient.powerClass q (UnitModule.integralUnitPow p (A3.F p) u Theta) ∈
      UnitQuotient.powerImage ((𝓞 (A3.F p))ˣ) q (realCircularUnits p)

lemma realUnitAnnihilator_iff_circular_powerClass
    (p q : ℕ) (Theta : R p (A3.F p)) :
    realUnitAnnihilator p q Theta ↔
      ∀ u : (𝓞 (A3.F p))ˣ, ∃ d : (𝓞 (A3.F p))ˣ, d ∈ realCircularUnits p ∧
        UnitQuotient.powerClass q d =
          UnitQuotient.powerClass q (UnitModule.integralUnitPow p (A3.F p) u Theta) := by
  simp only [realUnitAnnihilator, UnitQuotient.mem_powerImage_iff]

end Catalan.Thaine
