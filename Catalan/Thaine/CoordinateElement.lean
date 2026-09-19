import Catalan.Thaine.UnitResidueExponents
import Catalan.Thaine.OrbitReindex
import Catalan.CaseOne.NormSum

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

local instance integralCoordinateGalFintype (p : ℕ) : Fintype (G p (A3.F p)) :=
  Fintype.ofFinite _

lemma integralUnit_coordinate_element
    (p q ell : ℕ) [Fact q.Prime]
    (red : 𝓞 (A3.F p) →+* ZMod ell)
    (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q)
    (u : (𝓞 (A3.F p))ˣ) (b : ZMod q)
    (hu : ∀ g : G p (A3.F p),
      A3.unitResidueCoordinates p q ell red e (UnitQuotient.powerClass q u) g =
        (1 : MonoidAlgebra (ZMod q) (G p (A3.F p))).coeff g - b)
    (Theta : R p (A3.F p)) :
    groupAlgebraOfFunction (ZMod q) (G p (A3.F p))
      (A3.unitResidueCoordinates p q ell red e
        (UnitQuotient.powerClass q (UnitModule.integralUnitPow p (A3.F p) u Theta))) =
      Runge.reduceFull p (A3.F p) q Theta -
        ((weight p (A3.F p) Theta : ZMod q) * b) •
          UnitReduction.groupNorm (ZMod q) (G p (A3.F p)) := by
  classical
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [groupAlgebraOfFunction_coeff]
  rw [A3.unitResidueCoordinates_integralUnitPow p q ell red e u b hu Theta g]
  simp only [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_smul,
    Runge.reduceFull]
  simp [UnitReduction.groupNorm, MonoidAlgebra.coeff_sum,
    MonoidAlgebra.coeff_single]

end Catalan.Thaine
