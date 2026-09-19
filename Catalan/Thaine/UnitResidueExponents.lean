import Catalan.Thaine.IntegralUnitPow
import Catalan.Thaine.ResidueExponent
import Catalan.Density.OrbitAction
import Catalan.Density.UnitResidueCoordinates

set_option autoImplicit false
open NumberField
open scoped BigOperators
noncomputable section
namespace Catalan.A3
variable (p q : ℕ) [Fact q.Prime]
local instance unitExponentGalFintype : Fintype (G p (F p)) := Fintype.ofFinite _

lemma unitResidueCoordinates_integralUnitPow
    (ell : ℕ) (red : 𝓞 (F p) →+* ZMod ell)
    (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q)
    (u : (𝓞 (F p))ˣ) (b : ZMod q)
    (hu : ∀ g : G p (F p),
      unitResidueCoordinates p q ell red e (UnitQuotient.powerClass q u) g =
        (1 : MonoidAlgebra (ZMod q) (G p (F p))).coeff g - b)
    (Theta : R p (F p)) (g : G p (F p)) :
    unitResidueCoordinates p q ell red e
      (UnitQuotient.powerClass q (UnitModule.integralUnitPow p (F p) u Theta)) g =
        (Theta.coeff g : ZMod q) - (weight p (F p) Theta : ZMod q) * b := by
  rw [UnitModule.powerClass_integralUnitPow]
  have h := Residue.inverseOrbitMap_canonical_action
    (UnitModule.unitRepresentation p (F p) q) (unitResidueFunctional p q ell red e)
    (UnitQuotient.powerClass q u) b hu (Runge.reduceFull p (F p) q Theta) g
  simpa only [unitResidueCoordinates, Runge.reduceFull, MonoidAlgebra.coeff_mapRingHom, Int.coe_castRingHom,
    weight_eq_sum, Int.cast_sum] using h

lemma unit_residue_exponents_of_canonical
    (ell : ℕ) (red : 𝓞 (F p) →+* ZMod ell)
    (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q)
    (s : (ZMod ell)ˣ) (hs : e (UnitQuotient.powerClass q s) = 1)
    (u : (𝓞 (F p))ˣ) (b : ZMod q)
    (hu : ∀ g : G p (F p),
      unitResidueCoordinates p q ell red e (UnitQuotient.powerClass q u) g =
        (1 : MonoidAlgebra (ZMod q) (G p (F p))).coeff g - b)
    (Theta : R p (F p)) (hw : (weight p (F p) Theta : ZMod q) = 0)
    (g : G p (F p)) :
    ∃ w : (ZMod ell)ˣ,
      Units.map red.toMonoidHom (Circular.unitAction p (F p) g⁻¹
        (UnitModule.integralUnitPow p (F p) u Theta)) = s ^ (Theta.coeff g) * w ^ q := by
  apply (Residue.coordinate_eq_iff_power_error q e s hs _ _).mp
  rw [← unitResidueCoordinates_powerClass,
    unitResidueCoordinates_integralUnitPow p q ell red e u b hu Theta g,
    hw, zero_mul, sub_zero]

lemma exists_unit_residue_exponent_generator [Fact p.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hdegree : ¬ q ∣ (p - 1) / 2)
    (ell : ℕ) (red : 𝓞 (F p) →+* ZMod ell)
    (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q)
    (s : (ZMod ell)ˣ) (hs : e (UnitQuotient.powerClass q s) = 1)
    (hsep : ∀ u : (𝓞 (F p))ˣ,
      (∀ g : G p (F p), ∃ w : (ZMod ell)ˣ,
        w ^ q = Units.map red.toMonoidHom (Circular.unitAction p (F p) g u)) →
      ∃ w : (𝓞 (F p))ˣ, w ^ q = u) :
    ∃ u : (𝓞 (F p))ˣ, ∀ Theta : R p (F p),
      (weight p (F p) Theta : ZMod q) = 0 → ∀ g : G p (F p),
        ∃ w : (ZMod ell)ˣ,
          Units.map red.toMonoidHom (Circular.unitAction p (F p) g⁻¹
            (UnitModule.integralUnitPow p (F p) u Theta)) = s ^ (Theta.coeff g) * w ^ q := by
  obtain ⟨u, hu⟩ := exists_unit_augmentation_coordinates p q hp2 hq2 hdegree ell red e hsep
  refine ⟨u, fun Theta hw g => ?_⟩
  exact unit_residue_exponents_of_canonical p q ell red e s hs u
    (Fintype.card (G p (F p)) : ZMod q)⁻¹ hu Theta hw g

end Catalan.A3
