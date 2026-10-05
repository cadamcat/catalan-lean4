module

public import Catalan.Thaine.UnitResidueExponents

/-!
# `Catalan.Thaine.ResidueCoordinateSquare`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField
noncomputable section
namespace Catalan.Thaine

lemma twice_unitResidueCoordinate_of_residue_power
    (p q ell : ℕ) [Fact q.Prime]
    (red : 𝓞 (A3.F p) →+* ZMod ell)
    (e : UnitQuotient.PowerQuotient (ZMod ell)ˣ q ≃ₗ[ZMod q] ZMod q)
    (s : (ZMod ell)ˣ) (hs : e (UnitQuotient.powerClass q s) = 1)
    (d : (𝓞 (A3.F p))ˣ) (g : G p (A3.F p)) (n : ℕ)
    (hres : red (A3.integralAut g⁻¹ ((d ^ 2 : (𝓞 (A3.F p))ˣ) : 𝓞 (A3.F p))) =
      (s : ZMod ell) ^ n) :
    (2 : ZMod q) * A3.unitResidueCoordinates p q ell red e
      (UnitQuotient.powerClass q d) g = (n : ZMod q) := by
  have haction : A3.integralAut g⁻¹ ((d ^ 2 : (𝓞 (A3.F p))ˣ) : 𝓞 (A3.F p)) =
      (Circular.unitAction p (A3.F p) g⁻¹ (d ^ 2) : 𝓞 (A3.F p)) := by
    apply RingOfIntegers.coe_injective
    simp [A3.integralAut, Circular.unitAction_coe,
      NumberField.RingOfIntegers.mapRingEquiv_apply]
  have hresUnit : Units.map red.toMonoidHom
      (Circular.unitAction p (A3.F p) g⁻¹ (d ^ 2)) = s ^ n := by
    apply Units.ext
    change red (Circular.unitAction p (A3.F p) g⁻¹ (d ^ 2) : 𝓞 (A3.F p)) =
      (s ^ n : (ZMod ell)ˣ)
    rw [← haction]
    exact hres
  have hclassSq : UnitQuotient.powerClass q (d ^ 2) =
      (2 : ZMod q) • UnitQuotient.powerClass q d := by
    calc
      UnitQuotient.powerClass q (d ^ 2) =
          UnitQuotient.powerClass q d + UnitQuotient.powerClass q d := by
        change Additive.ofMul (QuotientGroup.mk (d ^ 2)) = _
        rw [pow_two]
        exact (QuotientGroup.mk'
          (UnitQuotient.qPowers ((𝓞 (A3.F p))ˣ) q)).toAdditive.map_add
          (Additive.ofMul d) (Additive.ofMul d)
      _ = (2 : ZMod q) • UnitQuotient.powerClass q d :=
        (two_smul (ZMod q) (UnitQuotient.powerClass q d)).symm
  have hlinear : A3.unitResidueCoordinates p q ell red e
      (UnitQuotient.powerClass q (d ^ 2)) g =
      (2 : ZMod q) * A3.unitResidueCoordinates p q ell red e
        (UnitQuotient.powerClass q d) g := by
    rw [hclassSq, map_smul]
    simp
  have hcoordSq : A3.unitResidueCoordinates p q ell red e
      (UnitQuotient.powerClass q (d ^ 2)) g = (n : ZMod q) := by
    rw [A3.unitResidueCoordinates_powerClass]
    rw [hresUnit]
    simpa only [zpow_natCast, Int.cast_natCast] using
      (Residue.coordinate_zpow q e s hs (n : ℤ))
  rw [← hlinear]
  exact hcoordSq

end Catalan.Thaine
