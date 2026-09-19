import GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicTorsionField
import GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicCharacterEquiv
import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Basic
import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Local
import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FiniteFree
import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Gather
import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Swap
import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Decomposition
import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.DenseTorsion
import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientEquiv
import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientMk
import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.CyclotomicQuotient
import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FreeCoordinate
import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FiniteOrder

set_option autoImplicit false

/-!
# The cyclotomic torsion fixed field

`rationalCyclotomicField` now denotes the actual field `ℚ(μ∞)` inside
`SeparableClosure ℚ`.  Its actual Galois group is therefore the standard
mathlib type
`rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField`; its finite
cyclotomic levels form a divisibility-directed system with supremum the
whole field.  The torsion fixed field is the actual
intermediate field `rationalCyclotomicTorsionFixedField`.

The actual continuous cyclotomic character identifies the full Galois
group with `ℤ̂ˣ`.  Applying infinite Galois correspondence to the actual
torsion closure and the group-theoretic decomposition of `ℤ̂ˣ` gives the
cyclotomic `ℤ̂`-extension.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open scoped IsMulCommutative
open KummerTheory
open ClassFormation

/-- The Galois group of the actual torsion fixed field in
`ℚ(μ∞)` is the additive group of the profinite integers, written
multiplicatively. -/
noncomputable def rationalCyclotomicTorsionFixedFieldGalEquivZHat :
    (rationalCyclotomicTorsionFixedField ≃ₐ[ℚ]
      rationalCyclotomicTorsionFixedField) ≃ₜ*
        Multiplicative ZHat := by
  letI : T2Space
      (rationalCyclotomicTorsionFixedField ≃ₐ[ℚ]
        rationalCyclotomicTorsionFixedField) :=
    krullTopology_t2
  let q :
      (rationalCyclotomicField ≃ₐ[ℚ]
          rationalCyclotomicField) ⧸
          rationalCyclotomicTorsionClosure.toSubgroup ≃ₜ*
        (rationalCyclotomicTorsionFixedField ≃ₐ[ℚ]
          rationalCyclotomicTorsionFixedField) :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.continuousMulEquivOfCompactToT2
        (InfiniteGalois.normalAutEquivQuotient
          (k := ℚ) (K := rationalCyclotomicField)
          rationalCyclotomicTorsionClosure)
        (by
          rw [←
            QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
          exact
            InfiniteGalois.restrictNormalHom_continuous
              rationalCyclotomicTorsionFixedField)
  exact q.symm.trans <|
    torsionQuotientEquivOfZHatMulDecomposition
      (rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField)
      CyclotomicFinitePart
      (rationalCyclotomicCharacterContinuousMulEquiv.trans
        zHatUnitsDecomposition)
      dense_torsion_cyclotomicFinitePart

/-- Restriction of an actual automorphism of the full rational
cyclotomic field to the torsion fixed field is sent to the genuine
torsion-free coordinate of its cyclotomic character. -/
@[simp]
theorem
    rationalCyclotomicTorsionFixedFieldGalEquivZHat_restrictNormal
    (σ :
      rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField) :
    rationalCyclotomicTorsionFixedFieldGalEquivZHat
        (AlgEquiv.restrictNormalHom
          rationalCyclotomicTorsionFixedField σ) =
      (zHatUnitsDecomposition
        (rationalCyclotomicCharacterContinuousMulEquiv σ)).1 := by
  let q :
      (rationalCyclotomicField ≃ₐ[ℚ]
          rationalCyclotomicField) ⧸
          rationalCyclotomicTorsionClosure.toSubgroup ≃ₜ*
        (rationalCyclotomicTorsionFixedField ≃ₐ[ℚ]
          rationalCyclotomicTorsionFixedField) :=
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.continuousMulEquivOfCompactToT2
      (InfiniteGalois.normalAutEquivQuotient
        (k := ℚ) (K := rationalCyclotomicField)
        rationalCyclotomicTorsionClosure)
      (by
        rw [←
          QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
        exact
          InfiniteGalois.restrictNormalHom_continuous
            rationalCyclotomicTorsionFixedField)
  change
    torsionQuotientEquivOfZHatMulDecomposition
        (rationalCyclotomicField ≃ₐ[ℚ]
          rationalCyclotomicField)
        CyclotomicFinitePart
        (rationalCyclotomicCharacterContinuousMulEquiv.trans
          zHatUnitsDecomposition)
        dense_torsion_cyclotomicFinitePart
        (q.symm
          (AlgEquiv.restrictNormalHom
            rationalCyclotomicTorsionFixedField σ)) =
      (zHatUnitsDecomposition
        (rationalCyclotomicCharacterContinuousMulEquiv σ)).1
  have hrestrict :
      InfiniteGalois.normalAutEquivQuotient
          rationalCyclotomicTorsionClosure σ =
        AlgEquiv.restrictNormalHom
          rationalCyclotomicTorsionFixedField σ := by
    exact
      InfiniteGalois.normalAutEquivQuotient_apply
        rationalCyclotomicTorsionClosure σ
  have hquotient :
      q.symm
          (InfiniteGalois.normalAutEquivQuotient
            rationalCyclotomicTorsionClosure σ) =
        QuotientGroup.mk σ := by
    apply q.symm_apply_eq.mpr
    rfl
  rw [← hrestrict, hquotient]
  exact
    torsionQuotientEquivOfZHatMulDecomposition_mk
      (rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
      CyclotomicFinitePart
      (rationalCyclotomicCharacterContinuousMulEquiv.trans
        zHatUnitsDecomposition)
      dense_torsion_cyclotomicFinitePart σ

end Reciprocity
end GlobalClassFieldTheory
