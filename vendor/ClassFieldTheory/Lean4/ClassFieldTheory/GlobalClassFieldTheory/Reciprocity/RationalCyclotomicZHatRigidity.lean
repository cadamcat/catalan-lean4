import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicPrincipalIdele
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicCharacterRigidity

set_option autoImplicit false

/-!
# Prime-power detection for the rational cyclotomic `ZHat`-Artin map

Prime-power reductions of the genuine cyclotomic character detect the
full rational cyclotomic automorphism.  Restricting that automorphism
through actual finite cyclotomic levels then detects every finite
coordinate of the rational cyclotomic `ZHat`-extension.
-/

open scoped Classical NumberField IsMulCommutative
open NumberField ClassFormation

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

local instance (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

/-- If all prime-power character reductions of the full cyclotomic
global Artin symbol have square one, then the corresponding Artin symbol
in the actual rational `ZHat`-extension has square one. -/
theorem
    rationalCyclotomicZHatGlobalArtin_sq_eq_one_of_character_reductions
    (a : IdeleGroup ℚ)
    (h :
      ∀ (p : Nat.Primes) (k : ℕ),
        Units.map (PadicInt.toZModPow k).toMonoidHom
              (KummerTheory.rationalCyclotomicCharacterPrimeProduct
                (infiniteGlobalArtinMonoidHom
                  ℚ KummerTheory.rationalCyclotomicField a) p) ^ 2 =
          1) :
    rationalCyclotomicZHatGlobalArtin a ^ 2 = 1 := by
  let σ :
      KummerTheory.rationalCyclotomicField ≃ₐ[ℚ]
        KummerTheory.rationalCyclotomicField :=
    infiniteGlobalArtinMonoidHom
      ℚ KummerTheory.rationalCyclotomicField a
  have hσ : σ ^ 2 = 1 :=
    rationalCyclotomicAutomorphism_sq_eq_one_of_character_reductions
      σ h
  let
      (E :
        FiniteGaloisIntermediateField
          ℚ rationalCyclotomicZHatField) :
      NumberField E :=
    NumberField.of_module_finite ℚ E
  let
      (E :
        FiniteGaloisIntermediateField
          ℚ rationalCyclotomicZHatField) :
      IsAbelianGalois ℚ E :=
    IsAbelianGalois.of_algHom E.toIntermediateField.val
  have happly :
      InfiniteGalois.continuousMulEquivToLimit
          ℚ rationalCyclotomicZHatField
          (rationalCyclotomicZHatGlobalArtin a) =
        infiniteGlobalArtinToLimit
          ℚ rationalCyclotomicZHatField a := by
    exact
      (InfiniteGalois.continuousMulEquivToLimit
        ℚ rationalCyclotomicZHatField).apply_symm_apply _
  apply
    (InfiniteGalois.continuousMulEquivToLimit
      ℚ rationalCyclotomicZHatField).injective
  rw [map_pow, happly, map_one]
  apply Subtype.ext
  funext E
  change
    globalArtinMonoidHom
          (K := ℚ) (L := E.unop) a ^ 2 =
      1
  obtain ⟨n, F, e, hF⟩ :=
    finiteSubfieldOfRationalCyclotomicZHatField_mapsIntoLevel E.unop
  let : FiniteDimensional ℚ F :=
    e.toLinearEquiv.finiteDimensional
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
  let : IsAbelianGalois ℚ F :=
    IsAbelianGalois.of_algHom e.symm.toAlgHom
  let algEF : Algebra E.unop F :=
    e.toRingHom.toAlgebra
  let : SMul E.unop F :=
    @Algebra.toSMul E.unop F _ _ algEF
  let : Algebra E.unop F := algEF
  let : Module E.unop F := Algebra.toModule
  let : IsScalarTower ℚ E.unop F :=
    IsScalarTower.of_algebraMap_eq'
      e.toAlgHom.comp_algebraMap.symm
  let : FiniteDimensional E.unop F :=
    FiniteDimensional.right ℚ E.unop F
  let algFN :
      Algebra F
        (KummerTheory.rationalCyclotomicLevel n) :=
    (IntermediateField.inclusion hF).toRingHom.toAlgebra
  let :
      SMul F
        (KummerTheory.rationalCyclotomicLevel n) :=
    @Algebra.toSMul F
      (KummerTheory.rationalCyclotomicLevel n) _ _ algFN
  let :
      Algebra F
        (KummerTheory.rationalCyclotomicLevel n) :=
    algFN
  let :
      IsScalarTower ℚ F
        (KummerTheory.rationalCyclotomicLevel n) :=
    IsScalarTower.of_algebraMap_eq'
      (IntermediateField.inclusion hF).comp_algebraMap.symm
  let N : FiniteGaloisIntermediateField
      ℚ KummerTheory.rationalCyclotomicField :=
    { toIntermediateField :=
        KummerTheory.rationalCyclotomicLevel n
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  let : NumberField N :=
    NumberField.of_module_finite ℚ N
  let : IsAbelianGalois ℚ N :=
    IsAbelianGalois.of_algHom N.toIntermediateField.val
  have hlevel :
      globalArtinMonoidHom
            (K := ℚ)
            (L := N)
            a ^ 2 =
        1 := by
    have hrestriction :
        AlgEquiv.restrictNormalHom N σ =
          globalArtinMonoidHom (K := ℚ) (L := N) a :=
      restrictNormalHom_infiniteGlobalArtinMonoidHom
        ℚ KummerTheory.rationalCyclotomicField a N
    calc
      globalArtinMonoidHom (K := ℚ) (L := N) a ^ 2 =
          (AlgEquiv.restrictNormalHom N σ) ^ 2 :=
        congrArg (fun τ => τ ^ 2) hrestriction.symm
      _ = AlgEquiv.restrictNormalHom N (σ ^ 2) :=
        (map_pow (AlgEquiv.restrictNormalHom N) σ 2).symm
      _ = AlgEquiv.restrictNormalHom N 1 :=
        congrArg (AlgEquiv.restrictNormalHom N) hσ
      _ = 1 := map_one (AlgEquiv.restrictNormalHom N)
  have hcoordinate :
      AlgEquiv.restrictNormalHom E.unop
          (AlgEquiv.restrictNormalHom F
            (globalArtinMonoidHom
              (K := ℚ)
              (L := N)
              a)) =
        globalArtinMonoidHom
          (K := ℚ) (L := E.unop) a := by
    have hFCoordinate :=
      DFunLike.congr_fun
        (globalArtinMonoidHom_restrict_tower
          (K := ℚ)
          (L := N)
          (E := F)) a
    have hECoordinate :=
      DFunLike.congr_fun
        (globalArtinMonoidHom_restrict_tower
          (K := ℚ) (L := F) (E := E.unop)) a
    exact
      (congrArg (AlgEquiv.restrictNormalHom E.unop)
        hFCoordinate).trans hECoordinate
  calc
    globalArtinMonoidHom (K := ℚ) (L := E.unop) a ^ 2 =
        (AlgEquiv.restrictNormalHom E.unop
          (AlgEquiv.restrictNormalHom F
            (globalArtinMonoidHom (K := ℚ) (L := N) a))) ^ 2 :=
      congrArg (fun τ => τ ^ 2) hcoordinate.symm
    _ = AlgEquiv.restrictNormalHom E.unop
        ((AlgEquiv.restrictNormalHom F
          (globalArtinMonoidHom (K := ℚ) (L := N) a)) ^ 2) :=
      (map_pow (AlgEquiv.restrictNormalHom E.unop) _ 2).symm
    _ = AlgEquiv.restrictNormalHom E.unop
        (AlgEquiv.restrictNormalHom F
          (globalArtinMonoidHom (K := ℚ) (L := N) a ^ 2)) :=
      congrArg (AlgEquiv.restrictNormalHom E.unop)
        ((map_pow (AlgEquiv.restrictNormalHom F)
          (globalArtinMonoidHom (K := ℚ) (L := N) a) 2).symm)
    _ = AlgEquiv.restrictNormalHom E.unop
        (AlgEquiv.restrictNormalHom F 1) :=
      congrArg
        (fun τ => AlgEquiv.restrictNormalHom E.unop
          (AlgEquiv.restrictNormalHom F τ)) hlevel
    _ = AlgEquiv.restrictNormalHom E.unop 1 :=
      congrArg (AlgEquiv.restrictNormalHom E.unop)
        (map_one (AlgEquiv.restrictNormalHom F))
    _ = 1 := map_one (AlgEquiv.restrictNormalHom E.unop)

/-- Prime-power square-one identities force the rational cyclotomic
idele value itself to be trivial.  Torsion-freeness of `ZHat` removes
the residual order-two ambiguity. -/
theorem
    rationalCyclotomicZHatIdeleValue_eq_one_of_character_reductions
    (a : IdeleGroup ℚ)
    (h :
      ∀ (p : Nat.Primes) (k : ℕ),
        Units.map (PadicInt.toZModPow k).toMonoidHom
              (KummerTheory.rationalCyclotomicCharacterPrimeProduct
                (infiniteGlobalArtinMonoidHom
                  ℚ KummerTheory.rationalCyclotomicField a) p) ^ 2 =
          1) :
    rationalCyclotomicZHatIdeleValue a = 1 := by
  have hArtin :
      rationalCyclotomicZHatGlobalArtin a ^ 2 = 1 :=
    rationalCyclotomicZHatGlobalArtin_sq_eq_one_of_character_reductions
      a h
  have hValue :
      rationalCyclotomicZHatIdeleValue a ^ 2 = 1 := by
    rw [rationalCyclotomicZHatIdeleValue_apply,
      ← map_pow, hArtin, map_one]
  exact
    (pow_left_injective
      (M := Multiplicative ZHat)
      (n := 2) (by norm_num))
        (by simpa using hValue)

end Reciprocity
end GlobalClassFieldTheory
