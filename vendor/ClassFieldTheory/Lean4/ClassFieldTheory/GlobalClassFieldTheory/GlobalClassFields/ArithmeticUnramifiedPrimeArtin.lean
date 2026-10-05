/-
MODIFIED FROM UPSTREAM:
n-yamaguchi-0729/ClassFieldTheory commit 7713795234690681b4406ae198b07aa95e82716a.
Added Lean module-system visibility declarations and ported this file to Mathlib/Lean v4.35.0-rc3.
Merged the excluded `UnramifiedNormalization` helper into this retained file to keep the 871-file subset.
-/
module

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.UnramifiedPrimeArtin
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization


/-!
# `ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin`

Part of the vendored ClassFieldTheory source bundle.
-/

@[expose] public section

set_option autoImplicit false

/-!
# Unramified normalization of the chosen finite-place Artin map

The chosen order-one input has normalized local valuation `-1` in the
geometric finite-place construction. Its local Artin image is therefore
inverse arithmetic Frobenius in the actual chosen completion.
-/

open scoped Classical NumberField ValuativeRel
open NumberField IsDedekindDomain
open AlgebraicNumberTheory.Valuations LocalFieldTheory

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [hKLfinite : FiniteDimensional K L] [IsAbelianGalois K L]

/-- Arithmetic Frobenius of the actual chosen unramified local extension. -/
noncomputable def chosenFinitePlaceLocalArithmeticFrobenius
    (v : HeightOneSpectrum (𝓞 K))
    (hunram : ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v ≃ₐ[
      ChosenFinitePlaceBaseCompletion (K := K) v]
      ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v := by
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  letI : IsGalois C E :=
    chosenFinitePlaceLocalizedIsGalois (K := K) (L := L) v
  letI : Valuation.HasExtension
      (ValuativeRel.valuation C) (ValuativeRel.valuation E) :=
    chosenFinitePlaceLocalizedValuationHasExtension (K := K) (L := L) v
  letI : IsIntegralClosure 𝒪[E] 𝒪[C] E :=
    chosenFinitePlaceLocalizedIsIntegralClosure (K := K) (L := L) v
  letI : Module.Finite 𝒪[C] 𝒪[E] :=
    chosenFinitePlaceLocalizedIntegerModuleFinite (K := K) (L := L) v
  letI : IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      C E := hunram
  exact arithmeticFrobeniusOfUnramifiedValuation C E

/-- At an unramified chosen finite place, the chosen geometric local Artin
symbol of the order-one section is inverse arithmetic Frobenius. -/
theorem chosenFinitePlaceLocalArtin_eq_arithmeticFrobenius_inv_of_unramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram : ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    finitePlaceLocalArtinMonoidHom (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v)
        (FiniteIdeleGroup.chosenLocalOrderSection v 1) =
      (chosenFinitePlaceLocalArithmeticFrobenius
        (K := K) (L := L) v hunram)⁻¹ := by
  let w := chosenFinitePlaceExtension (L := L) v
  let C := ChosenFinitePlaceBaseCompletion (K := K) v
  let E := ChosenFinitePlaceLocalizedCompletion (K := K) (L := L) v
  let x : (v.adicCompletion K)ˣ :=
    FiniteIdeleGroup.chosenLocalOrderSection v 1
  let : Algebra C E := finitePlaceLocalArtinLocalizedAlgebra v w
  let : FiniteDimensional C E := finitePlaceLocalArtinFiniteDimensional v w
  let : IsAbelianGalois C E :=
    finitePlaceLocalArtinIsAbelianGalois v w hKLfinite
  let : ValuativeRel C := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : IsIntegralClosure 𝒪[E] 𝒪[C] E :=
    chosenFinitePlaceLocalizedIsIntegralClosure (K := K) (L := L) v
  let : Module.Finite 𝒪[C] 𝒪[E] :=
    chosenFinitePlaceLocalizedIntegerModuleFinite (K := K) (L := L) v
  let : IsNonarchimedeanLocalField.IsUnramifiedValuedExtension C E := hunram
  have hval :
      IsNonarchimedeanLocalField.valuationMap C
        (Additive.ofMul (finitePlaceLocalArtinInput v x)) = -1 :=
    finitePlaceLocalArtinInput_chosenLocalOrderSection_valuationMap v
  have hfrob :=
    LocalClassFieldTheory.abelianLocalArtinMonoidHom_eq_frobenius_zpow
      C E (finitePlaceLocalArtinInput v x)
  have hnorm :
      LocalClassFieldTheory.abelianLocalArtinMonoidHom C E
          (finitePlaceLocalArtinInput v x) =
        (arithmeticFrobeniusOfUnramifiedValuation C E)⁻¹ := by
    simpa only [hval, zpow_neg_one] using hfrob
  calc
    finitePlaceLocalArtinMonoidHom (K := K) (L := L) v w x =
        LocalClassFieldTheory.abelianLocalArtinMonoidHom C E
          (finitePlaceLocalArtinInput v x) := by
      rfl
    _ = (chosenFinitePlaceLocalArithmeticFrobenius
          (K := K) (L := L) v hunram)⁻¹ := by
      exact hnorm

end Reciprocity
end GlobalClassFieldTheory

/-!
# Arithmetic Frobenius at an unramified finite place

The pre-existing local class-formation coordinate has geometric
Frobenius normalization.  This file supplies the canonical prime Artin
element used in the ideal-theoretic formulation: the ordinary normalized
prime idèle maps to arithmetic Frobenius.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField IsDedekindDomain IdeleGroup

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The arithmetic global Artin element of the ordinary normalized
one-place prime idèle. -/
noncomputable def arithmeticFinitePlacePrimeArtin
    (v : HeightOneSpectrum (𝓞 K)) :
    L ≃ₐ[K] L :=
  Reciprocity.arithmeticGlobalArtinMonoidHom K L
    (finitePrimeIdele v)

/-- The arithmetic prime Artin element is the arithmetic chosen local
Artin value of the normalized order-one element. -/
@[simp]
theorem arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin
    (v : HeightOneSpectrum (𝓞 K)) :
    arithmeticFinitePlacePrimeArtin (K := K) (L := L) v =
      Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom
        K L v (FiniteIdeleGroup.chosenLocalOrderSection v 1) := by
  rw [arithmeticFinitePlacePrimeArtin, finitePrimeIdele,
    Reciprocity.arithmeticGlobalArtinMonoidHom_finitePlaceIdele]

/-- Arithmetic and geometric prime Artin elements are inverse
automorphisms. -/
@[simp]
theorem arithmeticFinitePlacePrimeArtin_eq_inv
    (v : HeightOneSpectrum (𝓞 K)) :
    arithmeticFinitePlacePrimeArtin (K := K) (L := L) v =
      (finitePlacePrimeArtin (K := K) (L := L) v)⁻¹ := by
  rw [arithmeticFinitePlacePrimeArtin,
    Reciprocity.arithmeticGlobalArtinMonoidHom_apply,
    finitePlacePrimeArtin]

/-- The arithmetic Frobenius of the actual chosen completed extension,
transported through its decomposition group into the global Galois group.
The unramifiedness hypothesis concerns this chosen extension, not an
unrelated abstract local field. -/
noncomputable def chosenFinitePlaceArithmeticFrobenius
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    L ≃ₐ[K] L := by
  let w := chosenFinitePlaceExtension (L := L) v
  exact Reciprocity.finitePlaceLocalToGlobalMonoidHom
    (K := K) (L := L) v w
    (Reciprocity.chosenFinitePlaceLocalArithmeticFrobenius
      (K := K) (L := L) v hunram)

/-- At an unramified chosen finite place, the arithmetic prime Artin
element really is the global decomposition-group transport of local
arithmetic Frobenius. The local input has valuation `-1` in the
construction's convention, and arithmetic global reciprocity inverts
that geometric local Artin value. -/
theorem arithmeticFinitePlacePrimeArtin_eq_chosenFinitePlaceArithmeticFrobenius
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    arithmeticFinitePlacePrimeArtin (K := K) (L := L) v =
      chosenFinitePlaceArithmeticFrobenius
        (K := K) (L := L) v hunram := by
  let w := chosenFinitePlaceExtension (L := L) v
  let x : (v.adicCompletion K)ˣ :=
    FiniteIdeleGroup.chosenLocalOrderSection v 1
  have hgeometric :
      Reciprocity.chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v x =
        (chosenFinitePlaceArithmeticFrobenius
          (K := K) (L := L) v hunram)⁻¹ := by
    change Reciprocity.finitePlaceArtinMonoidHomOfExtension
        (K := K) (L := L) v w x = _
    rw [Reciprocity.finitePlaceArtinMonoidHomOfExtension_factor]
    change Reciprocity.finitePlaceLocalToGlobalMonoidHom
        (K := K) (L := L) v w
        (Reciprocity.finitePlaceLocalArtinMonoidHom
          (K := K) (L := L) v w x) = _
    rw [Reciprocity.chosenFinitePlaceLocalArtin_eq_arithmeticFrobenius_inv_of_unramified
      (K := K) (L := L) v hunram, map_inv]
    rfl
  rw [arithmeticFinitePlacePrimeArtin_eq_arithmeticChosenFinitePlaceArtin,
    Reciprocity.arithmeticChosenFinitePlaceArtinMonoidHom_apply]
  rw [hgeometric, inv_inv]

/-- At an unramified chosen place, the arithmetic prime Artin element
has order equal to the local extension degree. -/
theorem
    orderOf_arithmeticFinitePlacePrimeArtin_eq_finitePlaceLocalDegree_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    orderOf
        (arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v) =
      _root_.finitePlaceLocalDegree
        (K := K) (L := L) v := by
  rw [arithmeticFinitePlacePrimeArtin_eq_inv,
    orderOf_inv]
  exact
    orderOf_finitePlacePrimeArtin_eq_finitePlaceLocalDegree_of_chosenUnramified
      (K := K) (L := L) v hunram

/-- An unramified finite place splits completely exactly when its
arithmetic Frobenius is trivial. -/
theorem
    arithmeticFinitePlacePrimeArtin_eq_one_iff_splitsCompletely_of_chosenUnramified
    (v : HeightOneSpectrum (𝓞 K))
    (hunram :
      _root_.ChosenFinitePlaceIsUnramified
        (K := K) (L := L) v) :
    arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v =
        1 ↔
      _root_.FinitePlaceSplitsCompletely
        (K := K) (L := L) v := by
  rw [arithmeticFinitePlacePrimeArtin_eq_inv, inv_eq_one]
  exact
    finitePlacePrimeArtin_eq_one_iff_splitsCompletely_of_chosenUnramified
      (K := K) (L := L) v hunram

end GlobalClassFields
end GlobalClassFieldTheory
