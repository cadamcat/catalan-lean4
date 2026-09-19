import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.UnramifiedPrimeArtin
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization

set_option autoImplicit false

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
