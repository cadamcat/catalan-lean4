import Catalan.Density.FinitePlacePreservation
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin
import ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedTower
import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
import ClassFieldTheory.AlgebraicNumberTheory.Galois.CyclicPrimeSubextension

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.A3
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

lemma chosenFinitePlace_unramified_of_finitePlaces
    (hunram : IsUnramifiedAtFinitePlaces K L) (v : HeightOneSpectrum (𝓞 K)) :
    ChosenFinitePlaceIsUnramified (K := K) (L := L) v := by
  exact chosenFinitePlaceIsUnramified_of_isUnramifiedAt (K := K) (L := L) v
    (hunram (finitePlaceExtensionCentre (K := K) (L := L) v
      (chosenFinitePlaceExtension (L := L) v)))

lemma primeArtin_zpowers_of_unramified
    (hunram : IsUnramifiedAtFinitePlaces K L) (v : HeightOneSpectrum (𝓞 K)) :
    finitePlaceDecompositionGroup (K := K) (L := L) v =
      Subgroup.zpowers
        (GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) v) := by
  rw [GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin_eq_inv,
    Subgroup.zpowers_inv]
  exact GlobalClassFieldTheory.GlobalClassFields.finitePlaceDecompositionGroup_eq_zpowers_finitePlacePrimeArtin_of_chosenUnramified
    v (chosenFinitePlace_unramified_of_finitePlaces K L hunram v)

lemma preservesPrime_iff_mem_zpowers_primeArtin
    (hunram : IsUnramifiedAtFinitePlaces K L) (P : HeightOneSpectrum (𝓞 L))
    (sigma : L ≃ₐ[K] L) :
    PreservesPrime sigma P.asIdeal ↔
      sigma ∈ Subgroup.zpowers
        (GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := K) (L := L) (finitePlaceBelow (K := K) P)) := by
  let instPlaceAction := finitePlaceMulAction K L
  have hiff : PreservesPrime sigma P.asIdeal ↔ finitePlaceEquiv K L sigma P = P := by
    let eO : 𝓞 L ≃+* 𝓞 L := (RingOfIntegers.mapAlgEquiv sigma).toRingEquiv
    constructor
    · intro hpres
      apply HeightOneSpectrum.ext
      rw [finitePlaceEquiv_asIdeal]
      apply Ideal.ext
      intro y
      obtain ⟨x, rfl⟩ := eO.surjective y
      exact (Ideal.apply_mem_of_equiv_iff).trans (hpres x).symm
    · intro hfix
      have hmap : P.asIdeal.map eO = P.asIdeal := by
        change P.asIdeal.map (RingOfIntegers.mapAlgEquiv sigma).toRingEquiv = P.asIdeal
        rw [← finitePlaceEquiv_asIdeal, hfix]
      intro x
      change eO x ∈ P.asIdeal ↔ x ∈ P.asIdeal
      calc
        eO x ∈ P.asIdeal ↔ eO x ∈ P.asIdeal.map eO := by rw [hmap]
        _ ↔ x ∈ P.asIdeal := Ideal.apply_mem_of_equiv_iff
  let v := finitePlaceBelow (K := K) P
  let w := (finitePlaceExtensionEquivAbove (K := K) (L := L) v).symm ⟨P, rfl⟩
  have hw : finitePlaceExtensionCentre (K := K) (L := L) v w = P := by
    have h := congrArg Subtype.val
      ((finitePlaceExtensionEquivAbove (K := K) (L := L) v).apply_symm_apply ⟨P, rfl⟩)
    exact h
  have hgroups : finitePlaceDecompositionGroup (K := K) (L := L) v =
      MulAction.stabilizer (L ≃ₐ[K] L) P := by
    change HilbertRamification.absoluteValueDecompositionGroup K
      (chosenFinitePlaceExtension (L := L) v).1 = _
    rw [absoluteValueDecompositionGroup_eq_of_exactExtensions_of_isMulCommutative
      (HeightOneSpectrum.adicAbv K v) (RayClass.adicAbv_isNontrivial v)
      (chosenFinitePlaceExtension (L := L) v) w]
    rw [absoluteValueDecompositionGroup_eq_finitePlaceStabilizer v w, hw]
  rw [← primeArtin_zpowers_of_unramified K L hunram v, hgroups, MulAction.mem_stabilizer_iff]
  exact hiff

end Catalan.A3
