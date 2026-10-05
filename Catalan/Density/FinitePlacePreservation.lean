module

public import Catalan.Density.Definitions
public import ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal

/-!
# `Catalan.Density.FinitePlacePreservation`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.A3

lemma preservesPrime_of_mem_finitePlaceDecompositionGroup
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (τ : L ≃ₐ[K] L)
    (hτ : τ ∈ finitePlaceDecompositionGroup (K := K) (L := L) v) :
    PreservesPrime τ
      (finitePlaceExtensionCentre (K := K) (L := L) v
        (chosenFinitePlaceExtension (L := L) v)).asIdeal := by
  let instPlaceAction := finitePlaceMulAction K L
  let W := finitePlaceExtensionCentre (K := K) (L := L) v
    (chosenFinitePlaceExtension (L := L) v)
  change τ ∈ HilbertRamification.absoluteValueDecompositionGroup K
    (chosenFinitePlaceExtension (L := L) v).1 at hτ
  rw [absoluteValueDecompositionGroup_eq_finitePlaceStabilizer v
    (chosenFinitePlaceExtension (L := L) v)] at hτ
  have hfix : finitePlaceEquiv K L τ W = W := MulAction.mem_stabilizer_iff.mp hτ
  have hmap : W.asIdeal.map (RingOfIntegers.mapAlgEquiv τ).toRingEquiv = W.asIdeal := by
    rw [← finitePlaceEquiv_asIdeal, hfix]
  intro x
  change (RingOfIntegers.mapAlgEquiv τ) x ∈ W.asIdeal ↔ x ∈ W.asIdeal
  calc
    (RingOfIntegers.mapAlgEquiv τ) x ∈ W.asIdeal ↔
        (RingOfIntegers.mapAlgEquiv τ) x ∈
          W.asIdeal.map (RingOfIntegers.mapAlgEquiv τ).toRingEquiv := by rw [hmap]
    _ ↔ x ∈ W.asIdeal := Ideal.apply_mem_of_equiv_iff

end Catalan.A3
