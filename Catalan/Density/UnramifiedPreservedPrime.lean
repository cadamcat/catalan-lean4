module

public import Catalan.Density.FixedFieldPlaces
public import Catalan.Density.FinitePlacePreservation
public import Catalan.Density.RationalPlaces
public import Catalan.Density.InertiaBridge

/-!
# `Catalan.Density.UnramifiedPreservedPrime`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.A3

lemma exists_unramified_preserved_prime
    (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    (q : ℕ) (hq : q.Prime) (σ : L ≃ₐ[ℚ] L) (hne : σ ≠ 1) (hpow : σ ^ q = 1)
    (S : Finset ℕ) :
    ∃ ell : ℕ, ell.Prime ∧ ell ∉ S ∧
      ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ P ≠ ⊥ ∧ (ell : 𝓞 L) ∈ P ∧
        InertiaTrivial ℚ L P ∧ PreservesPrime σ P := by
  classical
  let H := Subgroup.zpowers σ
  let K := IntermediateField.fixedField H
  have instGaloisK : IsGalois K L := IsGalois.of_fixed_field L H
  have hinf : Set.Infinite {v : HeightOneSpectrum (𝓞 K) |
      finitePlaceDecompositionGroup (K := K) (L := L) v = ⊤} :=
    fixedField_fullDecomposition_infinite L q hq σ hne hpow
  have hbadNat := finite_places_above_natSet K S
  have hbadRam : {v : HeightOneSpectrum (𝓞 K) |
      finitePlaceBelow (K := ℚ) v ∈ ramifiedBaseFinitePlaces (K := ℚ) (L := L)}.Finite := by
    simpa only [Finset.mem_coe] using
      Set.Finite.preimage_finitePlaceBelow (K := ℚ) (L := K)
        (ramifiedBaseFinitePlaces (K := ℚ) (L := L)).finite_toSet
  obtain ⟨v, hvfull, hvbad⟩ := hinf.exists_notMem_finite (hbadNat.union hbadRam)
  have hvNat : Rat.HeightOneSpectrum.natGenerator (finitePlaceBelow (K := ℚ) v) ∉ S :=
    fun h => hvbad (Or.inl h)
  have hvRam : finitePlaceBelow (K := ℚ) v ∉ ramifiedBaseFinitePlaces (K := ℚ) (L := L) :=
    fun h => hvbad (Or.inr h)
  let W := finitePlaceExtensionCentre (K := K) (L := L) v
    (chosenFinitePlaceExtension (L := L) v)
  have hWv : finitePlaceBelow (K := K) W = v :=
    finitePlaceBelow_finitePlaceExtensionCentre v (chosenFinitePlaceExtension (L := L) v)
  have hWQ : finitePlaceBelow (K := ℚ) W = finitePlaceBelow (K := ℚ) v := by
    rw [← finitePlaceBelow_finitePlaceBelow (K := ℚ) (M := K) (L := L) W, hWv]
  have hunram : Algebra.IsUnramifiedAt (𝓞 ℚ) W.asIdeal := by
    by_contra hram
    apply hvRam
    apply (mem_ramifiedBaseFinitePlaces_iff (K := ℚ) (L := L) _).mpr
    exact ⟨W, ⟨(congrArg HeightOneSpectrum.asIdeal hWQ).symm⟩, hram⟩
  let τ : L ≃ₐ[K] L := IntermediateField.subgroupEquivAlgEquiv H ⟨σ, Subgroup.mem_zpowers σ⟩
  have hτ : τ.restrictScalars ℚ = σ := by
    ext x
    rfl
  have hτmem : τ ∈ finitePlaceDecompositionGroup (K := K) (L := L) v := by
    rw [hvfull]
    exact Subgroup.mem_top τ
  have hpres : PreservesPrime σ W.asIdeal := by
    have ht := preservesPrime_of_mem_finitePlaceDecompositionGroup K L v τ hτmem
    change PreservesPrime (τ.restrictScalars ℚ) W.asIdeal at ht
    rwa [hτ] at ht
  refine ⟨Rat.HeightOneSpectrum.natGenerator (finitePlaceBelow (K := ℚ) W),
    Rat.HeightOneSpectrum.prime_natGenerator _, ?_, W.asIdeal, inferInstance, W.ne_bot,
    rational_natGenerator_below_mem L W, ?_, hpres⟩
  · rwa [hWQ]
  · exact (inertiaTrivial_iff_isUnramifiedAt ℚ L W.asIdeal W.ne_bot).mpr hunram

end Catalan.A3
