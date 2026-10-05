module

public import Catalan.Density.AbsoluteT
public import ClassFieldTheory.GlobalClassFieldTheory.Cohomology.CyclicPrimePowerFullDecomposition
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge

/-!
# `Catalan.Density.FixedFieldPlaces`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.A3

lemma fixedField_fullDecomposition_infinite
    (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    (q : ℕ) (hq : q.Prime) (σ : L ≃ₐ[ℚ] L) (hne : σ ≠ 1) (hpow : σ ^ q = 1) :
    let K := IntermediateField.fixedField (Subgroup.zpowers σ)
    letI : IsGalois K L := IsGalois.of_fixed_field L (Subgroup.zpowers σ)
    Set.Infinite {v : HeightOneSpectrum (𝓞 K) |
      finitePlaceDecompositionGroup (K := K) (L := L) v = ⊤} := by
  let K := IntermediateField.fixedField (Subgroup.zpowers σ)
  let instGaloisK : IsGalois K L := IsGalois.of_fixed_field L (Subgroup.zpowers σ)
  let E := IntermediateField.subgroupEquivAlgEquiv (Subgroup.zpowers σ)
  have instCyclic : IsCyclic (L ≃ₐ[K] L) := E.isCyclic.mp inferInstance
  have horder : orderOf σ = q :=
    (hq.eq_one_or_self_of_dvd (orderOf σ) (orderOf_dvd_of_pow_eq_one hpow)).resolve_left
      (fun h => hne (orderOf_eq_one_iff.mp h))
  have hcard : Nat.card (L ≃ₐ[K] L) = q ^ 1 := by
    rw [← Nat.card_congr E.toEquiv, Nat.card_zpowers, horder, pow_one]
  exact GlobalClassFieldTheory.Cohomology.cyclic_prime_power_infinite_fullDecompositionPlaces
    (K := K) (L := L) hq (by decide : 0 < (1 : ℕ)) hcard

end Catalan.A3
