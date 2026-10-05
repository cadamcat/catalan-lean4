module

public import Catalan.Density.PrimeFrobenius
public import Catalan.Density.PrimeArtinFormula
public import Catalan.Density.FixedResidue
public import Catalan.Density.FrobeniusRestrict
public import Catalan.Density.GaloisModules
public import Catalan.Density.FiniteT
public import Catalan.Density.ClassGroupArtin

/-!
# `Catalan.Density.HPrimeFrobenius`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
namespace Catalan.A3
attribute [local instance] integerAutSMulCommClass

lemma classGroupToHGal_prime_zpowers_of_rationalFrob
    (p q : ℕ) [Fact q.Prime] (hq : Odd q)
    (sigmaB : T p q ≃ₐ[Bsub p q] T p q)
    (ell : ℕ) (hell : ell.Prime) (P : Ideal (𝓞 (T p q)))
    (hfrob : IsArithmeticFrob ell P (sigmaB.restrictScalars ℚ))
    (v : HeightOneSpectrum (𝓞 (F p))) (hv : v.asIdeal = P.under (𝓞 (F p))) :
    Subgroup.zpowers
      (classGroupToHGal p q hq (ClassGroup.mk (F p) (FractionalIdealGroup.prime v))) =
        Subgroup.zpowers (restrictTToH p q sigmaB) := by
  have instNumberFieldH : NumberField (Hsub p q) := numberField_Hsub p q hq
  have instNumberFieldT : NumberField (T p q) := numberField_T p q hq
  have instFiniteH : FiniteDimensional (F p) (Hsub p q) := finiteDimensional_Hsub p q hq
  have instGaloisH : IsGalois (F p) (Hsub p q) := isGalois_Hsub p q
  have instAbelianH : IsAbelianGalois (F p) (Hsub p q) :=
    { is_comm.comm := Hsub_gal_mul_comm p q }
  have instMaxP : P.IsMaximal := hfrob.1
  have hPbot : P ≠ ⊥ := hfrob.2.1
  let Q : HeightOneSpectrum (𝓞 (Hsub p q)) :=
    ⟨P.under (𝓞 (Hsub p q)), inferInstance,
      Ideal.under_ne_bot (𝓞 (Hsub p q)) hPbot⟩
  have hbelow : finitePlaceBelow (K := F p) Q = v := by
    apply HeightOneSpectrum.ext
    rw [finitePlaceBelow_asIdeal]
    change (P.under (𝓞 (Hsub p q))).under (𝓞 (F p)) = v.asIdeal
    rw [Ideal.under_under, hv]
  have hcard : Nat.card (𝓞 (F p) ⧸ Q.asIdeal.under (𝓞 (F p))) = ell := by
    change Nat.card (𝓞 (F p) ⧸ (P.under (𝓞 (Hsub p q))).under (𝓞 (F p))) = ell
    rw [Ideal.under_under]
    apply card_quotient_under_of_arithmeticFrob_fixes (F p) (T p q) ell hell P
      (sigmaB.restrictScalars ℚ) hfrob
    intro x
    exact (sigmaB.restrictScalars (F p)).commutes x
  have hfrobH : IsArithFrobAt (𝓞 (F p)) (restrictTToH p q sigmaB) Q.asIdeal := by
    apply relativeFrob_congruence_of_rationalFrob_compatible (F p) (Hsub p q) (T p q)
      ell P (sigmaB.restrictScalars ℚ) (restrictTToH p q sigmaB) hfrob _ hcard
    intro x
    exact (restrictTToH_commutes p q sigmaB x).symm
  have hw := unramifiedAbelianQ_Hsub p q hq
  have hunram : IsUnramifiedAtFinitePlaces (F p) (Hsub p q) :=
    unramifiedAbelianQ_finitePlaces p q (Hsub p q) hw
  have hclass :
      classGroupToHGal p q hq (ClassGroup.mk (F p) (FractionalIdealGroup.prime v)) =
        GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
          (K := F p) (L := Hsub p q) v := by
    exact classGroupArtinOfEverywhereUnramified_prime (F p) (Hsub p q)
      ⟨hunram, unramifiedAbelianQ_infinitePlaces p q hq (Hsub p q) hw⟩ v
  rw [hclass, ← hbelow]
  exact (zpowers_nativeFrob_eq_zpowers_primeArtin (F p) (Hsub p q) hunram Q
    (restrictTToH p q sigmaB) hfrobH).symm

lemma exists_H_prime_class_of_rationalFrob
    (p q : ℕ) [Fact q.Prime] (hq : Odd q)
    (sigmaB : T p q ≃ₐ[Bsub p q] T p q)
    (ell : ℕ) (hell : ell.Prime) (P : Ideal (𝓞 (T p q)))
    (hfrob : IsArithmeticFrob ell P (sigmaB.restrictScalars ℚ)) :
    ∃ v : HeightOneSpectrum (𝓞 (F p)),
      v.asIdeal = P.under (𝓞 (F p)) ∧ Nat.card (𝓞 (F p) ⧸ v.asIdeal) = ell ∧
      Subgroup.zpowers
        (classGroupToHGal p q hq (ClassGroup.mk (F p) (FractionalIdealGroup.prime v))) =
          Subgroup.zpowers (restrictTToH p q sigmaB) := by
  have instNumberFieldT : NumberField (T p q) := numberField_T p q hq
  have instMaxP : P.IsMaximal := hfrob.1
  let v : HeightOneSpectrum (𝓞 (F p)) :=
    ⟨P.under (𝓞 (F p)), inferInstance, Ideal.under_ne_bot (𝓞 (F p)) hfrob.2.1⟩
  refine ⟨v, rfl, ?_, classGroupToHGal_prime_zpowers_of_rationalFrob
    p q hq sigmaB ell hell P hfrob v rfl⟩
  apply card_quotient_under_of_arithmeticFrob_fixes (F p) (T p q) ell hell P
    (sigmaB.restrictScalars ℚ) hfrob
  intro x
  exact (sigmaB.restrictScalars (F p)).commutes x

end Catalan.A3
