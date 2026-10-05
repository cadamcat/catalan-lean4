module

public import Mathlib

/-!
# `Catalan.Thaine.LocalMultiplicity`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

noncomputable instance heightOneLocalizationDvr
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (P : HeightOneSpectrum R) : IsDiscreteValuationRing (Localization.AtPrime P.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R P.ne_bot
    (Localization.AtPrime P.asIdeal)

lemma local_addVal_eq_emultiplicity
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (P : HeightOneSpectrum R) (a : R) :
    IsDiscreteValuationRing.addVal (Localization.AtPrime P.asIdeal)
        (algebraMap R (Localization.AtPrime P.asIdeal) a) =
      emultiplicity P.asIdeal (Ideal.span {a}) := by
  let S := Localization.AtPrime P.asIdeal
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible S
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  calc
    (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal S (algebraMap R S a) ↔
        pi ^ n ∣ algebraMap R S a := by
      rw [← hpi.addVal_pow n, IsDiscreteValuationRing.addVal_le_iff_dvd]
    _ ↔ algebraMap R S a ∈ IsLocalRing.maximalIdeal S ^ n := by
      rw [hpi.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    _ ↔ a ∈ P.asIdeal ^ n := by
      change a ∈ (IsLocalRing.maximalIdeal S ^ n).under R ↔ a ∈ P.asIdeal ^ n
      rw [IsLocalization.AtPrime.under_maximalIdeal_pow P.asIdeal S n]
    _ ↔ P.asIdeal ^ n ∣ Ideal.span {a} := by
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    _ ↔ (n : ℕ∞) ≤ emultiplicity P.asIdeal (Ideal.span {a}) :=
      pow_dvd_iff_le_emultiplicity

end Catalan.Thaine
