module

public import Catalan.Thaine.LocalAction
public import Catalan.Thaine.LocalMultiplicity
public import Catalan.Thaine.DvrDecomposition
public import Catalan.Thaine.LocalExponent

/-!
# `Catalan.Thaine.DedekindLocalExponent`

Part of the Catalan formalization.
-/

@[expose] public section

set_option autoImplicit false
open IsDedekindDomain
noncomputable section
namespace Catalan.Thaine

lemma residue_coboundary_eq_pow_multiplicity
    (R k : Type*) [CommRing R] [IsDedekindDomain R] [Field k]
    (P : HeightOneSpectrum R)
    (tau : R ≃+* R) (hpres : ∀ x : R, tau x ∈ P.asIdeal ↔ x ∈ P.asIdeal)
    (red : R →+* k) (hker : RingHom.ker red = P.asIdeal)
    (hinertia : ∀ x : R, red (tau x) = red x)
    (pi t alpha : R) (eta : Rˣ)
    (hpi : emultiplicity P.asIdeal (Ideal.span {pi}) = 1)
    (ht : t ∉ P.asIdeal) (hpi_action : tau pi = pi * t)
    (halpha : alpha ≠ 0) (heta : tau alpha = (eta : R) * alpha) :
    red (eta : R) = (red t) ^ multiplicity P.asIdeal (Ideal.span {alpha}) := by
  let S := Localization.AtPrime P.asIdeal
  obtain ⟨tauLoc, redLoc, htau, hred, hinertiaLoc⟩ :=
    exists_localized_action_and_residue R k P.asIdeal tau hpres red hker hinertia
  have hpiLoc : IsDiscreteValuationRing.addVal S (algebraMap R S pi) = 1 := by
    rw [local_addVal_eq_emultiplicity, hpi]
  have halphaLoc : algebraMap R S alpha ≠ 0 := by
    intro h
    apply halpha
    apply IsLocalization.injective S P.asIdeal.primeCompl_le_nonZeroDivisors
    simpa only [map_zero] using h
  obtain ⟨n, u, hdecomp, hn⟩ := exists_unit_decomposition_of_addVal_one S
    (algebraMap R S pi) (algebraMap R S alpha) hpiLoc halphaLoc
  let tLoc : Sˣ := (IsLocalization.map_units S (⟨t, ht⟩ : P.asIdeal.primeCompl)).unit
  have htLoc : (tLoc : S) = algebraMap R S t :=
    (IsLocalization.map_units S (⟨t, ht⟩ : P.asIdeal.primeCompl)).unit_spec
  let etaLoc : Sˣ := Units.map (algebraMap R S).toMonoidHom eta
  have hetaLoc : (etaLoc : S) = algebraMap R S (eta : R) := rfl
  have hpiLoc_action : tauLoc (algebraMap R S pi) = (tLoc : S) * algebraMap R S pi := by
    rw [htau, hpi_action, map_mul, htLoc, mul_comm]
  let localFractionAlgebra : Algebra S (FractionRing S) :=
    OreLocalization.instAlgebra (R₀ := S) (R := S) (S := nonZeroDivisors S)
  let sigma : FractionRing S ≃+* FractionRing S :=
    IsFractionRing.ringEquivOfRingEquiv (A := S) (B := S) tauLoc
  have hcompat (x : S) : sigma (algebraMap S (FractionRing S) x) =
      algebraMap S (FractionRing S) (tauLoc x) :=
    IsFractionRing.ringEquivOfRingEquiv_algebraMap (A := S) (B := S) tauLoc x
  have heq := residue_coboundary_of_uniformizer_decomposition S (FractionRing S) k
    tauLoc sigma hcompat redLoc hinertiaLoc (algebraMap R S pi)
    (irreducible_of_addVal_one S _ hpiLoc).ne_zero tLoc u etaLoc hpiLoc_action
    (algebraMap S (FractionRing S) (algebraMap R S alpha)) (n : ℤ)
    (by simpa only [map_mul, map_pow, zpow_natCast] using
      congrArg (algebraMap S (FractionRing S)) hdecomp)
    (by rw [hcompat, htau, heta, map_mul, map_mul, hetaLoc])
  have hemult : emultiplicity P.asIdeal (Ideal.span {alpha}) = (n : ℕ∞) := by
    rw [← local_addVal_eq_emultiplicity R P alpha]
    exact hn
  have hmult : multiplicity P.asIdeal (Ideal.span {alpha}) = n :=
    multiplicity_eq_of_emultiplicity_eq_some hemult
  have hredEta : redLoc (etaLoc : S) = red (eta : R) := by
    rw [hetaLoc]
    exact hred (eta : R)
  have hredT : redLoc (tLoc : S) = red t := by
    rw [htLoc]
    exact hred t
  simpa only [hredEta, hredT, zpow_natCast, hmult] using heq

end Catalan.Thaine
